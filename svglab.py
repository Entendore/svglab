"""
svglab.py v14 — script-driven SVG animation -> video.

    python svglab.py                                    # built-in demo
    python svglab.py myscene.py -qh                     # render a scene
    python svglab.py myscene.py chapters.srt            # chapters only
    python svglab.py myscene.py -qm --srt chapters.srt  # render + chapters
    python svglab.py movie.py -qm                       # clip project
    python svglab.py movie.py order.json -qm            # order + transitions
    python svglab.py --gui [scene.py|proj.zip]
    python svglab.py --new-movie [movie.py]
    python svglab.py --gallery
    python svglab.py --pack scene.py proj.zip / --unpack proj.zip
    python svglab.py --clean
"""
import os, sys, re, math, copy, ast, json, zipfile, hashlib, inspect, linecache
import subprocess, shutil, tempfile

from lxml import etree
from PySide6.QtCore import (QRectF, QByteArray, Qt, QPointF, Signal, QThread,
                            QTimer, QSize)
from PySide6.QtGui import (QGuiApplication, QImage, QPainter, QColor,
                           QPainterPath, QFont, QFontMetricsF, QRegion,
                           QIcon, QPixmap, QPolygonF, QPen, QBrush,
                           QShortcut, QKeySequence)
from PySide6.QtWidgets import (QApplication, QMainWindow, QWidget, QLabel,
                               QPushButton, QSlider, QComboBox, QVBoxLayout,
                               QHBoxLayout, QFileDialog, QDialog, QListWidget,
                               QListWidgetItem, QFormLayout, QDoubleSpinBox,
                               QTableWidget, QTableWidgetItem, QMessageBox,
                               QToolButton, QMenu, QLineEdit, QScrollArea,
                               QGridLayout, QHeaderView)
from PySide6.QtSvg import QSvgRenderer

SVG_NS = "http://www.w3.org/2000/svg"
NSMAP = {None: SVG_NS}
CACHE_DIR = "svglab_cache"

# ---------------------------------------------------------------- easings
def linear(t): return t
def smooth(t): return t * t * (3 - 2 * t)
def ease_in(t): return t * t
def ease_out(t): return 1 - (1 - t) ** 2
def ping_pong(t): return smooth(2 * t if t < 0.5 else 2 * (1 - t))
def overshoot(t):
    c1 = 1.70158
    return 1 + (c1 + 1) * (t - 1) ** 3 + c1 * (t - 1) ** 2
def bounce_out(t):
    n1, d1 = 7.5625, 2.75
    if t < 1 / d1: return n1 * t * t
    if t < 2 / d1: return n1 * (t - 1.5 / d1) ** 2 + .75
    if t < 2.5 / d1: return n1 * (t - 2.25 / d1) ** 2 + .9375
    return n1 * (t - 2.625 / d1) ** 2 + .984375
def elastic_out(t):
    if t in (0.0, 1.0): return t
    return 2 ** (-10 * t) * math.sin((t * 10 - .75) * (2 * math.pi / 3)) + 1
def cubic_bezier(x1, y1, x2, y2):
    def b(t, p1, p2): return 3*(1-t)**2*t*p1 + 3*(1-t)*t*t*p2 + t**3
    def val(t, p1, p2, x):
        lo, hi = 0.0, 1.0
        for _ in range(30):
            mid = (lo + hi) / 2
            if b(mid, x1, x2) < x: lo = mid
            else: hi = mid
        return b((lo + hi) / 2, y1, y2)
    return lambda t: 1.0 if t >= 1 else (0.0 if t <= 0 else val(t, y1, y2, t))
def clamp01(x): return max(0.0, min(1.0, x))

EASING_PRESETS = {"ease (in-out)": (0.42, 0.0, 0.58, 1.0),
                  "linear": (0.0, 0.0, 1.0, 1.0),
                  "ease-in": (0.42, 0.0, 1.0, 1.0),
                  "ease-out": (0.0, 0.0, 0.58, 1.0),
                  "overshoot": (0.34, 1.56, 0.64, 1.0),
                  "anticipate": (0.68, -0.40, 0.32, 1.40)}

# ---------------------------------------------------------------- object base
class _Obj:
    _KEYS = ("x", "y", "scale", "rotation", "opacity")
    def __init__(self): self.updaters = []
    def state(self): return {k: getattr(self, k) for k in self._KEYS}
    def set_state(self, st): [setattr(self, k, v) for k, v in st.items()]
    def copy(self):
        dup = self.__class__.__new__(self.__class__)
        dup.__dict__.update(self.__dict__)
        dup.set_state(self.state())
        return dup
    def shift(self, dx, dy): self.x += dx; self.y += dy
    def move_to(self, x, y): self.x, self.y = x, y
    def scale_by(self, f): self.scale *= f
    def rotate(self, deg, around=None):
        if around is None:
            self.rotation += deg; return
        r = math.radians(deg); c, s = math.cos(r), math.sin(r)
        dx, dy = self.x - around[0], self.y - around[1]
        self.x = around[0] + dx * c - dy * s
        self.y = around[1] + dx * s + dy * c
        self.rotation += deg
    def set_opacity(self, o): self.opacity = o
    def add_updater(self, fn): self.updaters.append(fn)
    def remove_updater(self, fn): self.updaters.remove(fn)
    @property
    def animate(self): return _Anims(self)

# ---------------------------------------------------------------- path parsing
_TOK = re.compile(r"[MmLlHhVvCcSsQqTtAaZz]|[+-]?(?:\d*\.\d+|\d+\.?)(?:[eE][+-]?\d+)?")

def _arc_to_cubics(p, x1, y1, rx, ry, phi, laf, sf, x2, y2):
    rx, ry = abs(rx), abs(ry)
    if rx < 1e-9 or ry < 1e-9 or (abs(x1-x2) < 1e-9 and abs(y1-y2) < 1e-9):
        p.lineTo(x2, y2); return
    phi = math.radians(phi); cp, sp = math.cos(phi), math.sin(phi)
    dx2, dy2 = (x1 - x2) / 2, (y1 - y2) / 2
    x1p = cp*dx2 + sp*dy2; y1p = -sp*dx2 + cp*dy2
    lam = x1p*x1p/(rx*rx) + y1p*y1p/(ry*ry)
    if lam > 1:
        s = math.sqrt(lam); rx *= s; ry *= s
    num = rx*rx*ry*ry - rx*rx*y1p*y1p - ry*ry*x1p*x1p
    den = rx*rx*y1p*y1p + ry*ry*x1p*x1p
    co = math.sqrt(max(num/den, 0.0)) * (-1 if laf == sf else 1)
    cxp, cyp = co*rx*y1p/ry, -co*ry*x1p/rx
    cx = cp*cxp - sp*cyp + (x1+x2)/2; cy = sp*cxp + cp*cyp + (y1+y2)/2
    def ang(ux, uy, vx, vy):
        d = math.hypot(ux, uy) * math.hypot(vx, vy)
        a = math.acos(max(-1.0, min(1.0, (ux*vx+uy*vy)/d)))
        return -a if ux*vy - uy*vx < 0 else a
    th1 = ang(1, 0, (x1p-cxp)/rx, (y1p-cyp)/ry)
    dth = ang((x1p-cxp)/rx, (y1p-cyp)/ry, (-x1p-cxp)/rx, (-y1p-cyp)/ry)
    if not sf and dth > 0: dth -= 2*math.pi
    if sf and dth < 0: dth += 2*math.pi
    n = max(1, int(abs(dth)/(math.pi/2)) + 1); dt = dth/n
    def pt(a):
        return (cx + rx*math.cos(a)*cp - ry*math.sin(a)*sp,
                cy + rx*math.cos(a)*sp + ry*math.sin(a)*cp)
    def deriv(a):
        return (-rx*math.sin(a)*cp - ry*math.cos(a)*sp,
                -rx*math.sin(a)*sp + ry*math.cos(a)*cp)
    k = 4/3 * math.tan(dt/4); a = th1
    for _ in range(n):
        p0, p1 = pt(a), pt(a+dt); d0, d1 = deriv(a), deriv(a+dt)
        p.cubicTo(p0[0]+k*d0[0], p0[1]+k*d0[1], p1[0]-k*d1[0], p1[1]-k*d1[1], p1[0], p1[1])
        a += dt

def svg_path_to_qpath(d):
    p = QPainterPath()
    toks, i = _TOK.findall(d), 0
    cmd, x, y, sx, sy, px, py = None, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0
    def nums(n):
        nonlocal i
        v = [float(t) for t in toks[i:i+n]]; i += n; return v
    while i < len(toks):
        if toks[i].isalpha(): cmd = toks[i]; i += 1
        rel = cmd.islower(); c = cmd.upper()
        if c == "M":
            dx, dy = nums(2); x, y = (x+dx, y+dy) if rel else (dx, dy)
            p.moveTo(x, y); sx, sy = x, y; cmd = "l" if rel else "L"
        elif c == "L":
            dx, dy = nums(2); x, y = (x+dx, y+dy) if rel else (dx, dy); p.lineTo(x, y)
        elif c == "H":
            (dx,) = nums(1); x = x+dx if rel else dx; p.lineTo(x, y)
        elif c == "V":
            (dy,) = nums(1); y = y+dy if rel else dy; p.lineTo(x, y)
        elif c == "C":
            c1x, c1y, c2x, c2y, dx, dy = nums(6)
            if rel: c1x += x; c1y += y; c2x += x; c2y += y; dx += x; dy += y
            p.cubicTo(c1x, c1y, c2x, c2y, dx, dy); x, y, px, py = dx, dy, c2x, c2y
        elif c == "S":
            c2x, c2y, dx, dy = nums(4)
            if rel: c2x += x; c2y += y; dx += x; dy += y
            p.cubicTo(2*x-px, 2*y-py, c2x, c2y, dx, dy); x, y, px, py = dx, dy, c2x, c2y
        elif c == "Q":
            cx_, cy_, dx, dy = nums(4)
            if rel: cx_ += x; cy_ += y; dx += x; dy += y
            p.quadTo(cx_, cy_, dx, dy); x, y, px, py = dx, dy, cx_, cy_
        elif c == "T":
            dx, dy = nums(2)
            if rel: dx += x; dy += y
            cx_, cy_ = 2*x-px, 2*y-py
            p.quadTo(cx_, cy_, dx, dy); x, y, px, py = dx, dy, cx_, cy_
        elif c == "A":
            rx, ry, rot, laf, sf, dx, dy = nums(7)
            if rel: dx += x; dy += y
            _arc_to_cubics(p, x, y, rx, ry, rot, laf, sf, dx, dy); x, y = dx, dy
        elif c == "Z":
            p.closeSubpath(); x, y = sx, sy
        else:
            break
    return p

def qpath_to_svg_d(qp):
    n, out, i, open_ct = qp.elementCount(), [], 0, 0
    ET = QPainterPath.ElementType
    while i < n:
        el = qp.elementAt(i); t = el.type
        if t == ET.MoveToElement:
            if open_ct: out.append("Z")
            out.append(f"M{el.x():.2f},{el.y():.2f}"); open_ct = 1; i += 1
        elif t == ET.LineToElement:
            out.append(f"L{el.x():.2f},{el.y():.2f}"); open_ct += 1; i += 1
        elif t == ET.CurveToElement:
            c2, e = qp.elementAt(i+1), qp.elementAt(i+2)
            out.append(f"C{el.x():.2f},{el.y():.2f} "
                       f"{c2.x():.2f},{c2.y():.2f} {e.x():.2f},{e.y():.2f}")
            open_ct += 1; i += 3
        else:
            i += 1
    if open_ct: out.append("Z")
    return " ".join(out)

def _geom_for(elem):
    tag = etree.QName(elem).localname
    f = lambda k, d=0.0: float(elem.get(k, d) or d)
    p = QPainterPath()
    if tag == "path":
        return svg_path_to_qpath(elem.get("d", ""))
    if tag in ("line", "polyline", "polygon"):
        v = [float(t) for t in re.split(r"[\s,]+", (elem.get("points") or "").strip()) if t]
        if tag == "line": v = [f("x1"), f("y1"), f("x2"), f("y2")]
        if len(v) >= 4:
            p.moveTo(v[0], v[1])
            for j in range(2, len(v)-1, 2): p.lineTo(v[j], v[j+1])
            if tag == "polygon": p.closeSubpath()
            return p
    if tag == "circle":
        p.addEllipse(QRectF(f("cx")-f("r"), f("cy")-f("r"), 2*f("r"), 2*f("r"))); return p
    if tag == "ellipse":
        p.addEllipse(QRectF(f("cx")-f("rx"), f("cy")-f("ry"), 2*f("rx"), 2*f("ry"))); return p
    if tag == "rect":
        r = QRectF(f("x"), f("y"), f("width"), f("height"))
        if f("rx") > 0: p.addRoundedRect(r, f("rx"), f("ry"))
        else: p.addRect(r)
        return p
    return None

def _qlen(qp):
    L = 0.0
    for poly in qp.toSubpathPolygons():
        for a, b in zip(poly, poly[1:]):
            L += math.hypot(b.x()-a.x(), b.y()-a.y())
    return L

def _arc_sampler(qp, N=512):
    pts = [(qp.pointAtPercent(i/N).x(), qp.pointAtPercent(i/N).y())
           for i in range(N + 1)]
    cum = [0.0]
    for i in range(1, len(pts)):
        cum.append(cum[-1] + math.hypot(pts[i][0]-pts[i-1][0], pts[i][1]-pts[i-1][1]))
    total = cum[-1] or 1.0
    def at(f):
        d = clamp01(f) * total
        lo, hi = 0, len(cum) - 1
        while lo < hi:
            mid = (lo + hi) // 2
            if cum[mid] < d: lo = mid + 1
            else: hi = mid
        i = max(1, lo)
        seg = cum[i] - cum[i-1]
        g = (d - cum[i-1]) / seg if seg else 0.0
        return (pts[i-1][0] + (pts[i][0]-pts[i-1][0]) * g,
                pts[i-1][1] + (pts[i][1]-pts[i-1][1]) * g,
                i / N)
    return at

# ---------------------------------------------------------------- doc splitting
_SHARED = {"defs", "style", "symbol", "marker", "clipPath", "mask",
           "filter", "linearGradient", "radialGradient", "pattern"}

def _part_doc(root, elem):
    """(doc, wrapped): standalone doc; the element is MOVED in (live edits
    reach the renderer), under a chain of ancestor transforms."""
    doc = etree.Element(f"{{{SVG_NS}}}svg", nsmap=root.nsmap)
    for k, v in root.items(): doc.set(k, v)
    doc[:] = [copy.deepcopy(ch) for ch in root
              if isinstance(ch.tag, str) and etree.QName(ch).localname in _SHARED]
    chain, cur = [], elem.getparent()
    while cur is not None and cur is not root:
        tr = cur.get("transform")
        if tr: chain.insert(0, tr)
        cur = cur.getparent()
    target, wrapped = doc, False
    if chain:
        target = etree.SubElement(doc, f"{{{SVG_NS}}}g")
        target.set("transform", " ".join(chain))
        wrapped = True
    target.append(elem)
    return doc, wrapped

def _scan_bbox(renderer, vb):
    scale = min(1.0, 600.0 / max(vb.width(), vb.height(), 1))
    W = max(1, round(vb.width() * scale)); H = max(1, round(vb.height() * scale))
    img = QImage(W, H, QImage.Format_RGBA8888); img.fill(0)
    p = QPainter(img); renderer.render(p); p.end()
    bits, bpl = img.constBits(), img.bytesPerLine()
    x0, y0, x1, y1 = 10**9, 10**9, -1, -1
    for ry in range(H):
        ax = bytes(bits[ry*bpl: ry*bpl + W*4])[3::4]
        if not any(ax): continue
        idx = [i for i, v in enumerate(ax) if v > 10]
        x0, x1 = min(x0, idx[0]), max(x1, idx[-1])
        y0, y1 = min(y0, ry), max(y1, ry)
    if x1 < 0: return None
    return QRectF(vb.x() + x0/scale, vb.y() + y0/scale,
                  (x1-x0+1)/scale, (y1-y0+1)/scale)

def _raster_surface(w_units, h_units, density):
    d = min(density, 4096.0 / max(w_units, h_units, 1e-6))
    W = max(1, round(w_units * d)); H = max(1, round(h_units * d))
    img = QImage(W, H, QImage.Format_RGBA8888)
    img.fill(QColor(0, 0, 0, 0))
    p = QPainter(img)
    p.setRenderHints(QPainter.Antialiasing | QPainter.SmoothPixmapTransform)
    return img, p, d

# ---------------------------------------------------------------- objects
class SvgPart(_Obj):
    def __init__(self, svg, elem, doc, wrapped):
        super().__init__()
        self.svg, self.elem, self._doc, self._wraps = svg, elem, doc, wrapped
        self._base = elem.get("style", "")
        self._live, self._geom, self._doc_dirty = {}, None, False
        self._snap_doc = None
        self._bytes = etree.tostring(doc)
        self._renderer = QSvgRenderer(QByteArray(self._bytes))
        vb = svg.vb
        self._bbox = _scan_bbox(self._renderer, vb) or QRectF(
            vb.center().x(), vb.center().y(), 0, 0)
        cx, cy = self._bbox.center().x(), self._bbox.center().y()
        self.x, self.y = (cx - vb.center().x()) * svg.k, (cy - vb.center().y()) * svg.k
        self.scale, self.rotation, self.opacity = svg.k, 0.0, 1.0

    def invalidate(self):
        self._doc_dirty = True
        self._bytes = etree.tostring(self._doc)
        self._renderer = QSvgRenderer(QByteArray(self._bytes))

    def geom(self):
        if self._geom is None: self._geom = _geom_for(self.elem)
        return self._geom

    def content_size(self):
        return self._bbox.width() * self.scale, self._bbox.height() * self.scale

    def style_set(self, **kv): self._live.update(kv); self._flush()
    def style_pop(self, *keys):
        for k in keys: self._live.pop(k, None)
        self._flush()
    def _flush(self):
        if self._live:
            extra = ";".join(f"{k}:{v}" for k, v in self._live.items())
            self.elem.set("style", (self._base + ";" if self._base else "") + extra)
        elif self._base: self.elem.set("style", self._base)
        else: self.elem.attrib.pop("style", None)
        self.invalidate()

    def rasterize(self, density):
        vb, bb = self.svg.vb, self._bbox
        img, p, d = _raster_surface(bb.width(), bb.height(), density)
        self._renderer.render(p, QRectF((vb.x()-bb.x())*d, (vb.y()-bb.y())*d,
                                        vb.width()*d, vb.height()*d))
        p.end()
        rect = QRectF(bb.x()-vb.x()-vb.width()/2, bb.y()-vb.y()-vb.height()/2,
                      bb.width(), bb.height())
        return img, rect, d

    def paint(self, p):
        if self.opacity <= 0: return
        p.save()
        p.setOpacity(p.opacity() * self.opacity)
        p.translate(self.x, self.y); p.rotate(self.rotation); p.scale(self.scale, self.scale)
        vb = self.svg.vb
        self._renderer.render(p, QRectF(-vb.width()/2, -vb.height()/2, vb.width(), vb.height()))
        p.restore()


class Svg(_Obj):
    def __init__(self, path, canvas=None):
        super().__init__()
        self.tree = etree.parse(path)
        self.root = self.tree.getroot()
        self.renderer = QSvgRenderer(path)
        vb = self.renderer.viewBoxF()
        self.vb = QRectF(vb)
        self.k = (canvas[0] / vb.width()) if canvas else 1.0
        self.x = self.y = 0.0
        self.scale, self.rotation, self.opacity = self.k, 0.0, 1.0
        self._parts, self._moved = {}, []
        self._snap_doc, self._doc_dirty = None, False

    def content_size(self):
        return self.vb.width() * self.scale, self.vb.height() * self.scale

    def select(self, sel):
        seen, out = set(), []
        pool = [el for el in self.root.iter()
                if isinstance(el.tag, str) and el is not self.root] + self._moved
        for el in pool:
            if id(el) in seen: continue
            seen.add(id(el))
            hit = (sel == "*"
                   or (sel.startswith("#") and el.get("id") == sel[1:])
                   or (sel.startswith(".") and sel[1:] in (el.get("class") or "").split())
                   or etree.QName(el).localname == sel)
            if hit: out.append(self._part_for(el))
        return Selection(out)

    def _part_for(self, el):
        key = id(el)
        if key in self._parts: return self._parts[key]
        if el.getparent() is not None:
            el.set("display", "none")
            self.renderer = QSvgRenderer(QByteArray(etree.tostring(self.root)))
            self._doc_dirty = True
        doc, wrapped = _part_doc(self.root, el)
        part = SvgPart(self, el, doc, wrapped)
        self._moved.append(el)
        self._parts[key] = part
        return part

    def all(self): return Selection(list(self._parts.values()))

    def rasterize(self, density):
        vb = self.vb
        img, p, d = _raster_surface(vb.width(), vb.height(), density)
        self.renderer.render(p, QRectF(0, 0, img.width(), img.height()))
        p.end()
        return img, QRectF(-vb.width()/2, -vb.height()/2, vb.width(), vb.height()), d

    def paint(self, p):
        if self.opacity <= 0: return
        p.save()
        p.setOpacity(p.opacity() * self.opacity)
        p.translate(self.x, self.y); p.rotate(self.rotation); p.scale(self.scale, self.scale)
        vb = self.vb
        self.renderer.render(p, QRectF(-vb.width()/2, -vb.height()/2, vb.width(), vb.height()))
        p.restore()


class GeneratedObj(_Obj):
    def __init__(self, svg_str):
        super().__init__()
        self.x = self.y = 0.0
        self.scale, self.rotation, self.opacity = 1.0, 0.0, 1.0
        self._snap_doc = None
        self._install(etree.fromstring(svg_str.encode()))

    def _install(self, root_el):
        self._doc = root_el
        self._renderer = QSvgRenderer(QByteArray(etree.tostring(root_el)))
        vb = self._renderer.viewBoxF()
        self.vb = QRectF(vb)
        self._geom = None
        self._doc_dirty = True

    def set_svg(self, s): self._install(etree.fromstring(s.encode()))

    # style channel: lets Draw/FillIn/Recolor target generated objects
    @property
    def elem(self):
        for el in self._doc.iter():
            if isinstance(el.tag, str):
                if etree.QName(el).localname not in ("svg", "defs", "style"):
                    return el
        return self._doc

    def style_set(self, **kv):
        if not hasattr(self, "_live"): self._live = {}
        self._live.update(kv); self._flush()

    def style_pop(self, *keys):
        for k in keys: self._live.pop(k, None)
        self._flush()

    def _flush(self):
        if not hasattr(self, "_base_style"):
            self._base_style = self.elem.get("style", "")
        if self._live:
            extra = ";".join(f"{k}:{v}" for k, v in self._live.items())
            self.elem.set("style", (self._base_style + ";" if self._base_style else "") + extra)
        elif self._base_style:
            self.elem.set("style", self._base_style)
        else:
            self.elem.attrib.pop("style", None)
        self._install(self._doc)

    def invalidate(self):
        self._install(self._doc)

    def geom(self):
        if self._geom is None:
            for el in self._doc.iter():
                if isinstance(el.tag, str):
                    g = _geom_for(el)
                    if g is not None and not g.isEmpty():
                        self._geom = g; break
        return self._geom

    def content_size(self):
        return self.vb.width() * self.scale, self.vb.height() * self.scale

    def rasterize(self, density):
        vb = self.vb
        img, p, d = _raster_surface(vb.width(), vb.height(), density)
        self._renderer.render(p, QRectF(0, 0, img.width(), img.height()))
        p.end()
        return img, QRectF(-vb.width()/2, -vb.height()/2, vb.width(), vb.height()), d

    def paint(self, p):
        if self.opacity <= 0: return
        p.save()
        p.setOpacity(p.opacity() * self.opacity)
        p.translate(self.x, self.y); p.rotate(self.rotation); p.scale(self.scale, self.scale)
        self._renderer.render(p, QRectF(-self.vb.width()/2, -self.vb.height()/2,
                                        self.vb.width(), self.vb.height()))
        p.restore()


class Text(GeneratedObj):
    """Vector-outline text (font needed only at build time)."""
    def __init__(self, s, size=36, color="#e8e8f0", font="sans-serif", weight="normal"):
        super().__init__(f'<svg xmlns="{SVG_NS}" viewBox="0 0 1 1"/>')
        self.cfg = dict(size=size, color=color, font=font, weight=weight)
        self.set_text(s)

    def _qfont(self):
        f = QFont(self.cfg["font"]); f.setPixelSize(int(self.cfg["size"]))
        if str(self.cfg["weight"]).lower() in ("bold", "700", "800", "900"):
            f.setWeight(QFont.Bold)
        return f

    def set_text(self, s):
        self._s = s
        f = self._qfont(); fm = QFontMetricsF(f)
        lines = s.split("\n")
        lh = fm.height() * 1.2
        w = max((fm.horizontalAdvance(l) for l in lines), default=0.0)
        path = QPainterPath()
        for i, l in enumerate(lines):
            if not l: continue
            path.addText((w - fm.horizontalAdvance(l)) / 2, lh * i + fm.ascent(), f, l)
        if path.isEmpty():
            self._install(etree.fromstring(
                f'<svg xmlns="{SVG_NS}" viewBox="0 0 1 1"/>'.encode())); return
        bb, pad = path.boundingRect(), 2
        vb = QRectF(bb.x()-pad, bb.y()-pad, bb.width()+2*pad, bb.height()+2*pad)
        root = etree.Element(f"{{{SVG_NS}}}svg", nsmap=NSMAP)
        root.set("viewBox", f"{vb.x():.1f} {vb.y():.1f} {vb.width():.1f} {vb.height():.1f}")
        pe = etree.SubElement(root, f"{{{SVG_NS}}}path")
        pe.set("d", qpath_to_svg_d(path))
        pe.set("fill", self.cfg["color"]); pe.set("fill-rule", "evenodd")
        self._install(root)


class Image(_Obj):
    def __init__(self, path, height=None):
        super().__init__()
        self.path = path
        self.img = QImage(path)
        s = 1.0 if height is None else height / max(self.img.height(), 1)
        self.x = self.y = 0.0
        self.scale, self.rotation, self.opacity = s, 0.0, 1.0
        self._w = float(self.img.width()); self._h = float(self.img.height())

    def content_size(self): return self._w * self.scale, self._h * self.scale

    def rasterize(self, density):
        # native resolution is the ceiling — report requested density
        return self.img, QRectF(-self._w/2, -self._h/2, self._w, self._h), density

    def paint(self, p):
        if self.opacity <= 0: return
        p.save()
        p.setOpacity(p.opacity() * self.opacity)
        p.translate(self.x, self.y); p.rotate(self.rotation); p.scale(self.scale, self.scale)
        p.drawImage(QRectF(-self._w/2, -self._h/2, self._w, self._h), self.img)
        p.restore()


class Group(_Obj):
    def __init__(self, *members):
        super().__init__()
        self.members = list(members)
        n = len(members) or 1
        self.x = sum(m.x for m in members) / n
        self.y = sum(m.y for m in members) / n
        self.scale, self.rotation, self.opacity = 1.0, 0.0, 1.0

    def paint(self, p):
        if self.opacity <= 0: return
        p.save()
        p.setOpacity(p.opacity() * self.opacity)
        p.translate(self.x, self.y); p.rotate(self.rotation); p.scale(self.scale, self.scale)
        p.translate(-self.x, -self.y)
        for m in self.members: m.paint(p)
        p.restore()


class Camera(_Obj):
    def __init__(self):
        super().__init__()
        self.x = self.y = 0.0
        self.scale, self.rotation, self.opacity = 1.0, 0.0, 1.0
    def zoom(self, f): self.scale *= f
    def paint(self, p): pass


class Selection(list):
    @property
    def animate(self): return _Anims(*self)

# ---------------------------------------------------------------- generators
def arrow(p1, p2, color="#9aa0b0", width=3, head=12):
    (x1, y1), (x2, y2) = p1, p2
    d = math.hypot(x2-x1, y2-y1) or 1.0
    ux, uy = (x2-x1)/d, (y2-y1)/d
    bx, by = x2 - ux*head, y2 - uy*head
    px, py = -uy, ux
    a1 = (bx + px*head*0.5, by + py*head*0.5)
    a2 = (bx - px*head*0.5, by - py*head*0.5)
    m = width + head
    minx, miny = min(x1, bx, a1[0], a2[0]) - m, min(y1, by, a1[1], a2[1]) - m
    maxx, maxy = max(x1, bx, a1[0], a2[0]) + m, max(y1, by, a1[1], a2[1]) + m
    svg = (f'<svg xmlns="{SVG_NS}" viewBox="{minx:.1f} {miny:.1f} '
           f'{maxx-minx:.1f} {maxy-miny:.1f}">'
           f'<path d="M{x1},{y1} L{bx:.1f},{by:.1f}" stroke="{color}" '
           f'stroke-width="{width}" fill="none" stroke-linecap="round"/>'
           f'<polygon points="{x2:.1f},{y2:.1f} {a1[0]:.1f},{a1[1]:.1f} '
           f'{a2[0]:.1f},{a2[1]:.1f}" fill="{color}"/></svg>')
    a = GeneratedObj(svg)
    a.move_to((minx + maxx) / 2, (miny + maxy) / 2)
    return a

def ring_around(part, pad=10, color="#ffffff", width=3, radius=12):
    w, h = part.content_size()
    w += 2*pad; h += 2*pad
    svg = (f'<svg xmlns="{SVG_NS}" viewBox="0 0 {w:.1f} {h:.1f}">'
           f'<rect x="{width/2}" y="{width/2}" width="{w-width:.1f}" '
           f'height="{h-width:.1f}" rx="{radius}" fill="none" '
           f'stroke="{color}" stroke-width="{width}"/></svg>')
    r = GeneratedObj(svg)
    r.move_to(part.x, part.y); r.rotation = part.rotation
    return r

# ---------------------------------------------------------------- animations
class Animation:
    def __init__(self, run_time=1.0, easing=smooth, delay=0.0):
        self.run_time, self.easing, self.delay = run_time, easing, delay
        self.objects, self.total = [], run_time
    def begin(self): pass
    def finish(self): pass
    def alpha_at(self, t):
        tt = t * self.total - self.delay
        return 0.0 if tt <= 0 else (1.0 if tt >= self.run_time else tt / self.run_time)
    def integrate(self, t): self.interpolate(self.easing(self.alpha_at(t)))
    def interpolate(self, a): raise NotImplementedError


class _Anims:
    def __init__(self, *objects): self.objects, self.calls = objects, []
    def __getattr__(self, name):
        def call(*args): self.calls.append((name, args)); return self
        return call


class Tween(Animation):
    def __init__(self, builder, **kw):
        super().__init__(**kw)
        self.objects, self.calls = list(builder.objects), builder.calls
    def begin(self):
        self.starts = [o.state() for o in self.objects]
        ghosts = [o.copy() for o in self.objects]
        for g in ghosts:
            for name, args in self.calls: getattr(g, name)(*args)
        self.ends = [g.state() for g in ghosts]
    def interpolate(self, a):
        for o, s, e in zip(self.objects, self.starts, self.ends):
            o.set_state({k: s[k] + (e[k]-s[k]) * a for k in s})
    def finish(self):
        for o, e in zip(self.objects, self.ends): o.set_state(e)


class FadeIn(Animation):
    def __init__(self, objects, **kw):
        super().__init__(**kw)
        self.objects = list(objects) if isinstance(objects, (list, Selection)) else [objects]
    def begin(self): self.op = [o.opacity for o in self.objects]
    def interpolate(self, a):
        for o, base in zip(self.objects, self.op): o.opacity = base * a
    def finish(self):
        for o, base in zip(self.objects, self.op): o.opacity = base


class FadeOut(FadeIn):
    def interpolate(self, a):
        for o, base in zip(self.objects, self.op): o.opacity = base * (1 - a)
    def finish(self):
        for o in self.objects: o.opacity = 0.0


class Draw(Animation):
    def __init__(self, part, **kw):
        super().__init__(**kw); self.part = part; self.objects = [part]
    def begin(self):
        qp = self.part.geom()
        if qp is None or qp.isEmpty():
            raise ValueError("Draw: element has no drawable geometry")
        self.L = max(_qlen(qp), 1e-6)
        self.part.style_set(**{"stroke-dasharray": f"{self.L:.2f}",
                               "stroke-dashoffset": f"{self.L:.2f}",
                               "fill-opacity": "0"})
    def interpolate(self, a):
        self.part.style_set(**{"stroke-dashoffset": f"{self.L * (1-a):.2f}"})
    def finish(self):
        self.part.style_pop("stroke-dasharray", "stroke-dashoffset", "fill-opacity")


class FillIn(Animation):
    def __init__(self, part, **kw):
        super().__init__(**kw); self.part = part; self.objects = [part]
    def begin(self): self.part.style_set(**{"fill-opacity": "0"})
    def interpolate(self, a): self.part.style_set(**{"fill-opacity": f"{a:.3f}"})
    def finish(self): self.part.style_pop("fill-opacity")


class MoveAlongPath(Animation):
    def __init__(self, part, path_part, orient=False, fade=True, **kw):
        super().__init__(**kw)
        self.part, self.pathp, self.orient, self.fade = part, path_part, orient, fade
        self.objects = [part]
    def begin(self):
        qp = self.pathp.geom()
        if qp is None or qp.isEmpty(): raise ValueError("MoveAlongPath: no path geometry")
        self.qp = qp
        self.at = _arc_sampler(qp)          # constant speed (arc length)
        vb = self.part.svg.vb
        self.cx, self.cy, self.k = vb.center().x(), vb.center().y(), self.part.svg.k
    def interpolate(self, a):
        x, y, f = self.at(a)
        self.part.x = (x - self.cx) * self.k
        self.part.y = (y - self.cy) * self.k
        if self.orient: self.part.rotation = self.qp.angleAtPercent(clamp01(f))
        if self.fade: self.part.opacity = min(1.0, 4*a, 4*(1-a))
    def finish(self):
        if self.fade: self.part.opacity = 0.0


class Stagger(Animation):
    def __init__(self, *anims, lag_ratio=0.15, **kw):
        super().__init__(**kw)
        self.anims, self.lag = list(anims), lag_ratio
        self.run_time = max(a.run_time for a in anims) * (1 + lag_ratio * (len(anims)-1))
        self.objects = [o for a in anims for o in a.objects]
    def begin(self): [a.begin() for a in self.anims]
    def finish(self): [a.finish() for a in self.anims]
    def integrate(self, t):
        k = len(self.anims)
        sub = self.run_time / (1 + self.lag * (k-1))
        for j, a in enumerate(self.anims):
            a.interpolate(a.easing(clamp01(
                (t*self.run_time - j*self.lag*sub) / sub)))


class Sequence(Animation):
    def __init__(self, *anims, **kw):
        super().__init__(**kw)
        self.anims = list(anims)
        self.run_time = sum(a.run_time for a in anims)
        self.objects = [o for a in anims for o in a.objects]
        self._begun = [False] * len(self.anims)
    def begin(self): self._begun = [False] * len(self.anims)
    def _maybe_begin(self, i):
        if not self._begun[i]:
            self.anims[i].begin(); self._begun[i] = True
    def integrate(self, t):
        T = t * self.total; acc = 0.0
        for i, a in enumerate(self.anims):
            if T >= acc:
                self._maybe_begin(i)
                a.interpolate(a.easing(clamp01((T - acc) / a.run_time)))
            acc += a.run_time
    def finish(self):
        for i, a in enumerate(self.anims):
            self._maybe_begin(i); a.finish()


class Recolor(Animation):
    def __init__(self, part, fill=None, stroke=None, **kw):
        super().__init__(**kw)
        self.part, self.fill, self.stroke = part, fill, stroke
        self.objects = [part]
    @staticmethod
    def _rgb(c):
        c = str(c).lstrip("#")
        if len(c) == 3: c = "".join(ch*2 for ch in c)
        return tuple(int(c[i:i+2], 16) for i in (0, 2, 4))
    def _cur(self, attr, dflt):
        v = self.part._live.get(attr) or self.part.elem.get(attr) or dflt
        try: return self._rgb(v)
        except ValueError: return self._rgb(dflt)
    def begin(self):
        self.f0 = self._cur("fill", "#000000") if self.fill else None
        self.s0 = self._cur("stroke", "#000000") if self.stroke else None
    def _mix(self, c0, c1, a):
        return "#%02x%02x%02x" % tuple(round(s + (t-s)*a)
                                       for s, t in zip(c0, self._rgb(c1)))
    def interpolate(self, a):
        if self.fill: self.part.style_set(fill=self._mix(self.f0, self.fill, a))
        if self.stroke: self.part.style_set(stroke=self._mix(self.s0, self.stroke, a))
    def finish(self):
        if self.fill: self.part.style_set(fill=self.fill)
        if self.stroke: self.part.style_set(stroke=self.stroke)


class Indicate(Animation):
    def __init__(self, obj, amp=0.15, **kw):
        super().__init__(**kw); self.obj, self.amp = obj, amp; self.objects = [obj]
    def begin(self): self.s0 = self.obj.scale
    def interpolate(self, a):
        self.obj.scale = self.s0 * (1 + self.amp * math.sin(math.pi * a))
    def finish(self): self.obj.scale = self.s0


class Shake(Animation):
    def __init__(self, obj, intensity=10, freq=18, **kw):
        super().__init__(**kw)
        self.obj, self.amp, self.freq = obj, intensity, freq
        self.objects = [obj]
    def begin(self): self.x0, self.y0 = self.obj.x, self.obj.y
    def interpolate(self, a):
        d = math.exp(-3.5 * a); ph = 2 * math.pi * self.freq * a
        self.obj.x = self.x0 + self.amp * d * math.sin(ph)
        self.obj.y = self.y0 + self.amp * 0.6 * d * math.sin(ph + 1.3)
    def finish(self): self.obj.x, self.obj.y = self.x0, self.y0


class Morph(Animation):
    """Compound-path morph: subpaths matched greedily by centroid; extras
    collapse in place / grow from center."""
    def __init__(self, part, target, n=240, **kw):
        super().__init__(**kw)
        self.part, self.n = part, n
        self.target_d = target if isinstance(target, str) else target.elem.get("d")
        self.objects = [part]

    @staticmethod
    def _subpaths(qp):
        out = []
        for poly in qp.toSubpathPolygons():
            pts = [(p.x(), p.y()) for p in poly]
            if len(pts) >= 2: out.append(pts)
        return out

    @staticmethod
    def _clop(pts):
        L = sum(math.hypot(b[0]-a[0], b[1]-a[1]) for a, b in zip(pts, pts[1:]))
        return L + math.hypot(pts[0][0]-pts[-1][0], pts[0][1]-pts[-1][1])

    @staticmethod
    def _cent(pts):
        return (sum(p[0] for p in pts)/len(pts), sum(p[1] for p in pts)/len(pts))

    @staticmethod
    def _samp(pts, n):
        full = pts + [pts[0]]
        seg = [math.hypot(b[0]-a[0], b[1]-a[1]) for a, b in zip(full, full[1:])]
        total = sum(seg) or 1.0
        res, acc, j = [], 0.0, 0
        for k in range(n):
            target = k * total / max(n-1, 1)
            while j < len(seg)-1 and acc + seg[j] < target:
                acc += seg[j]; j += 1
            f = (target - acc) / seg[j] if seg[j] else 0.0
            a, b = full[j], full[j+1]
            res.append((a[0]+(b[0]-a[0])*f, a[1]+(b[1]-a[1])*f))
        return res

    def begin(self):
        if self.part.elem.get("d") is None:
            raise ValueError("Morph: part must be a <path> element")
        A = self._subpaths(self.part.geom())
        B = self._subpaths(svg_path_to_qpath(self.target_d))
        if not A or not B: raise ValueError("Morph: empty geometry")
        ca = [self._cent(p) for p in A]; cb = [self._cent(p) for p in B]
        cand = sorted((math.hypot(ca[i][0]-cb[j][0], ca[i][1]-cb[j][1]), i, j)
                      for i in range(len(A)) for j in range(len(B)))
        ua, ub, pairs = set(), set(), []
        for _, i, j in cand:
            if i in ua or j in ub: continue
            pairs.append((A[i], B[j])); ua.add(i); ub.add(j)
        for i, p in enumerate(A):
            if i not in ua:
                c = ca[i]; pairs.append((p, [c, (c[0]+.01, c[1])]))
        for j, p in enumerate(B):
            if j not in ub:
                c = cb[j]; pairs.append(([c, (c[0]+.01, c[1])], p))
        totA = sum(self._clop(p) for p, _ in pairs) or 1.0
        totB = sum(self._clop(q) for _, q in pairs) or 1.0
        self.pa, self.pb = [], []
        for p, q in pairs:
            share = (self._clop(p)/totA + self._clop(q)/totB) / 2
            k = max(6, round(self.n * share))
            self.pa.append(self._samp(p, k)); self.pb.append(self._samp(q, k))

    def interpolate(self, a):
        parts = []
        for P, Q in zip(self.pa, self.pb):
            pts = [f"{s[0]+(e[0]-s[0])*a:.1f},{s[1]+(e[1]-s[1])*a:.1f}"
                   for s, e in zip(P, Q)]
            parts.append("M" + " L".join(pts) + " Z")
        self.part.elem.set("d", " ".join(parts))
        self.part.invalidate()

    def finish(self):
        self.part.elem.set("d", self.target_d)
        self.part._geom = None
        self.part.invalidate()


class Typewriter(Animation):
    def __init__(self, text_obj, **kw):
        super().__init__(**kw); self.t = text_obj; self.objects = [text_obj]
    def begin(self): self.full = self.t._s; self.t.set_text("")
    def interpolate(self, a):
        self.t.set_text(self.full[:int(round(a * len(self.full)))])
    def finish(self): self.t.set_text(self.full)


class Tracker:
    def __init__(self, v=0.0): self.value = v


class ValueTo(Animation):
    def __init__(self, tracker, to, **kw):
        super().__init__(**kw); self.tr, self.to = tracker, to
    def begin(self): self.v0 = self.tr.value
    def interpolate(self, a): self.tr.value = self.v0 + (self.to - self.v0) * a
    def finish(self): self.tr.value = self.to

# ---------------------------------------------------------------- scene
class Scene:
    background = "#101014"
    SUPERSAMPLE = 2.0

    def __init__(self, width=1280, height=720, fps=30):
        self.w, self.h, self.fps = width, height, fps
        self.objects, self._writer = [], None
        self.camera = Camera()
        self._time, self._transparent = 0.0, False
        self._segcache, self._segments, self._crf = False, [], 20
        self._frames_done, self.progress_fn = 0, None
        self._record, self._snaps, self._intern = False, [], {}
        self._reg, self._next_gid = {}, 0
        self._tracks, self._layer_cache = [], {}
        self.segment_log = []

    def load(self, path): return Svg(path, canvas=(self.w, self.h))
    def text(self, s, **kw): return Text(s, **kw)
    def soundtrack(self, path, volume=1.0, fade_in=0.0, fade_out=0.0, start=0.0):
        self._tracks.append(dict(path=path, volume=volume, fade_in=fade_in,
                                 fade_out=fade_out, start=start))

    def _gid_of(self, o):
        gid = getattr(o, "_gid", None)
        if gid is None:
            gid = o._gid = self._next_gid
            self._reg[gid] = o
            self._next_gid += 1
        return gid

    def add(self, *objs):
        for o in objs: self._gid_of(o)
        self.objects += objs
    def remove(self, *objs):
        for o in objs: self.objects.remove(o)
    def clear(self): self.objects.clear()
    def bring_to_front(self, o):
        self.objects.remove(o); self.objects.append(o)
    def send_to_back(self, o):
        self.objects.remove(o); self.objects.insert(0, o)

    # -- coordinate mapping & picking -------------------------------------
    def stage_to_img(self, x, y):
        r = math.radians(self.camera.rotation); c, s = math.cos(r), math.sin(r)
        dx, dy = x - self.camera.x, y - self.camera.y
        return (self.w/2 + self.camera.scale * (dx*c - dy*s),
                self.h/2 + self.camera.scale * (dx*s + dy*c))

    def img_to_stage(self, ix, iy):
        r = math.radians(self.camera.rotation); c, s = math.cos(r), math.sin(r)
        dx = (ix - self.w/2) / self.camera.scale
        dy = (iy - self.h/2) / self.camera.scale
        return (self.camera.x + dx*c + dy*s, self.camera.y - dx*s + dy*c)

    @staticmethod
    def _inv(pt, g):
        r = math.radians(g.rotation); c, s = math.cos(r), math.sin(r)
        dx, dy = pt[0] - g.x, pt[1] - g.y
        return (g.x + (dx*c + dy*s) / g.scale, g.y + (-dx*s + dy*c) / g.scale)

    @staticmethod
    def _fwd(pt, g):
        r = math.radians(g.rotation); c, s = math.cos(r), math.sin(r)
        dx, dy = pt[0] - g.x, pt[1] - g.y
        return (g.x + g.scale * (dx*c - dy*s), g.y + g.scale * (dx*s + dy*c))

    def _ancestors_of(self, target):
        def find(objs, anc):
            for o in objs:
                if o is target: return list(anc)
                if isinstance(o, Group):
                    r = find(o.members, anc + [o])
                    if r is not None: return r
            return None
        return find(self.objects, []) or []

    def hit_test(self, sx, sy):
        def contains(o, lx, ly):
            if hasattr(o, "content_size"):
                hw, hh = o.content_size(); hw, hh = hw / 2, hh / 2
            else:
                hw = hh = 20.0
            return abs(lx - o.x) <= hw and abs(ly - o.y) <= hh
        found = []
        def walk(objs, mapper):
            for o in reversed(objs):
                if isinstance(o, Camera): continue
                if getattr(o, "opacity", 1) <= 0: continue
                if isinstance(o, Group):
                    if walk(o.members,
                            (lambda p, g=o, m=mapper: m(self._inv(p, g)))):
                        return True
                else:
                    lx, ly = mapper((sx, sy))
                    if contains(o, lx, ly):
                        found.append(o); return True
            return False
        walk(self.objects, lambda p: p)
        return found[0] if found else None

    def img_to_local(self, target, ix, iy):
        x, y = self.img_to_stage(ix, iy)
        for g in reversed(self._ancestors_of(target)):
            x, y = self._inv((x, y), g)
        return x, y

    def obj_corners(self, target):
        anc = self._ancestors_of(target)
        if hasattr(target, "content_size"):
            hw, hh = target.content_size()[0] / 2, target.content_size()[1] / 2
        else:
            hw = hh = 20.0
        r = math.radians(target.rotation); c, s = math.cos(r), math.sin(r)
        pts = []
        for dx, dy in ((-hw, -hh), (hw, -hh), (hw, hh), (-hw, hh)):
            p = (target.x + dx*c - dy*s, target.y + dx*s + dy*c)
            for g in anc:
                p = self._fwd(p, g)
            pts.append(self.stage_to_img(*p))
        return pts

    # -- timing -------------------------------------------------------------
    def play(self, *items, run_time=None, easing=smooth):
        anims = []
        for it in items:
            if isinstance(it, _Anims):
                anims.append(Tween(it, easing=easing))
            else:
                if easing is not smooth and it.easing is smooth:
                    it.easing = easing
                anims.append(it)
        for a in anims:
            for o in a.objects:
                if o not in self.objects and not isinstance(o, Camera):
                    self.add(o)
        total = run_time or max(a.delay + a.run_time for a in anims)
        n = max(1, round(total * self.fps))
        for a in anims: a.total = total; a.begin()
        self._run_segment(n, anims, self._caller_info(), "play")
        for a in anims: a.finish()

    def wait(self, seconds=1.0):
        n = max(1, round(seconds * self.fps))
        self._run_segment(n, [], self._caller_info(), "wait")

    def _caller_info(self):
        fr = inspect.currentframe().f_back.f_back
        try:
            lines = linecache.getlines(fr.f_code.co_filename)
            src = "".join(lines[fr.f_lineno - 1: fr.f_lineno + 2])
            return src, fr.f_code.co_filename, fr.f_lineno
        except Exception:
            return "", "", 0

    def _run_segment(self, n, anims, info, kind):
        rec_start = len(self._snaps) if self._record else None
        if self._segcache:
            key = self._segment_hash(info[0])
            f = os.path.join(CACHE_DIR, key + ".mp4")
            if os.path.exists(f):
                print(f"  [cached] {key[:10]}")
                self._loop(n, anims, emit=False)
            else:
                vw = VideoWriter(f, self.w, self.h, self.fps, "mp4", self._crf)
                self._writer = vw
                self._loop(n, anims, emit=True)
                vw.close()
            self._segments.append(f)
        else:
            self._loop(n, anims, emit=True)
        if self._record:
            self.segment_log.append(dict(
                start=rec_start, end=len(self._snaps),
                src=" ".join(info[0].split()) or "(wait)",
                file=info[1], line=info[2], kind=kind))

    def _loop(self, n, anims, emit):
        for i in range(n):
            t = (i + 1) / n
            for a in anims: a.integrate(t)
            self._tick()
            if self._record:
                self._snaps.append(self._snap_obj_state())
                self._count_frame()
            elif emit: self._emit()
            else: self._count_frame()

    def _tick(self):
        self._time += 1.0 / self.fps
        for o in list(self.objects):
            for fn in tuple(o.updaters):
                fn(o, self._time)

    # -- snapshots ------------------------------------------------------------
    @staticmethod
    def _content_root(o):
        if isinstance(o, Svg): return o.root
        return getattr(o, "_doc", None)

    def _intern_doc(self, o):
        root = self._content_root(o)
        if root is None: return None
        raw = etree.tostring(root)
        return self._intern.setdefault(raw, raw)

    def _snap_obj_state(self):
        return (self._time, self.camera.state(),
                [self._snap_entry(o) for o in self.objects])

    def _snap_entry(self, o):
        if not hasattr(o, "_snap_doc"):
            o._snap_doc = self._intern_doc(o)
        if getattr(o, "_doc_dirty", False):
            o._snap_doc = self._intern_doc(o)
            o._doc_dirty = False
        doc = getattr(o, "_snap_doc", None)
        if isinstance(o, Group):
            return (self._gid_of(o), o.state(), doc,
                    tuple(self._snap_entry(m) for m in o.members))
        return (self._gid_of(o), o.state(), doc)

    def _apply_doc(self, o, doc):
        if doc is None: return
        if isinstance(o, SvgPart):
            o._doc = etree.fromstring(doc)
            o._bytes = doc
            o._renderer = QSvgRenderer(QByteArray(doc))
            target = o._doc[-1] if o._wraps else o._doc
            o.elem = target[-1]
            o._geom = None
            o._snap_doc = doc
        elif isinstance(o, Svg):
            o.root = etree.fromstring(doc)
            o.renderer = QSvgRenderer(QByteArray(doc))
            o._snap_doc = doc
        elif isinstance(o, GeneratedObj):
            o._install(etree.fromstring(doc))
            o._snap_doc = doc

    def _apply_entry(self, o, entry):
        o.set_state(entry[1])
        self._apply_doc(o, entry[2])
        if len(entry) == 4:
            for m, sub in zip(o.members, entry[3]):
                self._apply_entry(m, sub)

    def restore(self, snap):
        t, cam, objs = snap
        self._time = t
        self.camera.set_state(cam)
        out = []
        for e in objs:
            o = self._reg[e[0]]
            self._apply_entry(o, e)
            out.append(o)
        self.objects = out

    def paint_snapshot(self, snap, use_cache=True):
        self.restore(snap)
        return self._render_image(use_cache=use_cache)

    def record_playable(self, fn, progress=None):
        """Run fn(self) capturing a snapshot per frame; no painting."""
        self._record, self._snaps, self._intern = True, [], {}
        self._layer_cache = {}
        self._transparent = False
        self._time, self._frames_done = 0.0, 0
        self.segment_log = []
        self.progress_fn = progress
        self._writer = NullWriter()
        fn()
        self._record = False
        return self._snaps

    def record_preview(self, progress=None):
        return self.record_playable(self.build, progress)

    # -- cache fingerprinting ---------------------------------------------------
    def _segment_hash(self, src):
        h = hashlib.sha256()
        for part in (self.__class__.__name__,
                     f"{self.w}x{self.h}@{self.fps}",
                     self.background, str(self._transparent), str(self._crf),
                     src, repr(round(self._time, 9)),
                     repr(sorted(self.camera.state().items()))):
            h.update(part.encode())
        for o in self.objects: self._fingerprint(o, h)
        return h.hexdigest()

    def _fingerprint(self, o, h):
        h.update(type(o).__name__.encode())
        h.update(repr(sorted(o.state().items())).encode())
        for fn in getattr(o, "updaters", []):
            h.update(self._fn_src(fn).encode())
        try:
            if isinstance(o, (SvgPart, GeneratedObj)):
                h.update(hashlib.sha256(etree.tostring(o._doc)).digest())
            elif isinstance(o, Svg):
                h.update(hashlib.sha256(etree.tostring(o.root)).digest())
            elif isinstance(o, Image):
                try:
                    with open(o.path, "rb") as fh:
                        h.update(hashlib.sha256(fh.read()).digest())
                except OSError:
                    h.update(str(o.path).encode())
            elif isinstance(o, Group):
                for m in o.members: self._fingerprint(m, h)
        except Exception:
            h.update(repr(id(o)).encode())

    @staticmethod
    def _fn_src(fn):
        try:
            return inspect.getsource(fn)
        except Exception:
            c = fn.__code__
            return repr((c.co_code, c.co_consts, c.co_names))

    # -- rendering ---------------------------------------------------------------
    def render(self, path, crf=20):
        self._segments, self._crf = [], crf
        ext = os.path.splitext(path)[1].lower()
        self._transparent = False
        if ext in (".mp4", ".m4v"):
            self._segcache = True
            os.makedirs(CACHE_DIR, exist_ok=True)
            self.build()
            self._concat(path)
        else:
            self._segcache = False
            if ext == ".gif":
                self._writer = VideoWriter(path, self.w, self.h, self.fps, "gif")
            elif ext == ".webm":
                self._writer = VideoWriter(path, self.w, self.h, self.fps, "webm", crf)
                self._transparent = True
            else:
                self._writer = PngSeqWriter(path)
                self._transparent = True
            self.build()
            self._writer.close()

    def _concat(self, out):
        if not self._segments:
            raise RuntimeError("no segments rendered")
        tmp = out + ".muted.mp4"
        lst = tmp + ".txt"
        with open(lst, "w") as f:
            for s in self._segments:
                f.write("file '%s'\n" % os.path.abspath(s).replace("\\", "/"))
        subprocess.run([_ffmpeg(), "-y", "-f", "concat", "-safe", "0",
                        "-i", lst, "-c", "copy", tmp],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        os.remove(lst)
        if self._tracks:
            mux_audio(tmp, self._tracks, out, self._frames_done / self.fps)
            os.remove(tmp)
        else:
            os.replace(tmp, out)

    def build(self): raise NotImplementedError

    def _render_image(self, use_cache=False):
        img = QImage(self.w, self.h, QImage.Format_RGBA8888)
        if not self._transparent:
            img.fill(QColor(self.background))
        p = QPainter(img)
        p.setRenderHints(QPainter.Antialiasing | QPainter.SmoothPixmapTransform)
        cam = self.camera
        p.save()
        p.translate(self.w/2, self.h/2)
        p.rotate(cam.rotation); p.scale(cam.scale, cam.scale)
        p.translate(-cam.x, -cam.y)
        for o in self.objects:
            if isinstance(o, Camera): continue
            if use_cache: self._paint_cached(p, o)
            else: o.paint(p)
        p.restore(); p.end()
        return img

    def _paint_cached(self, p, o):
        if isinstance(o, Group):
            if o.opacity <= 0: return
            p.save()
            p.setOpacity(p.opacity() * o.opacity)
            p.translate(o.x, o.y); p.rotate(o.rotation); p.scale(o.scale, o.scale)
            p.translate(-o.x, -o.y)
            for m in o.members: self._paint_cached(p, m)
            p.restore()
            return
        if o.opacity <= 0 or isinstance(o, Camera): return
        gid = self._gid_of(o)
        raw = getattr(o, "_snap_doc", None)
        ent = self._layer_cache.get(gid)
        want = max(o.scale, 1e-3) * max(self.camera.scale, 1e-3) * self.SUPERSAMPLE
        miss = ent is None or ent.raw is not raw
        if not miss:
            units = max(ent.rect.width(), ent.rect.height(), 1e-6)
            cap = 4096.0 / units
            if want > ent.density * 1.3:
                miss = min(want, cap) > ent.density * 1.05
            elif ent.density > cap * 1.05:
                miss = True
        if miss:
            pix, rect, dens = o.rasterize(want)
            ent = _Layer(pix, rect, raw, dens)
            self._layer_cache[gid] = ent
        p.save()
        p.setOpacity(p.opacity() * o.opacity)
        p.translate(o.x, o.y); p.rotate(o.rotation); p.scale(o.scale, o.scale)
        p.drawImage(ent.rect, ent.pix)
        p.restore()

    def _emit(self):
        self._writer.write(self._render_image(use_cache=False))
        self._count_frame()

    def _count_frame(self):
        self._frames_done += 1
        if self.progress_fn: self.progress_fn(self._frames_done)

# ---------------------------------------------------------------- writers
def _ffmpeg():
    ff = shutil.which("ffmpeg")
    if ff: return ff
    try:
        import imageio_ffmpeg; return imageio_ffmpeg.get_ffmpeg_exe()
    except ImportError:
        sys.exit("ffmpeg not found — install it, or: pip install imageio-ffmpeg")


class _Layer:
    __slots__ = ("pix", "rect", "raw", "density")
    def __init__(self, pix, rect, raw, density):
        self.pix, self.rect, self.raw, self.density = pix, rect, raw, density


class VideoWriter:
    def __init__(self, path, w, h, fps, fmt="mp4", crf=20):
        base = ["-y", "-f", "rawvideo", "-pix_fmt", "rgba",
                "-s", f"{w}x{h}", "-r", str(fps), "-i", "-"]
        if fmt == "mp4":
            tail = ["-an", "-c:v", "libx264", "-preset", "medium", "-crf", str(crf),
                    "-pix_fmt", "yuv420p", "-movflags", "+faststart"]
        elif fmt == "webm":
            tail = ["-an", "-c:v", "libvpx-vp9", "-crf", str(max(crf, 30)),
                    "-b:v", "0", "-pix_fmt", "yuva420p", "-auto-alt-ref", "0"]
        else:
            tail = ["-an", "-vf",
                    "split[a][b];[a]palettegen=max_colors=128[p];"
                    "[b][p]paletteuse=dither=bayer:bayer_scale=4",
                    "-loop", "0"]
        self.proc = subprocess.Popen([_ffmpeg(), *base, *tail, path],
                                     stdin=subprocess.PIPE,
                                     stdout=subprocess.DEVNULL,
                                     stderr=subprocess.DEVNULL)
        self.frame = 0

    def write(self, img):
        w, row = img.width(), img.width() * 4
        bpl, bits = img.bytesPerLine(), img.constBits()
        if bpl == row:
            self.proc.stdin.write(bytes(bits))
        else:
            buf = bytearray()
            for r in range(img.height()):
                buf += bits[r*bpl: r*bpl + row]
            self.proc.stdin.write(buf)
        self.frame += 1
        if self.frame % 30 == 0: print(f"\r  frame {self.frame}", end="", flush=True)

    def close(self):
        self.proc.stdin.close(); self.proc.wait()


class PngSeqWriter:
    def __init__(self, directory):
        self.dir = directory.rstrip("/\\")
        os.makedirs(self.dir, exist_ok=True)
        self.frame = 0
    def write(self, img):
        img.save(os.path.join(self.dir, f"frame_{self.frame:05d}.png"))
        self.frame += 1
    def close(self): print(f"  {self.frame} PNGs -> {self.dir}/")


class NullWriter:
    def write(self, img): pass
    def close(self): pass

# ---------------------------------------------------------------- xfade composite
def _pixelate(img, block):
    b = max(1, int(block))
    w = max(1, img.width() // b)
    h = max(1, img.height() // b)
    return (img.scaled(w, h, Qt.IgnoreAspectRatio, Qt.FastTransformation)
               .scaled(img.width(), img.height(), Qt.IgnoreAspectRatio,
                       Qt.FastTransformation))

_DISSOLVE_NX, _DISSOLVE_NY = 20, 12
_DISSOLVE_ORDER = None

def _dissolve_order():
    import random as _r
    cells = list(range(_DISSOLVE_NX * _DISSOLVE_NY))
    _r.Random(1234).shuffle(cells)
    return cells

def xfade_composite(a, b, ttype, p):
    """B over A at progress p for xfade type ttype (preview == export)."""
    global _DISSOLVE_ORDER
    p = clamp01(p)
    W, H = a.width(), a.height()
    out = QImage(W, H, QImage.Format_RGBA8888)
    out.fill(QColor(0, 0, 0, 255))
    pt = QPainter(out)
    if ttype == "fade":
        pt.drawImage(0, 0, a)
        pt.setOpacity(p); pt.drawImage(0, 0, b); pt.setOpacity(1.0)
    elif ttype == "fadeblack":
        if p < 0.5:
            pt.drawImage(0, 0, a)
            pt.fillRect(0, 0, W, H, QColor(0, 0, 0, int(510 * p)))
        else:
            pt.drawImage(0, 0, b)
            pt.fillRect(0, 0, W, H, QColor(0, 0, 0, int(255 * (2 - 2 * p))))
    elif ttype == "fadewhite":
        if p < 0.5:
            pt.drawImage(0, 0, a)
            pt.fillRect(0, 0, W, H, QColor(255, 255, 255, int(510 * p)))
        else:
            pt.drawImage(0, 0, b)
            pt.fillRect(0, 0, W, H, QColor(255, 255, 255, int(255 * (2 - 2 * p))))
    elif ttype == "wipeleft":
        pt.drawImage(0, 0, a)
        pt.save(); pt.setClipRect(QRectF((1 - p) * W, 0, p * W + 0.5, H))
        pt.drawImage(0, 0, b); pt.restore()
    elif ttype == "wiperight":
        pt.drawImage(0, 0, a)
        pt.save(); pt.setClipRect(QRectF(0, 0, p * W + 0.5, H))
        pt.drawImage(0, 0, b); pt.restore()
    elif ttype == "wipeup":
        pt.drawImage(0, 0, a)
        pt.save(); pt.setClipRect(QRectF(0, (1 - p) * H, W, p * H + 0.5))
        pt.drawImage(0, 0, b); pt.restore()
    elif ttype == "wipedown":
        pt.drawImage(0, 0, a)
        pt.save(); pt.setClipRect(QRectF(0, 0, W, p * H + 0.5))
        pt.drawImage(0, 0, b); pt.restore()
    elif ttype == "slideleft":
        pt.drawImage(QPointF(-p * W, 0), a)
        pt.drawImage(QPointF((1 - p) * W, 0), b)
    elif ttype == "slideright":
        pt.drawImage(QPointF(p * W, 0), a)
        pt.drawImage(QPointF(-(1 - p) * W, 0), b)
    elif ttype == "slideup":
        pt.drawImage(QPointF(0, -p * H), a)
        pt.drawImage(QPointF(0, (1 - p) * H), b)
    elif ttype == "slidedown":
        pt.drawImage(QPointF(0, p * H), a)
        pt.drawImage(QPointF(0, -(1 - p) * H), b)
    elif ttype == "circleopen":
        pt.drawImage(0, 0, a)
        R = p * 0.5 * math.hypot(W, H)
        path = QPainterPath()
        path.addEllipse(QPointF(W / 2, H / 2), max(R, 0.01), max(R, 0.01))
        pt.save(); pt.setClipPath(path); pt.drawImage(0, 0, b); pt.restore()
    elif ttype == "circleclose":
        pt.drawImage(0, 0, b)
        R = (1 - p) * 0.5 * math.hypot(W, H)
        path = QPainterPath()
        path.addEllipse(QPointF(W / 2, H / 2), max(R, 0.01), max(R, 0.01))
        pt.save(); pt.setClipPath(path); pt.drawImage(0, 0, a); pt.restore()
    elif ttype == "radial":
        pt.drawImage(0, 0, a)
        R = 0.5 * math.hypot(W, H)
        path = QPainterPath()
        path.moveTo(W / 2, H / 2)
        path.arcTo(QRectF(W / 2 - R, H / 2 - R, 2 * R, 2 * R),
                   -90.0, -360.0 * p)
        path.closeSubpath()
        pt.save(); pt.setClipPath(path); pt.drawImage(0, 0, b); pt.restore()
    elif ttype == "pixelize":
        if p < 0.5:
            pt.drawImage(0, 0, _pixelate(a, 1 + (p / 0.5) * 39))
        else:
            pt.drawImage(0, 0, _pixelate(b, 1 + ((1 - p) / 0.5) * 39))
    elif ttype == "dissolve":
        pt.drawImage(0, 0, a)
        if _DISSOLVE_ORDER is None:
            _DISSOLVE_ORDER = _dissolve_order()
        n = _DISSOLVE_NX * _DISSOLVE_NY
        k = int(p * n)
        if k > 0:
            cw, ch = W / _DISSOLVE_NX, H / _DISSOLVE_NY
            region = QRegion()
            for idx in _DISSOLVE_ORDER[:k]:
                cx, cy = idx % _DISSOLVE_NX, idx // _DISSOLVE_NX
                region += QRegion(QRectF(cx * cw, cy * ch, cw, ch).toRect())
            pt.save(); pt.setClipRegion(region)
            pt.drawImage(0, 0, b); pt.restore()
    else:
        pt.drawImage(0, 0, a)
        pt.setOpacity(p); pt.drawImage(0, 0, b); pt.setOpacity(1.0)
    pt.end()
    return out

# ---------------------------------------------------------------- srt / audio
def _srt_ts(sec):
    ms = int(round(max(sec, 0.0) * 1000))
    h, ms = divmod(ms, 3600000)
    m, ms = divmod(ms, 60000)
    s, ms = divmod(ms, 1000)
    return f"{h:02d}:{m:02d}:{s:02d},{ms:03d}"


def write_srt(path, entries):
    with open(path, "w", encoding="utf-8") as f:
        for i, (a, b, txt) in enumerate(entries, 1):
            f.write(f"{i}\n{_srt_ts(a)} --> {_srt_ts(max(b, a + 0.05))}\n"
                    f"{txt}\n\n")


def scene_srt_entries(scene, fps):
    out = []
    for s in scene.segment_log:
        txt = s["src"] if s["src"] != "(wait)" else "(hold)"
        out.append((s["start"] / fps, s["end"] / fps, txt))
    if out and scene._frames_done:
        a, b, t = out[-1]
        out[-1] = (a, scene._frames_done / fps, t)
    return out


def movie_srt_entries(studio, order, transitions, fps):
    marks, t, prev_d = [], 0.0, 0
    for i, key in enumerate(order):
        F = studio.built[key]["frames"]
        marks.append((t, studio.specs[key][0]))
        nxt = order[i + 1] if i + 1 < len(order) else None
        d = 0
        if nxt:
            tr = transitions.get((key, nxt))
            if tr:
                d = max(2, round(tr[1] * fps))
                d = min(d, F, studio.built[nxt]["frames"])
                if d < 2: d = 0
        t += (F - prev_d) / fps
        prev_d = d
    total = t
    return [(a, marks[i + 1][0] if i + 1 < len(marks) else total, label)
            for i, (a, label) in enumerate(marks)]


def mux_audio(vid, tracks, out, duration):
    args, flts = ["-i", vid], []
    for i, tr in enumerate(tracks):
        args += ["-i", tr["path"]]
        f = (f"[{i+1}:a]atrim=start={tr['start']},asetpts=PTS-STARTPTS"
             f",volume={tr['volume']}")
        if tr["fade_in"] > 0:  f += f",afade=t=in:d={tr['fade_in']}"
        if tr["fade_out"] > 0:
            st = max(duration - tr["start"] - tr["fade_out"], 0.0)
            f += f",afade=t=out:st={st:.3f}:d={tr['fade_out']}"
        f += f"[t{i}]"; flts.append(f)
    if len(flts) > 1:
        flts.append("".join(f"[t{i}]" for i in range(len(tracks)))
                    + f"amix=inputs={len(tracks)}:normalize=0,apad[aout]")
    else:
        flts.append("[t0]apad[aout]")
    r = subprocess.run([_ffmpeg(), "-y", *args, "-filter_complex",
                        ";".join(flts), "-map", "0:v", "-map", "[aout]",
                        "-c:v", "copy", "-c:a", "aac", "-b:a", "192k",
                        "-shortest", out],
                       stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    if r.returncode != 0:
        sys.stderr.write(r.stderr.decode(errors="replace")[-800:])
        raise RuntimeError("audio mux failed — check track paths/codecs")

# ---------------------------------------------------------------- projects
ASSET_EXTS = {".svg", ".png", ".jpg", ".jpeg", ".gif", ".bmp", ".webp",
              ".mp3", ".wav", ".ogg", ".m4a", ".flac", ".ttf", ".otf"}

def pack_project(scene_py, out_zip):
    scene_py = os.path.abspath(scene_py)
    base = os.path.dirname(scene_py)
    refs, missing = [], []
    try:
        tree = ast.parse(open(scene_py, encoding="utf-8").read())
    except (OSError, SyntaxError) as e:
        sys.exit(f"cannot read {scene_py}: {e}")
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            v = node.value.strip()
            if not v or "\n" in v or len(v) > 512: continue
            if os.path.splitext(v)[1].lower() in ASSET_EXTS:
                for root in (base, os.getcwd()):
                    cand = os.path.abspath(os.path.join(root, v))
                    if os.path.isfile(cand):
                        refs.append((v, cand)); break
                else:
                    missing.append(v)
    with zipfile.ZipFile(out_zip, "w", zipfile.ZIP_DEFLATED) as z:
        z.write(scene_py, os.path.basename(scene_py))
        if os.path.abspath(__file__) != scene_py:
            z.write(__file__, "svglab.py")
        for rel, full in refs:
            arc = os.path.relpath(full, base)
            if arc.startswith(".."):
                arc = "assets/" + os.path.basename(full)
            z.write(full, arc)
        z.writestr("manifest.json", json.dumps(
            {"scene": os.path.basename(scene_py), "engine": "svglab.py",
             "assets": sorted(r for r, _ in refs),
             "missing": sorted(set(missing))}, indent=2))
    print(f"packed scene + {len(refs)} assets -> {out_zip}")
    for m in sorted(set(missing)):
        print(f"  ! referenced but not found: {m}")


def _read_project(zpath):
    tmpdir = os.path.abspath(os.path.splitext(os.path.basename(zpath))[0] + "_proj")
    os.makedirs(tmpdir, exist_ok=True)
    with zipfile.ZipFile(zpath) as z:
        for info in z.infolist():
            n = os.path.normpath(info.filename)
            if n.startswith("..") or os.path.isabs(n):
                sys.exit(f"unsafe path in project: {info.filename}")
        z.extractall(tmpdir)
    pys = [f for f in os.listdir(tmpdir)
           if f.endswith(".py") and f != "svglab.py"]
    if not pys: sys.exit("no scene file found in project")
    return os.path.join(tmpdir, pys[0]), tmpdir


def unpack_project(zpath):
    scene, d = _read_project(zpath)
    print(f"extracted -> {d}/")
    print(f'run:  python svglab.py "{scene}"  (or pass the .zip directly)')


def _scene_module(path):
    import importlib
    path = os.path.abspath(path)
    d, fn = os.path.split(path)
    name = fn[:-3]
    if d not in sys.path:
        sys.path.insert(0, d)
    mod = sys.modules.get(name)
    if mod is not None and os.path.abspath(getattr(mod, "__file__", "")) == path:
        return importlib.reload(mod)
    return importlib.import_module(name)


def load_project(path):
    """(cls, kind) — kind is 'movie' or 'scene'. Reload-safe."""
    mod = _scene_module(path)
    movies, scenes = [], []
    for o in vars(mod).values():
        if not (isinstance(o, type) and o.__module__ == mod.__name__):
            continue
        if (callable(getattr(o, "clips", None))
                and getattr(o, "SceneClass", None) is not None):
            movies.append(o)
        elif callable(getattr(o, "build", None)) and hasattr(o, "play"):
            scenes.append(o)
    if movies: return movies[-1], "movie"
    if scenes: return scenes[-1], "scene"
    raise RuntimeError(f"no Scene/Movie class found in {os.path.basename(path)}")


def load_scene_cls(path):
    cls, kind = load_project(path)
    if kind != "scene":
        raise RuntimeError(f"{os.path.basename(path)} is a Movie project (clips GUI)")
    return cls

# ---------------------------------------------------------------- source patcher
class SourcePatcher:
    """Best-effort text surgery on a scene file. Never patches on failure."""

    def __init__(self, path):
        self.path = path
        with open(path, encoding="utf-8") as f:
            self.lines = f.readlines()

    def _stmt_index(self, seg):
        lo = max(0, seg["line"] - 10)
        for i in range(min(seg["line"] - 1, len(self.lines) - 1), lo - 1, -1):
            if f"self.{seg['kind']}(" in self.lines[i]:
                return i
        return None

    def _indent_of(self, i):
        ln = self.lines[i]
        return ln[:len(ln) - len(ln.lstrip())]

    def _save(self):
        with open(self.path, "w", encoding="utf-8") as f:
            f.writelines(self.lines)

    def patch_move(self, sel, x, y, anchor_line):
        tok = f"{sel}[0].move_to("
        hits = [i for i, ln in enumerate(self.lines) if tok in ln]
        text = f"{tok.rstrip('(')}({x:.1f}, {y:.1f})\n"
        if hits:
            idx = hits[-1]
            self.lines[idx] = self._indent_of(idx) + text
            self._save()
            return "updated"
        anchor = self._stmt_index({"kind": "play", "line": anchor_line})
        if anchor is None:
            anchor = self._stmt_index({"kind": "wait", "line": anchor_line})
        if anchor is None:
            raise RuntimeError("could not locate the play()/wait() line")
        self.lines.insert(anchor, self._indent_of(anchor) + text)
        self._save()
        return "inserted"

    def patch_duration(self, seg, frames, fps):
        if frames < 2:
            raise RuntimeError("segment too short")
        new_sec = frames / fps
        i = self._stmt_index(seg)
        if i is None:
            raise RuntimeError("could not locate the call line")
        if seg["kind"] == "wait":
            line = self.lines[i]
            if re.search(r"self\.wait\(\s*\)", line):
                self.lines[i] = line.replace(
                    "self.wait()", f"self.wait({new_sec:.2f})")
                self._save(); return f"wait -> {new_sec:.2f}s"
            line, n = re.subn(r"(self\.wait\()\s*[0-9.]+\s*(\))",
                              rf"\g<1>{new_sec:.2f}\g<2>", line)
            if n:
                self.lines[i] = line
                self._save(); return f"wait -> {new_sec:.2f}s"
            raise RuntimeError("wait(<number>) not found on that line")
        for j in range(i, min(i + 3, len(self.lines))):
            line, n = re.subn(r"(run_time\s*=\s*)[0-9.]+",
                              rf"\g<1>{new_sec:.2f}", self.lines[j])
            if n:
                self.lines[j] = line
                self._save(); return f"run_time -> {new_sec:.2f}s"
        line = self.lines[i]
        if "self.play(" in line and line.rstrip().endswith(")"):
            core = line.rstrip()[:-1].rstrip()
            if core.endswith(","):
                core = core[:-1].rstrip()
            self.lines[i] = f"{core}, run_time={new_sec:.2f})\n"
            self._save(); return f"run_time={new_sec:.2f} added"
        raise RuntimeError("multi-line call without run_time= — add it manually")

# ---------------------------------------------------------------- movies
XFADE_TYPES = ["fade", "fadeblack", "fadewhite", "dissolve",
               "wipeleft", "wiperight", "wipeup", "wipedown",
               "slideleft", "slideright", "slideup", "slidedown",
               "circleopen", "circleclose", "pixelize", "radial"]


class Movie:
    """Reorderable clip project. Define clip_* methods — each gets a FRESH
    Scene, so clips are independent and assemble in any order.

        def clip_card(self, s, color="#4aa8ff", word="card"):
            ...

    Parameters after `s` become variant options. Playlist entries may be a
    name ("card") or {"clip": "card", "args": {...}}. Identical arg sets
    share one render. soundtrack(...) is muxed onto the final MP4."""
    SceneClass = Scene

    def soundtrack(self, path, volume=1.0, fade_in=0.0, fade_out=0.0, start=0.0):
        if not hasattr(self, "_tracks"):
            self._tracks = []
        self._tracks.append(dict(path=path, volume=volume, fade_in=fade_in,
                                 fade_out=fade_out, start=start))

    def clips(self):
        items = [(k, v) for k, v in vars(type(self)).items()
                 if k.startswith("clip_") and callable(v)]
        items.sort(key=lambda kv: kv[1].__code__.co_firstlineno)
        return [(k[5:], getattr(self, k)) for k, v in items]

    def params(self, name):
        fn = dict(self.clips()).get(name)
        if fn is None:
            raise KeyError(f"unknown clip: {name}")
        return [(p, v.default) for p, v in inspect.signature(fn).parameters.items()
                if p != "s"]

    def resolve(self, name, args=None):
        args = dict(args or {})
        fn = dict(self.clips()).get(name)
        if fn is None:
            raise KeyError(f"unknown clip: {name}")
        known = {p for p, _ in self.params(name)}
        unknown = set(args) - known
        if unknown:
            raise ValueError(f"{name}: unknown option(s) {sorted(unknown)}")
        missing = [p for p, dflt in self.params(name)
                   if dflt is inspect.Parameter.empty and p not in args]
        if missing:
            raise ValueError(f"{name}: missing required {missing}")
        key = (name if not args else
               f"{name}[{hashlib.sha256(repr(sorted(args.items())).encode()).hexdigest()[:8]}]")
        call = (lambda s, _f=fn, _a=args: _f(s, **_a)) if args else fn
        return key, call


class ClipStudio:
    """Renders clips in isolation; cut boundaries concat -c copy (zero
    encode), transitioned boundaries group into cached join encodes."""
    def __init__(self, project, width=1280, height=720, fps=30, crf=20):
        self.project = project
        self.w, self.h, self.fps, self.crf = width, height, fps, crf
        self.built, self.specs = {}, {}

    def names(self):
        return [n for n, _ in self.project.clips()]

    def params(self, name):
        return self.project.params(name)

    def ensure_spec(self, name, args=None):
        key, call = self.project.resolve(name, args)
        self.specs.setdefault(key, (name, dict(args or {}), call))
        return key

    def _fn(self, key):
        return self.specs[key][2]

    def build_clip(self, key, progress=None):
        if key in self.built:
            return self.built[key]
        if key not in self.specs:
            raise KeyError(f"clip spec not registered: {key}")
        fn = self._fn(key)
        sc = self.project.SceneClass(width=self.w, height=self.h, fps=self.fps)
        sc._crf = self.crf
        sc._segcache = True
        os.makedirs(CACHE_DIR, exist_ok=True)
        sc.progress_fn = progress
        fn(sc)
        segments, log = list(sc._segments), list(sc.segment_log)
        full = os.path.join(CACHE_DIR, "joins",
                            "full_" + hashlib.sha256(key.encode()).hexdigest()[:16] + ".mp4")
        os.makedirs(os.path.dirname(full), exist_ok=True)
        lst = full + ".txt"
        with open(lst, "w") as f:
            for s in segments:
                f.write("file '%s'\n" % os.path.abspath(s).replace("\\", "/"))
        subprocess.run([_ffmpeg(), "-y", "-f", "concat", "-safe", "0",
                        "-i", lst, "-c", "copy", full],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        os.remove(lst)
        rc = self.project.SceneClass(width=self.w, height=self.h, fps=self.fps)
        snaps = rc.record_playable(fn, progress=progress)
        self.built[key] = dict(segments=segments, full=full, snaps=snaps,
                               scene=rc, frames=len(snaps), log=log)
        return self.built[key]

    def ensure_all(self, progress=None):
        names = self.names()
        for i, n in enumerate(names):
            key = self.ensure_spec(n)
            if key in self.built:
                continue
            wrap = ((lambda k, ii: lambda c: progress(
                        c, f"clip {ii+1}/{len(names)}: {k}"))(key, i)
                    if progress else None)
            self.build_clip(key, wrap)

    def _join_group(self, keys, specs):
        h = hashlib.sha256(repr((tuple(keys), tuple(map(tuple, specs)),
                                 self.w, self.h, self.fps, self.crf)).encode()).hexdigest()
        path = os.path.join(CACHE_DIR, "joins", h[:24] + ".mp4")
        if os.path.exists(path):
            print(f"  [join cached] {' -> '.join(keys)}")
            return path
        os.makedirs(os.path.dirname(path), exist_ok=True)
        cmd = [_ffmpeg(), "-y"]
        for k in keys:
            cmd += ["-i", self.built[k]["full"]]
        Ls = [self.built[k]["frames"] / self.fps for k in keys]
        parts, running = [], Ls[0]
        for i, (t, Df) in enumerate(specs, start=1):
            D = Df / self.fps
            off = max(running - D, 0.0)
            a = "[0:v]" if i == 1 else f"[t{i-1}]"
            parts.append(f"{a}[{i}:v]xfade=transition={t}"
                         f":duration={D:.6f}:offset={off:.6f}[t{i}]")
            running = off + Ls[i]
        chain = ";".join(parts) + f";[t{len(specs)}]format=yuv420p[v]"
        cmd += ["-filter_complex", chain, "-map", "[v]",
                "-c:v", "libx264", "-preset", "medium", "-crf", str(self.crf),
                "-pix_fmt", "yuv420p", "-r", str(self.fps),
                "-movflags", "+faststart", path]
        print(f"  [join] {' -> '.join(keys)}  "
              f"({', '.join(f'{t}@{Df/self.fps:.2f}s' for t, Df in specs)})")
        r = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        if r.returncode != 0:
            sys.stderr.write(r.stderr.decode(errors="replace")[-600:])
            raise RuntimeError("transition join failed")
        return path

    def assemble(self, order, out_path, transitions=None):
        transitions = transitions or {}
        pieces, frames = [], 0
        i = 0
        while i < len(order):
            group = [order[i]]
            specs = []
            j = i
            while j + 1 < len(order):
                tr = transitions.get((order[j], order[j + 1]))
                if not tr: break
                t, dur = tr
                if t not in XFADE_TYPES: break
                Df = max(2, round(dur * self.fps))
                Df = min(Df, self.built[order[j]]["frames"],
                         self.built[order[j + 1]]["frames"])
                if Df < 2: break
                specs.append((t, Df))
                group.append(order[j + 1])
                j += 1
            if len(group) == 1:
                c = self.built.get(group[0]) or self.build_clip(group[0])
                pieces += c["segments"]
                frames += c["frames"]
            else:
                for k in group:
                    if k not in self.built:
                        self.build_clip(k)
                path = self._join_group(group, specs)
                pieces.append(path)
                frames += (sum(self.built[k]["frames"] for k in group)
                           - sum(Df for _, Df in specs))
            i = j + 1
        if not pieces:
            raise RuntimeError("nothing to assemble")
        tmp = out_path + ".muted.mp4"
        lst = tmp + ".txt"
        with open(lst, "w") as f:
            for s in pieces:
                f.write("file '%s'\n" % os.path.abspath(s).replace("\\", "/"))
        subprocess.run([_ffmpeg(), "-y", "-f", "concat", "-safe", "0",
                        "-i", lst, "-c", "copy", tmp],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        os.remove(lst)
        tracks = getattr(self.project, "_tracks", [])
        if tracks:
            mux_audio(tmp, tracks, out_path, frames / self.fps)
            os.remove(tmp)
        else:
            os.replace(tmp, out_path)
        return out_path


MOVIE_TEMPLATE = '''"""svglab clip project — each clip_* method is an independent,
reorder-safe shot on a fresh Scene (the `s` argument). Parameters after `s`
become variant options; the playlist can instantiate them per instance."""
from svglab import *


class MyMovie(Movie):
    def clip_intro(self, s):
        t = s.text("Hello", size=72)
        s.play(FadeIn(t), run_time=0.5)
        s.wait(0.6)
        s.play(FadeOut(t), run_time=0.5)

    def clip_card(self, s, color="#4aa8ff", word="card"):
        t = s.text(word, size=72, color=color)
        s.play(FadeIn(t), run_time=0.4)
        s.play(t.animate.scale_by(1.4), run_time=0.7)
        s.wait(0.4)
        s.play(FadeOut(t), run_time=0.4)

    def clip_outro(self, s):
        t = s.text("svglab", size=56, color="#59d499")
        s.play(FadeIn(t), run_time=0.5)
        s.wait(0.8)
        s.play(FadeOut(t), run_time=0.5)
'''

# ---------------------------------------------------------------- demo
DEMO_SVG = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 480 270">
  <rect width="480" height="270" rx="14" fill="#15151f"/>
  <path id="wire" d="M96,190 C160,110 320,110 384,190" fill="none"
        stroke="#4aa8ff" stroke-width="4" stroke-linecap="round"/>
  <circle class="node" id="n1" cx="96"  cy="190" r="18" fill="#f6c445"/>
  <circle class="node" id="n2" cx="240" cy="128" r="18" fill="#e05a5a"/>
  <circle class="node" id="n3" cx="384" cy="190" r="18" fill="#59d499"/>
  <circle id="packet" cx="96" cy="190" r="7" fill="#ffffff"/>
</svg>"""


class Demo(Scene):
    def build(self):
        with open("demo.svg", "w") as f: f.write(DEMO_SVG)
        svg = self.load("demo.svg")
        self.play(FadeIn(svg), run_time=0.6)

        nodes = svg.select(".node")
        wire  = svg.select("#wire")[0]
        pkt   = svg.select("#packet")[0]

        self.remove(*nodes)
        self.play(Stagger(*[FadeIn(n) for n in nodes], lag_ratio=0.2), run_time=1.2)
        self.play(Draw(wire), run_time=1.2)

        title = self.text("Systems in Motion", size=52)
        title.move_to(0, -self.h/2 + 70)
        self.play(Typewriter(title), run_time=1.2)

        pct = self.text("0%", size=40); pct.move_to(0, self.h/2 - 60)
        pkt.opacity = 0.0
        self.add(pkt, pct)
        tr = Tracker(0.0)
        pct.add_updater(lambda p, t: p.set_text(f"{tr.value*100:.0f}%"))
        self.play(ValueTo(tr, 1.0),
                  MoveAlongPath(pkt, wire, orient=True),
                  run_time=2.2, easing=linear)
        pct.remove_updater(pct.updaters[0]); pct.set_text("100%")

        self.play(Recolor(nodes[1], fill="#7c5cff"), run_time=0.5)
        ring = ring_around(nodes[1], color="#7c5cff")
        self.add(ring)
        self.play(Sequence(Draw(ring, run_time=0.6),
                           Indicate(nodes[1], run_time=0.5)), run_time=1.1)
        self.play(FadeOut(ring), run_time=0.4)

        ar = arrow((nodes[0].x, nodes[0].y - 36), (nodes[0].x, nodes[0].y - 22),
                   color="#f6c445")
        self.add(ar)
        self.play(FadeIn(ar), run_time=0.4)

        self.play(Tween(self.camera.animate
                        .move_to(nodes[2].x, nodes[2].y).zoom(2.2)), run_time=1.0)
        tag = self.text("exit node", size=24)
        tag.move_to(nodes[2].x, nodes[2].y + 46)
        self.play(FadeIn(tag), run_time=0.4)
        self.wait(0.4)
        self.play(FadeOut(tag),
                  Tween(self.camera.animate.move_to(0, 0).zoom(1)), run_time=0.8)

        self.play(Morph(wire, "M96,190 C150,110 210,250 240,128 S330,60 384,190"),
                  run_time=1.4)
        self.play(Shake(title, intensity=7), run_time=0.5)

        grp = Group(*nodes)
        self.remove(*nodes); self.add(grp)
        self.play(grp.animate.shift(0, 26), run_time=0.8)

        self.play(*[FadeOut(o) for o in list(self.objects)], run_time=0.8)

# ==================================================================== GUI ===
SCENE_CLASS = Demo

QUAL = {"480p15": (854, 480, 15, 28), "720p30": (1280, 720, 30, 23),
        "1080p60": (1920, 1080, 60, 20)}
SEGCOLORS = ["#1f3a5f", "#25462f", "#4a3a1f", "#3a2546", "#462525",
             "#1f4a44", "#4a2438"]
FMT_EXT = {"MP4": ".mp4", "GIF": ".gif", "WebM (alpha)": ".webm"}


class Canvas(QWidget):
    def __init__(self):
        super().__init__()
        self.img = None; self.overlay = None; self.drag_cb = None
        self._pressed = False
        self.setMinimumSize(480, 270)
    def set_image(self, img):
        self.img = img; self.update()
    def set_overlay(self, pts): self.overlay = pts; self.update()
    def _img_xy(self, e):
        iw, ih = self.img.width(), self.img.height()
        vs = min(self.width() / iw, self.height() / ih)
        ox, oy = (self.width() - iw*vs) / 2, (self.height() - ih*vs) / 2
        ix, iy = (e.position().x() - ox) / vs, (e.position().y() - oy) / vs
        return ix, iy, 0 <= ix < iw and 0 <= iy < ih
    def mousePressEvent(self, e):
        if self.img is None or self.drag_cb is None: return
        ix, iy, ok = self._img_xy(e)
        if ok:
            self._pressed = True
            self.drag_cb(ix, iy, "start")
    def mouseMoveEvent(self, e):
        if self.img is None or self.drag_cb is None or not self._pressed: return
        ix, iy, _ = self._img_xy(e)
        self.drag_cb(ix, iy, "move")
    def mouseReleaseEvent(self, e):
        if not self._pressed: return
        self._pressed = False
        if self.img is not None and self.drag_cb is not None:
            ix, iy, _ = self._img_xy(e)
            self.drag_cb(ix, iy, "end")
    def paintEvent(self, ev):
        p = QPainter(self)
        p.fillRect(self.rect(), QColor("#0a0a0e"))
        if self.img is not None:
            iw, ih = self.img.width(), self.img.height()
            vs = min(self.width() / iw, self.height() / ih)
            w, h = iw * vs, ih * vs
            ox, oy = (self.width() - w) / 2, (self.height() - h) / 2
            p.drawImage(QRectF(ox, oy, w, h), self.img)
            if self.overlay:
                p.setPen(QPen(QColor("#f6c445"), 2, Qt.DashLine))
                p.setBrush(Qt.NoBrush)
                p.drawPolygon(QPolygonF(
                    [QPointF(ox + px*vs, oy + py*vs) for px, py in self.overlay]))
        p.end()


class TimelineStrip(QWidget):
    jumped = Signal(int)
    edgeReleased = Signal(int, int)
    EDGE_PX = 5
    def __init__(self):
        super().__init__()
        self.segments = []; self.nframes = 0; self.frame = 0; self.fps = 30
        self.marks = {}
        self._drag_edge = None; self._preview = None
        self.setMinimumHeight(56)
        self.setMouseTracking(True)
    def set_data(self, segments, nframes, fps):
        self.segments, self.nframes, self.fps = segments, nframes, fps
        self._drag_edge = self._preview = None
        self.update()
    def set_marks(self, marks): self.marks = dict(marks); self.update()
    def set_frame(self, f): self.frame = f; self.update()
    def _x_for(self, f):
        return 6 + f / max(self.nframes, 1) * (self.width() - 12)
    def _f_for(self, x):
        return round((x - 6) / max(self.width() - 12, 1) * self.nframes)
    def _snap(self, f):
        sec = round(max(f, 0) / self.fps, 2)
        return round(sec * self.fps)
    def _edge_at(self, x):
        for i, seg in enumerate(self.segments):
            if abs(x - self._x_for(seg["end"])) <= self.EDGE_PX:
                return i
        return None
    def _bounds(self, i):
        seg = self.segments[i]
        lo = seg["start"] + 2
        if i + 1 < len(self.segments):
            hi = self.segments[i + 1]["end"] - 2
        else:
            hi = self.nframes + self.fps * 10
        return lo, max(hi, lo + 1)
    def mousePressEvent(self, e):
        if not self.nframes: return
        x = e.position().x()
        i = self._edge_at(x)
        if i is not None:
            self._drag_edge = i
            self._preview = (i, self.segments[i]["end"])
        else:
            f = max(0, min(self._f_for(x), self.nframes - 1))
            self.jumped.emit(f)
    def mouseMoveEvent(self, e):
        if not self.segments: return
        x = e.position().x()
        if self._drag_edge is not None:
            lo, hi = self._bounds(self._drag_edge)
            self._preview = (self._drag_edge,
                             max(lo, min(self._snap(self._f_for(x)), hi)))
            self.update()
            return
        i = self._edge_at(x)
        self.setCursor(Qt.SizeHorCursor if i is not None else Qt.ArrowCursor)
        f = self._f_for(x)
        for seg in self.segments:
            if seg["start"] <= f < seg["end"]:
                tip = f"frames {seg['start']+1}-{seg['end']}: {seg['src']}"
                if i is not None:
                    tip += "\n(drag right edge to retime)"
                self.setToolTip(tip)
                break
    def mouseReleaseEvent(self, e):
        if self._drag_edge is None: return
        i, f = self._preview
        self._drag_edge = None; self._preview = None
        self.update()
        self.edgeReleased.emit(i, f)
    def mouseDoubleClickEvent(self, e):
        if not self.nframes or not self.segments: return
        f = self._f_for(e.position().x())
        for seg in self.segments:
            if seg["start"] <= f < seg["end"]:
                self.jumped.emit(seg["start"])
                break
    def paintEvent(self, ev):
        p = QPainter(self)
        p.fillRect(self.rect(), QColor("#0a0a0e"))
        if self.nframes:
            p.setPen(QPen(QColor("#26262f"), 1))
            sec = self.fps
            while sec < self.nframes:
                x = self._x_for(sec)
                p.drawLine(QPointF(x, self.height() - 12), QPointF(x, self.height() - 4))
                p.setPen(QPen(QColor("#55556a"), 1))
                p.drawText(QPointF(x + 2, self.height() - 6), f"{sec // self.fps}s")
                p.setPen(QPen(QColor("#26262f"), 1))
                sec += self.fps
            for i, seg in enumerate(self.segments):
                s, e = seg["start"], seg["end"]
                if self._preview:
                    pi, pf = self._preview
                    if i == pi: e = pf
                    elif i == pi + 1: s = pf
                x0 = self._x_for(s)
                x1 = max(self._x_for(e), x0 + 2)
                p.fillRect(QRectF(x0, 8, x1 - x0, self.height() - 26),
                           QColor(SEGCOLORS[i % len(SEGCOLORS)]))
            p.setPen(Qt.NoPen)
            for bi, t in self.marks.items():
                if bi >= len(self.segments): continue
                x = self._x_for(self.segments[bi]["end"])
                p.setBrush(QBrush(QColor("#7c5cff")))
                p.drawPolygon(QPolygonF([QPointF(x, 14), QPointF(x + 6, 22),
                                         QPointF(x, 30), QPointF(x - 6, 22)]))
            x = self._x_for(self.frame)
            p.setPen(QPen(QColor("#f6c445"), 2))
            p.drawLine(QPointF(x, 2), QPointF(x, self.height() - 2))
            p.setBrush(QBrush(QColor("#f6c445"))); p.setPen(Qt.NoPen)
            p.drawPolygon(QPolygonF([QPointF(x - 5, 2), QPointF(x + 5, 2),
                                     QPointF(x, 10)]))
        else:
            p.setPen(QPen(QColor("#55556a"), 1))
            p.drawText(self.rect(), Qt.AlignCenter, "timeline (build preview)")
        p.end()


def _bx(t, x1, x2): return 3*(1-t)**2*t*x1 + 3*(1-t)*t*t*x2 + t**3
def _by(t, y1, y2): return 3*(1-t)**2*t*y1 + 3*(1-t)*t*t*y2 + t**3


class EasingCurve(QWidget):
    valsChanged = Signal()
    def __init__(self, vals):
        super().__init__()
        self.v = list(vals); self.drag = -1
        self.setMinimumSize(280, 280)
    def _m(self, x, y):
        m = 26
        return QPointF(m + x * (self.width() - 2*m),
                       self.height() - m - y * (self.height() - 2*m))
    def _um(self, px, py):
        m = 26
        return ((px - m) / max(self.width() - 2*m, 1),
                (self.height() - m - py) / max(self.height() - 2*m, 1))
    def mousePressEvent(self, e):
        self.drag = -1
        for i in (0, 1):
            if (self._m(self.v[2*i], self.v[2*i+1])
                    - e.position()).manhattanLength() < 16:
                self.drag = i; break
    def mouseMoveEvent(self, e):
        if self.drag < 0: return
        x, y = self._um(e.position().x(), e.position().y())
        self.v[2*self.drag] = clamp01(x)
        self.v[2*self.drag + 1] = max(-1.0, min(2.0, y))
        self.update(); self.valsChanged.emit()
    def mouseReleaseEvent(self, e): self.drag = -1
    def paintEvent(self, ev):
        p = QPainter(self); p.setRenderHint(QPainter.Antialiasing)
        m = 26; W, H = self.width(), self.height()
        p.fillRect(m, m, W - 2*m, H - 2*m, QColor("#15151f"))
        p.setPen(QPen(QColor("#3a3a4c"), 1))
        p.drawRect(m, m, W - 2*m, H - 2*m)
        x1, y1, x2, y2 = self.v
        p.setPen(QPen(QColor("#5a5a78"), 1, Qt.DashLine))
        p.drawLine(self._m(0, 0), self._m(x1, y1))
        p.drawLine(self._m(1, 1), self._m(x2, y2))
        path = QPainterPath(self._m(0, 0))
        for i in range(1, 101):
            x = i / 100
            lo, hi, t = 0.0, 1.0, x
            for _ in range(24):
                b = _bx(t, x1, x2)
                if abs(b - x) < 1e-5: break
                if b < x: lo = t
                else: hi = t
                t = (lo + hi) / 2
            path.lineTo(self._m(x, _by(t, y1, y2)))
        p.setPen(QPen(QColor("#4aa8ff"), 2)); p.setBrush(Qt.NoBrush)
        p.drawPath(path)
        p.setPen(Qt.NoPen)
        for i, col in ((0, "#f6c445"), (1, "#59d499")):
            p.setBrush(QBrush(QColor(col)))
            p.drawEllipse(self._m(self.v[2*i], self.v[2*i+1]), 6, 6)
        p.end()


def _open_chapters_dialog(parent, entries, fps, on_jump, title="Chapters"):
    dlg = QDialog(parent)
    dlg.setWindowTitle(title)
    dlg.resize(760, 480)
    table = QTableWidget(len(entries), 3)
    table.setHorizontalHeaderLabels(["#", "time", "segment / clip"])
    table.horizontalHeader().setSectionResizeMode(2, QHeaderView.Stretch)
    table.verticalHeader().setVisible(False)
    table.setEditTriggers(QTableWidget.NoEditTriggers)
    table.setSelectionBehavior(QTableWidget.SelectRows)
    def _fmt(sec):
        return f"{int(sec // 60)}:{sec % 60:04.1f}"
    for i, (s, e, txt) in enumerate(entries):
        table.setItem(i, 0, QTableWidgetItem(str(i + 1)))
        table.setItem(i, 1, QTableWidgetItem(f"{_fmt(s / fps)} - {_fmt(e / fps)}"))
        it = QTableWidgetItem(txt)
        it.setToolTip(txt)
        table.setItem(i, 2, it)
    def _jump(accept):
        r = table.currentRow()
        if 0 <= r < len(entries):
            on_jump(int(entries[r][0]))
            if accept: dlg.accept()
    table.itemClicked.connect(lambda *_: _jump(False))
    table.itemDoubleClicked.connect(lambda *_: _jump(True))
    def _srt():
        path, _f = QFileDialog.getSaveFileName(
            dlg, "Export chapters SRT", "chapters.srt", "SubRip (*.srt)")
        if path:
            write_srt(path, [(s / fps, e / fps, txt) for s, e, txt in entries])
    srt_btn = QPushButton("Export SRT…"); srt_btn.clicked.connect(_srt)
    close = QPushButton("Close"); close.clicked.connect(dlg.reject)
    row = QHBoxLayout()
    row.addWidget(srt_btn); row.addStretch(1); row.addWidget(close)
    v = QVBoxLayout(dlg)
    v.addWidget(table, 1)
    v.addLayout(row)
    dlg.show()
    return dlg

# ---------------------------------------------------------------- scene GUI
def _launch_scene_gui(scene_cls, scene_path=None):
    class RecordWorker(QThread):
        tick = Signal(int); done = Signal(bool, object, str)
        def __init__(self, base_cls, spath, q):
            super().__init__(); self.base_cls, self.spath, self.q = base_cls, spath, q
        def run(self):
            try:
                cls = load_scene_cls(self.spath) if self.spath else self.base_cls
                w, h, fps, crf = QUAL[self.q]
                sc = cls(width=w, height=h, fps=fps)
                snaps = sc.record_preview(progress=self.tick.emit)
                segs = [dict(s) for s in sc.segment_log]
                self.done.emit(True, (sc, snaps, fps, segs), "")
            except Exception as e:
                import traceback; traceback.print_exc()
                self.done.emit(False, None, f"{type(e).__name__}: {e}")

    class ExportWorker(QThread):
        tick = Signal(int); done = Signal(bool, str)
        def __init__(self, base_cls, spath, q, out):
            super().__init__()
            self.base_cls, self.spath, self.q, self.out = base_cls, spath, q, out
        def run(self):
            try:
                cls = load_scene_cls(self.spath) if self.spath else self.base_cls
                w, h, fps, crf = QUAL[self.q]
                sc = cls(width=w, height=h, fps=fps)
                sc.progress_fn = self.tick.emit
                sc.render(self.out, crf=crf)
                self.done.emit(True, self.out)
            except Exception as e:
                import traceback; traceback.print_exc()
                self.done.emit(False, f"{type(e).__name__}: {e}")

    class Win(QMainWindow):
        def __init__(self):
            super().__init__()
            self.setWindowTitle("svglab — preview")
            self.resize(1180, 730)
            self.scene = self.snaps = None
            self.fps, self.frame, self.playing = 30, 0, False
            self.worker, self.sel_gid = None, None
            self._dragging = False
            self._chap_dlg = None
            self.scene_path = scene_path

            self.canvas = Canvas(); self.canvas.drag_cb = self._drag
            self.strip = TimelineStrip()
            self.strip.jumped.connect(self._set_frame)
            self.strip.edgeReleased.connect(self._edge_released)
            self.slider = QSlider(Qt.Horizontal); self.slider.setEnabled(False)
            self.slider.setRange(0, 0); self.slider.setFocusPolicy(Qt.NoFocus)
            self.slider.sliderMoved.connect(self._scrub)
            self.lbl = QLabel("no preview")
            self.play_btn = QPushButton("▶"); self.play_btn.setEnabled(False)
            self.play_btn.setFocusPolicy(Qt.NoFocus)
            self.play_btn.clicked.connect(self._toggle)
            self.b0 = QPushButton("⏮"); self.b0.setFocusPolicy(Qt.NoFocus)
            self.bp = QPushButton("◀"); self.bp.setFocusPolicy(Qt.NoFocus)
            self.bn = QPushButton("▶|"); self.bn.setFocusPolicy(Qt.NoFocus)
            self.b0.clicked.connect(lambda: self._set_frame(0))
            self.bp.clicked.connect(lambda: self._set_frame(self.frame-1))
            self.bn.clicked.connect(lambda: self._set_frame(self.frame+1))
            for b in (self.b0, self.bp, self.bn): b.setEnabled(False)
            self.combo = QComboBox(); self.combo.addItems(list(QUAL))
            self.combo.setCurrentText("720p30")
            self.fmt = QComboBox(); self.fmt.addItems(list(FMT_EXT) + ["PNG sequence"])
            self.build_btn = QPushButton("Build preview")
            self.export_btn = QPushButton("Export…")
            self.snap_btn = QPushButton("Save frame"); self.snap_btn.setEnabled(False)
            self.chap_btn = QPushButton("Chapters…"); self.chap_btn.setEnabled(False)
            self.ex_btn = QPushButton("Examples…")
            self.build_btn.clicked.connect(self.build)
            self.export_btn.clicked.connect(self.export)
            self.snap_btn.clicked.connect(self.save_frame)
            self.chap_btn.clicked.connect(self._open_chapters)
            self.ex_btn.clicked.connect(lambda: open_example_gallery(self))
            self.status = QLabel("idle — Build preview, click selects, drag moves")

            self.info_name = QLabel("nothing selected")
            self.info_vals = QLabel("click an object in the preview")
            self.info_sel = QLabel("—"); self.info_sel.setWordWrap(True)
            self.info_sel.setTextInteractionFlags(Qt.TextSelectableByMouse)
            self.copy_btn = QPushButton("Copy selector")
            self.copy_btn.setEnabled(False); self.copy_btn.clicked.connect(self._copy_sel)
            self.seg_lbl = QLabel("segment: —")
            self.seg_lbl.setWordWrap(True)
            self.seg_lbl.setTextInteractionFlags(Qt.TextSelectableByMouse)
            self.snip_lbl = QLabel("drag the selection to generate a move_to() line")
            self.snip_lbl.setWordWrap(True)
            self.snip_lbl.setTextInteractionFlags(Qt.TextSelectableByMouse)
            self.snip_lbl.setStyleSheet("font-family: monospace;")
            self.snip_ctx = QLabel("")
            self.snip_copy = QPushButton("Copy code line")
            self.snip_copy.setEnabled(False)
            self.snip_copy.clicked.connect(self._copy_snip)
            self.patch_btn = QPushButton("Patch into file")
            self.patch_btn.setEnabled(False)
            self.patch_btn.clicked.connect(self._patch_move)
            self.ease_btn = QPushButton("Easing editor…")
            self.ease_btn.clicked.connect(self._easing_dialog)

            left = QVBoxLayout()
            left.addWidget(self.canvas, 1)
            left.addWidget(self.strip)
            row = QHBoxLayout()
            row.addWidget(self.b0); row.addWidget(self.bp)
            row.addWidget(self.play_btn); row.addWidget(self.bn)
            row.addWidget(self.slider, 1); row.addWidget(self.lbl)
            left.addLayout(row)
            right = QVBoxLayout()
            right.addWidget(QLabel("<b>Inspector</b>"))
            right.addWidget(self.info_name)
            right.addWidget(self.info_vals)
            right.addWidget(QLabel("selector:"))
            right.addWidget(self.info_sel)
            right.addWidget(self.copy_btn)
            right.addWidget(QLabel("segment:"))
            right.addWidget(self.seg_lbl)
            right.addWidget(QLabel("code:"))
            right.addWidget(self.snip_lbl)
            right.addWidget(self.snip_ctx)
            right.addWidget(self.snip_copy)
            right.addWidget(self.patch_btn)
            right.addStretch(1)
            right.addWidget(self.ease_btn)
            body = QHBoxLayout(); body.addLayout(left, 1); body.addLayout(right)

            v = QVBoxLayout(); v.addLayout(body)
            row2 = QHBoxLayout()
            row2.addWidget(QLabel("Quality:")); row2.addWidget(self.combo)
            row2.addWidget(QLabel("Format:")); row2.addWidget(self.fmt)
            row2.addWidget(self.build_btn); row2.addWidget(self.export_btn)
            row2.addWidget(self.snap_btn); row2.addWidget(self.chap_btn)
            row2.addWidget(self.ex_btn)
            row2.addWidget(self.status, 1)
            v.addLayout(row2)
            central = QWidget(); central.setLayout(v)
            self.setCentralWidget(central)

            self.timer = QTimer(); self.timer.timeout.connect(self._advance)
            QShortcut(QKeySequence(Qt.Key_Space), self, self._toggle)
            QShortcut(QKeySequence(Qt.Key_Left), self,
                      lambda: self._set_frame(self.frame - 1))
            QShortcut(QKeySequence(Qt.Key_Right), self,
                      lambda: self._set_frame(self.frame + 1))
            QShortcut(QKeySequence(Qt.Key_Escape), self, self._deselect)

        # -- dragging / inspector -----------------------------------------
        def _drag(self, ix, iy, phase):
            if not self.scene or self.playing: return
            if phase == "start":
                o = self.scene.hit_test(*self.scene.img_to_stage(ix, iy))
                gid = getattr(o, "_gid", None)
                if gid != self.sel_gid:
                    self.sel_gid = gid
                    self._dragging = False
                    self.snip_lbl.setText(
                        "drag the selection to generate a move_to() line")
                    self.snip_ctx.setText(""); self.snip_copy.setEnabled(False)
                    self.patch_btn.setEnabled(False)
                    self._refresh_info()
                else:
                    self._dragging = gid is not None
            elif phase == "move" and self._dragging:
                o = self._find_by_gid(self.sel_gid)
                if o is None: return
                o.x, o.y = self.scene.img_to_local(o, ix, iy)
                self.canvas.set_image(self.scene._render_image(use_cache=True))
                self._refresh_info()
            elif phase == "end" and self._dragging:
                self._dragging = False
                self._update_snippet()

        @staticmethod
        def _selector_of(o):
            el = getattr(o, "elem", None)
            if el is None: return None
            i = el.get("id")
            if i: return f"svg.select('#{i}')"
            cl = (el.get("class") or "").split()
            if cl: return f"svg.select('.{cl[0]}')"
            return f"svg.select('{etree.QName(el).localname}')"

        def _update_snippet(self):
            o = self._find_by_gid(self.sel_gid)
            if o is None: return
            sel = self._selector_of(o)
            if sel:
                line = f"{sel}[0].move_to({o.x:.1f}, {o.y:.1f})"
            else:
                line = f"<your-var>.move_to({o.x:.1f}, {o.y:.1f})"
            grouped = bool(self.scene._ancestors_of(o))
            if grouped:
                line += "   # group-local coords"
            self.snip_lbl.setText(line)
            for i, seg in enumerate(self.scene.segment_log):
                if seg["start"] <= self.frame < seg["end"]:
                    self.snip_ctx.setText(
                        f"@ frame {self.frame+1}, segment {i+1}"
                        f"/{len(self.scene.segment_log)}")
                    break
            self.snip_copy.setEnabled(True)
            self.patch_btn.setEnabled(
                bool(self.scene_path) and sel is not None and not grouped)

        def _copy_snip(self):
            QApplication.clipboard().setText(self.snip_lbl.text())

        def _patch_move(self):
            o = self._find_by_gid(self.sel_gid)
            if not (o and self.scene_path): return
            sel = self._selector_of(o)
            if not sel:
                self.status.setText("no selector for this object"); return
            if not (sel.startswith("svg.select('#") or sel.startswith("svg.select('.'")):
                self.status.setText("tag selector matches many elements — "
                                    "give it an id/class in the SVG first"); return
            seg = next((s for s in self.scene.segment_log
                        if s["start"] <= self.frame < s["end"]), None)
            try:
                res = SourcePatcher(self.scene_path).patch_move(
                    sel, o.x, o.y, seg["line"] if seg else 1)
                self.status.setText(f"{res} {sel}[0].move_to(...) — "
                                    f"Build preview to apply")
            except Exception as e:
                self.status.setText(f"patch failed: {e}")

        def _edge_released(self, i, new_end):
            if not self.scene_path:
                self.status.setText("no scene file — cannot retime"); return
            if self.worker and self.worker.isRunning(): return
            seg = self.scene.segment_log[i]
            try:
                msg = SourcePatcher(self.scene_path).patch_duration(
                    seg, new_end - seg["start"], self.fps)
            except Exception as e:
                self.status.setText(f"retime patch failed: {e}"); return
            seg["end"] = new_end
            if i + 1 < len(self.scene.segment_log):
                self.scene.segment_log[i + 1]["start"] = new_end
            self.strip.set_data(self.scene.segment_log, len(self.snaps), self.fps)
            self.status.setText(f"segment {i+1}: {msg} — Build preview to apply")

        def _deselect(self):
            self.sel_gid = None
            self.snip_lbl.setText("drag the selection to generate a move_to() line")
            self.snip_ctx.setText(""); self.snip_copy.setEnabled(False)
            self.patch_btn.setEnabled(False)
            self._refresh_info()

        def _find_by_gid(self, gid):
            if not (self.scene and gid is not None): return None
            def walk(objs):
                for o in objs:
                    if getattr(o, "_gid", None) == gid: return o
                    if isinstance(o, Group):
                        r = walk(o.members)
                        if r is not None: return r
                return None
            return walk(self.scene.objects)

        def _refresh_info(self):
            o = self._find_by_gid(self.sel_gid)
            self.canvas.set_overlay(self.scene.obj_corners(o) if o else None)
            if o is None:
                self.info_name.setText("nothing selected")
                self.info_vals.setText("click an object in the preview")
                self.info_sel.setText("—")
                self.copy_btn.setEnabled(False)
                return
            self.copy_btn.setEnabled(True)
            self.info_name.setText(f"<b>{type(o).__name__}</b>")
            self.info_vals.setText(
                f"x {o.x:.1f}   y {o.y:.1f}\n"
                f"scale {o.scale:.2f}   rot {o.rotation:.1f}\N{DEGREE SIGN}\n"
                f"opacity {o.opacity:.2f}")
            self.info_sel.setText(self._selector_of(o) or "(generated in code)")

        def _copy_sel(self):
            QApplication.clipboard().setText(self.info_sel.text())

        def _easing_dialog(self):
            dlg = QDialog(self)
            dlg.setWindowTitle("Easing curve editor")
            ed = EasingCurve(EASING_PRESETS["ease (in-out)"])
            combo = QComboBox(); combo.addItems(list(EASING_PRESETS))
            lbl = QLabel(); lbl.setTextInteractionFlags(Qt.TextSelectableByMouse)
            def sync():
                x1, y1, x2, y2 = ed.v
                lbl.setText(f"cubic_bezier({x1:.3f}, {y1:.3f}, {x2:.3f}, {y2:.3f})")
            def pick(name):
                ed.v = list(EASING_PRESETS[name]); ed.update(); sync()
            ed.valsChanged.connect(sync)
            combo.currentTextChanged.connect(pick)
            cp = QPushButton("Copy")
            cp.clicked.connect(lambda: QApplication.clipboard().setText(lbl.text()))
            v = QVBoxLayout(dlg)
            v.addWidget(ed); v.addWidget(combo); v.addWidget(lbl); v.addWidget(cp)
            sync(); dlg.show()

        # -- chapters -------------------------------------------------------
        def _chapters(self):
            return [(s["start"], s["end"], s["src"])
                    for s in self.scene.segment_log]

        def _open_chapters(self):
            if not (self.scene and self.scene.segment_log):
                self.status.setText("no chapters recorded — Build preview first")
                return
            self._chap_dlg = _open_chapters_dialog(
                self, self._chapters(), self.fps, self._set_frame,
                "Chapters — click a row to jump")

        # -- preview ----------------------------------------------------------
        def build(self):
            if self.worker and self.worker.isRunning(): return
            self._busy(True); self.status.setText("recording preview…")
            self.worker = RecordWorker(scene_cls, self.scene_path,
                                       self.combo.currentText())
            self.worker.tick.connect(
                lambda n: self.status.setText(f"recording… frame {n}"))
            self.worker.done.connect(self._built)
            self.worker.start()

        def _built(self, ok, payload, err):
            self._busy(False)
            if not ok:
                self.status.setText(err); return
            self.scene, self.snaps, self.fps, segs = payload
            self.scene.segment_log = segs
            self.slider.setRange(0, len(self.snaps) - 1)
            self.slider.setEnabled(True)
            for b in (self.play_btn, self.b0, self.bp, self.bn,
                      self.snap_btn, self.chap_btn):
                b.setEnabled(True)
            self.strip.set_data(segs, len(self.snaps), self.fps)
            self.status.setText(f"{len(self.snaps)} frames — Space plays, "
                                f"drag scrubs, click inspects")
            self.sel_gid = None
            self._set_frame(0)

        def _set_frame(self, i):
            if not self.snaps:
                return
            self.frame = max(0, min(i, len(self.snaps) - 1))
            self.slider.blockSignals(True)
            self.slider.setValue(self.frame)
            self.slider.blockSignals(False)
            self.strip.set_frame(self.frame)
            self.lbl.setText(f"{self.frame+1}/{len(self.snaps)}  "
                             f"({self.frame/self.fps:.2f}s)")
            self.canvas.set_image(self.scene.paint_snapshot(self.snaps[self.frame]))
            self._refresh_info()
            seg = next((f"{k+1}: {txt}" for k, (a, e, txt)
                        in enumerate(self._chapters())
                        if a <= self.frame < e), None)
            self.seg_lbl.setText(seg or "—")

        def _scrub(self, v):
            if not self.playing: self._set_frame(v)

        def _toggle(self):
            if not self.snaps: return
            self.playing = not self.playing
            self.play_btn.setText("⏸" if self.playing else "▶")
            if self.playing:
                self._dragging = False
                if self.frame + 1 >= len(self.snaps): self._set_frame(0)
                self.timer.start(int(1000 / self.fps))
            else:
                self.timer.stop()

        def _advance(self):
            if self.frame + 1 >= len(self.snaps): self._toggle()
            else: self._set_frame(self.frame + 1)

        def save_frame(self):
            if not (self.snaps and self.scene): return
            path, _ = QFileDialog.getSaveFileName(
                self, "Save frame", f"frame_{self.frame:05d}.png", "PNG (*.png)")
            if path:
                self.scene.paint_snapshot(self.snaps[self.frame]).save(path)
                self.status.setText(f"saved -> {path}")

        def export(self):
            if self.worker and self.worker.isRunning(): return
            fmt = self.fmt.currentText()
            if fmt == "PNG sequence":
                d = QFileDialog.getExistingDirectory(self, "PNG sequence folder")
                if not d: return
                out = d
            else:
                ext = FMT_EXT[fmt]
                path, _ = QFileDialog.getSaveFileName(
                    self, "Export", "video" + ext, f"{fmt} (*{ext})")
                if not path: return
                out = path
            self._busy(True); self.status.setText("exporting…")
            self.worker = ExportWorker(scene_cls, self.scene_path,
                                       self.combo.currentText(), out)
            self.worker.tick.connect(
                lambda n: self.status.setText(f"exporting… frame {n}"))
            self.worker.done.connect(self._exported)
            self.worker.start()

        def _exported(self, ok, info):
            self._busy(False)
            self.status.setText(f"exported -> {info}" if ok else info)

        def _busy(self, on):
            for b in (self.build_btn, self.export_btn, self.combo,
                      self.fmt, self.snap_btn, self.chap_btn):
                b.setEnabled(not on)

    win = Win(); win.show()
    return win

# ---------------------------------------------------------------- clips GUI
def _launch_clip_gui(project_cls, project_path):
    class BuildWorker(QThread):
        tick = Signal(int, str); done = Signal(bool, str)
        def __init__(self, proj_cls, spath, q):
            super().__init__()
            self.proj_cls, self.spath, self.q = proj_cls, spath, q
            self.studio = None
        def run(self):
            try:
                cls = load_project(self.spath)[0] if self.spath else self.proj_cls
                w, h, fps, crf = QUAL[self.q]
                studio = ClipStudio(cls(), width=w, height=h, fps=fps, crf=crf)
                self.studio = studio
                names = studio.names()
                for i, n in enumerate(names):
                    key = studio.ensure_spec(n)
                    def prog(cnt, _k=key, _i=i):
                        self.tick.emit(cnt, f"clip {_i+1}/{len(names)}: {_k}")
                    studio.build_clip(key, prog)
                    self.tick.emit(0, f"done: {key}")
                self.done.emit(True, "")
            except Exception as e:
                import traceback; traceback.print_exc()
                self.done.emit(False, f"{type(e).__name__}: {e}")

    class AssembleWorker(QThread):
        done = Signal(bool, str)
        def __init__(self, studio, order, out, transitions):
            super().__init__()
            self.studio, self.order = studio, order
            self.out, self.transitions = out, transitions
        def run(self):
            try:
                self.studio.assemble(self.order, self.out, self.transitions)
                self.done.emit(True, self.out)
            except Exception as e:
                self.done.emit(False, f"{type(e).__name__}: {e}")

    class VariantDialog(QDialog):
        def __init__(self, studio, parent=None, name=None, args=None):
            super().__init__(parent)
            self.setWindowTitle("Clip variant")
            self.studio = studio
            self.combo = QComboBox(); self.combo.addItems(studio.names())
            if name: self.combo.setCurrentText(name)
            self.form = QFormLayout()
            self.edits = {}
            outer = QVBoxLayout(self)
            outer.addWidget(QLabel("Clip:")); outer.addWidget(self.combo)
            outer.addLayout(self.form)
            btns = QHBoxLayout()
            ok = QPushButton("OK"); ca = QPushButton("Cancel")
            ok.clicked.connect(self.accept); ca.clicked.connect(self.reject)
            btns.addStretch(1); btns.addWidget(ca); btns.addWidget(ok)
            outer.addLayout(btns)
            self.combo.currentTextChanged.connect(lambda _: self._fields(None))
            self._fields(args)
            self.resize(360, 200)

        def _fields(self, args):
            while self.form.rowCount(): self.form.removeRow(0)
            self.edits = {}
            for p, dflt in self.studio.params(self.combo.currentText()):
                e = QLineEdit(repr(dflt) if dflt is not inspect.Parameter.empty
                              else (repr(args.get(p)) if args and p in args else ""))
                self.form.addRow(p, e)
                self.edits[p] = e

        def values(self):
            name = self.combo.currentText()
            args = {}
            for p, e in self.edits.items():
                raw = e.text().strip()
                if raw == "": continue
                try: args[p] = ast.literal_eval(raw)
                except (ValueError, SyntaxError): args[p] = raw
            return name, args

    class TransitionsDialog(QDialog):
        def __init__(self, blocks, current, parent=None):
            super().__init__(parent)
            self.setWindowTitle("Transitions between clips")
            self.blocks, self.current = blocks, dict(current)
            v = QVBoxLayout(self)
            self.table = QTableWidget(max(len(blocks) - 1, 0), 3)
            self.table.setHorizontalHeaderLabels(["between", "type", "duration (s)"])
            self.table.horizontalHeader().setStretchLastSection(True)
            self.table.verticalHeader().setVisible(False)
            for j in range(len(blocks) - 1):
                lkey, rkey = blocks[j][0], blocks[j + 1][0]
                self.table.setItem(j, 0, QTableWidgetItem(f"{lkey} \N{LEFT RIGHT DOUBLE ARROW} {rkey}"))
                combo = QComboBox(); combo.addItems(["cut"] + XFADE_TYPES)
                typ, dur = self.current.get((lkey, rkey), ("cut", 1.0))
                combo.setCurrentText(typ if typ in XFADE_TYPES else "cut")
                self.table.setCellWidget(j, 1, combo)
                spin = QDoubleSpinBox(); spin.setRange(0.25, 5.0)
                spin.setSingleStep(0.25); spin.setValue(dur)
                spin.setEnabled(combo.currentText() != "cut")
                combo.currentTextChanged.connect(
                    lambda t, s=spin: s.setEnabled(t != "cut"))
                self.table.setCellWidget(j, 2, spin)
            self.table.setColumnWidth(0, 260)
            v.addWidget(self.table)
            row = QHBoxLayout()
            ok = QPushButton("Apply"); ca = QPushButton("Cancel")
            ok.clicked.connect(self.accept); ca.clicked.connect(self.reject)
            row.addStretch(1); row.addWidget(ca); row.addWidget(ok)
            v.addLayout(row)

        def result_map(self):
            out = {}
            for j in range(len(self.blocks) - 1):
                lkey, rkey = self.blocks[j][0], self.blocks[j + 1][0]
                combo = self.table.cellWidget(j, 1)
                spin = self.table.cellWidget(j, 2)
                t = combo.currentText()
                if t != "cut":
                    out[(lkey, rkey)] = (t, float(spin.value()))
            return out

    class Win(QMainWindow):
        def __init__(self):
            super().__init__()
            self.setWindowTitle("svglab — clips")
            self.resize(1240, 730)
            self.studio = None
            self.fps, self.frame, self.playing = 30, 0, False
            self.worker = None
            self.transitions = {}
            self.timeline, self.total = [], 0
            self._chap_dlg = None

            self.canvas = Canvas()
            self.strip = TimelineStrip()
            self.strip.jumped.connect(self._set_frame)
            self.slider = QSlider(Qt.Horizontal); self.slider.setEnabled(False)
            self.slider.setRange(0, 0); self.slider.setFocusPolicy(Qt.NoFocus)
            self.slider.sliderMoved.connect(self._scrub)
            self.lbl = QLabel("no clips")
            self.play_btn = QPushButton("▶"); self.play_btn.setEnabled(False)
            self.play_btn.setFocusPolicy(Qt.NoFocus)
            self.play_btn.clicked.connect(self._toggle)
            self.b0 = QPushButton("⏮"); self.b0.setFocusPolicy(Qt.NoFocus)
            self.bp = QPushButton("◀"); self.bp.setFocusPolicy(Qt.NoFocus)
            self.bn = QPushButton("▶|"); self.bn.setFocusPolicy(Qt.NoFocus)
            self.b0.clicked.connect(lambda: self._set_frame(0))
            self.bp.clicked.connect(lambda: self._set_frame(self.frame - 1))
            self.bn.clicked.connect(lambda: self._set_frame(self.frame + 1))
            for b in (self.b0, self.bp, self.bn): b.setEnabled(False)
            self.combo = QComboBox(); self.combo.addItems(list(QUAL))
            self.combo.setCurrentText("720p30")
            self.build_btn = QPushButton("Build clips")
            self.render_btn = QPushButton("Render MP4…")
            self.chap_btn = QPushButton("Chapters…"); self.chap_btn.setEnabled(False)
            self.ex_btn = QPushButton("Examples…")
            self.build_btn.clicked.connect(self.build)
            self.render_btn.clicked.connect(self.render_mp4)
            self.chap_btn.clicked.connect(self._open_chapters)
            self.ex_btn.clicked.connect(lambda: open_example_gallery(self))

            self.list = QListWidget()
            self.list.setDragDropMode(QListWidget.InternalMove)
            self.list.itemChanged.connect(lambda *_: self._sync())
            self.list.model().rowsMoved.connect(lambda *_: self._sync())
            self.list.itemDoubleClicked.connect(self._edit_variant)
            self.add_btn = QPushButton("Add clip")
            self.var_btn = QPushButton("Add variant…")
            self.tr_btn = QPushButton("Transitions…")
            self.dup_btn = QPushButton("Duplicate")
            self.del_btn = QPushButton("Remove")
            self.add_btn.clicked.connect(self._add_clip)
            self.var_btn.clicked.connect(self._add_variant)
            self.tr_btn.clicked.connect(self._edit_transitions)
            self.dup_btn.clicked.connect(self._dup)
            self.del_btn.clicked.connect(self._del_item)
            for b in (self.add_btn, self.var_btn, self.tr_btn,
                      self.dup_btn, self.del_btn): b.setEnabled(False)
            self.seg_lbl = QLabel("segment: —")
            self.seg_lbl.setWordWrap(True)
            self.status = QLabel("idle — Build clips, drag to arrange, Render")

            left = QVBoxLayout()
            left.addWidget(self.canvas, 1)
            left.addWidget(self.strip)
            row = QHBoxLayout()
            row.addWidget(self.b0); row.addWidget(self.bp)
            row.addWidget(self.play_btn); row.addWidget(self.bn)
            row.addWidget(self.slider, 1); row.addWidget(self.lbl)
            left.addLayout(row)
            left.addWidget(self.seg_lbl)
            right = QVBoxLayout()
            right.addWidget(QLabel("<b>Playlist</b> — drag to reorder, "
                                   "check to include, double-click to edit args"))
            right.addWidget(self.list, 1)
            r1 = QHBoxLayout(); r1.addWidget(self.add_btn); r1.addWidget(self.var_btn)
            r2 = QHBoxLayout(); r2.addWidget(self.dup_btn); r2.addWidget(self.del_btn)
            r3 = QHBoxLayout(); r3.addWidget(self.tr_btn)
            right.addLayout(r1); right.addLayout(r2); right.addLayout(r3)
            body = QHBoxLayout(); body.addLayout(left, 1); body.addLayout(right)

            v = QVBoxLayout(); v.addLayout(body)
            row2 = QHBoxLayout()
            row2.addWidget(QLabel("Quality:")); row2.addWidget(self.combo)
            row2.addWidget(self.build_btn); row2.addWidget(self.render_btn)
            row2.addWidget(self.chap_btn); row2.addWidget(self.ex_btn)
            row2.addWidget(self.status, 1)
            v.addLayout(row2)
            central = QWidget(); central.setLayout(v)
            self.setCentralWidget(central)

            self.timer = QTimer(); self.timer.timeout.connect(self._advance)
            QShortcut(QKeySequence(Qt.Key_Space), self, self._toggle)
            QShortcut(QKeySequence(Qt.Key_Left), self,
                      lambda: self._set_frame(self.frame - 1))
            QShortcut(QKeySequence(Qt.Key_Right), self,
                      lambda: self._set_frame(self.frame + 1))

        # -- playlist model ---------------------------------------------------
        @staticmethod
        def _disp(name, args):
            if not args: return name
            tail = ", ".join(f"{k}={v!r}" for k, v in sorted(args.items()))
            return f"{name} · {tail}" if len(tail) <= 48 else f"{name} · {tail[:45]}…"

        def _add_item(self, name, args, check=True):
            key = self.studio.ensure_spec(name, args)
            c = self.studio.built.get(key)
            it = QListWidgetItem(self._disp(name, args))
            if c:
                img = c["scene"].paint_snapshot(c["snaps"][0], use_cache=True)
                it.setIcon(QIcon(QPixmap.fromImage(img).scaled(
                    96, 54, Qt.KeepAspectRatio, Qt.SmoothTransformation)))
                it.setText(f"{self._disp(name, args)}  ({c['frames']/self.fps:.2f}s)")
            it.setData(Qt.UserRole, key)
            it.setFlags(it.flags() | Qt.ItemIsUserCheckable | Qt.ItemIsDragEnabled)
            it.setCheckState(Qt.Checked if check else Qt.Unchecked)
            self.list.addItem(it)
            return key

        def _order(self):
            out = []
            for row in range(self.list.count()):
                it = self.list.item(row)
                if it.checkState() == Qt.Checked:
                    out.append(it.data(Qt.UserRole))
            return out

        def _timeline(self):
            order = [k for k in self._order() if k in self.studio.built]
            tl, pos, prev_d = [], 0, 0
            for i, key in enumerate(order):
                F = self.studio.built[key]["frames"]
                nxt = order[i + 1] if i + 1 < len(order) else None
                d, typ = 0, None
                if nxt:
                    tr = self.transitions.get((key, nxt))
                    if tr:
                        d = max(2, round(tr[1] * self.fps))
                        d = min(d, F, self.studio.built[nxt]["frames"])
                        if d < 2:
                            d, typ = 0, None
                tl.append(dict(key=key, pos=pos, F=F, consumed=prev_d,
                               span=F - prev_d, d_next=d, ttype=typ))
                pos += F - prev_d
                prev_d = d
            return tl, pos

        def _blocks(self):
            tl, _ = self._timeline()
            return [(b["key"], b["pos"], b["pos"] + b["span"]) for b in tl]

        def _sync(self):
            if not self.studio: return
            tl, total = self._timeline()
            self.timeline, self.total = tl, total
            self.slider.blockSignals(True)
            self.slider.setRange(0, max(total - 1, 0))
            self.slider.blockSignals(False)
            self.strip.set_data([{"start": b["pos"], "end": b["pos"] + b["span"],
                                  "src": b["key"]} for b in tl], total, self.fps)
            self.strip.set_marks({j: b["ttype"] for j, b in enumerate(tl[:-1])
                                  if b["ttype"]})
            self._set_frame(min(self.frame, max(total - 1, 0)))

        def _add_clip(self):
            if not self.studio: return
            names = self.studio.names()
            if len(names) == 1:
                name, args = names[0], {}
            else:
                dlg = VariantDialog(self.studio, self)
                if dlg.exec() != QDialog.Accepted: return
                name, args = dlg.values()
                if args:
                    try: self._add_item(name, args)
                    except Exception as e:
                        QMessageBox.warning(self, "Variant", str(e)); return
                    self._sync(); return
            self._add_item(name, args)
            self._sync()

        def _add_variant(self):
            if not self.studio: return
            dlg = VariantDialog(self.studio, self)
            if dlg.exec() != QDialog.Accepted: return
            name, args = dlg.values()
            try:
                self._add_item(name, args)
            except Exception as e:
                QMessageBox.warning(self, "Variant", str(e)); return
            self._sync()

        def _edit_variant(self, it):
            if not self.studio: return
            key = it.data(Qt.UserRole)
            name, args = self.studio.specs[key][0], self.studio.specs[key][1]
            if not self.studio.params(name):
                return
            dlg = VariantDialog(self.studio, self, name=name, args=args)
            if dlg.exec() != QDialog.Accepted: return
            nname, nargs = dlg.values()
            try:
                nkey = self.studio.ensure_spec(nname, nargs)
            except Exception as e:
                QMessageBox.warning(self, "Variant", str(e)); return
            row = self.list.row(it)
            nit = QListWidgetItem(self._disp(nname, nargs))
            c = self.studio.built.get(nkey)
            if c:
                img = c["scene"].paint_snapshot(c["snaps"][0], use_cache=True)
                nit.setIcon(QIcon(QPixmap.fromImage(img).scaled(
                    96, 54, Qt.KeepAspectRatio, Qt.SmoothTransformation)))
                nit.setText(f"{self._disp(nname, nargs)}  ({c['frames']/self.fps:.2f}s)")
            nit.setData(Qt.UserRole, nkey)
            nit.setFlags(it.flags()); nit.setCheckState(it.checkState())
            self.list.insertItem(row, nit)
            self.list.takeItem(row + 1)
            self._sync()

        def _dup(self):
            it = self.list.currentItem()
            if it is None: return
            key = it.data(Qt.UserRole)
            name, args = self.studio.specs[key][0], self.studio.specs[key][1]
            self._add_item(name, args, check=(it.checkState() == Qt.Checked))
            self._sync()

        def _del_item(self):
            row = self.list.currentRow()
            if row >= 0:
                self.list.takeItem(row)
                self._sync()

        def _edit_transitions(self):
            blocks = self._blocks()
            if len(blocks) < 2:
                self.status.setText("need >=2 included clips for transitions")
                return
            dlg = TransitionsDialog(blocks, self.transitions, self)
            if dlg.exec() != QDialog.Accepted: return
            self.transitions = dlg.result_map()
            self._sync()
            self.status.setText(f"{len(self.transitions)} transition(s) set — "
                                f"Render MP4 to assemble")

        # -- chapters -----------------------------------------------------------
        def _chapters(self):
            out = []
            for b in self.timeline:
                for seg in self.studio.built[b["key"]]["log"]:
                    a0 = b["pos"] + max(seg["start"] - b["consumed"], 0)
                    a1 = b["pos"] + min(seg["end"] - b["consumed"], b["span"])
                    if a1 > a0:
                        out.append((a0, a1, f"[{b['key']}] {seg['src']}"))
            return out

        def _open_chapters(self):
            ch = self._chapters()
            if not ch:
                self.status.setText("no chapters — Build clips first")
                return
            self._chap_dlg = _open_chapters_dialog(
                self, ch, self.fps, self._set_frame,
                "Chapters — click a row to jump")

        # -- build / preview -------------------------------------------------------
        def build(self):
            if self.worker and self.worker.isRunning(): return
            self._busy(True); self.status.setText("building clips…")
            self.worker = BuildWorker(project_cls, project_path,
                                      self.combo.currentText())
            self.worker.tick.connect(
                lambda c, s: self.status.setText(f"building… {s} (frame {c})"))
            self.worker.done.connect(self._built)
            self.worker.start()

        def _built(self, ok, err):
            self._busy(False)
            if not ok:
                self.status.setText(err); return
            self.studio = self.worker.studio
            self.fps = self.studio.fps
            self.list.blockSignals(True)
            self.list.clear()
            for n in self.studio.names():
                self._add_item(n, {})
            self.list.blockSignals(False)
            for b in (self.play_btn, self.b0, self.bp, self.bn, self.add_btn,
                      self.var_btn, self.tr_btn, self.dup_btn, self.del_btn,
                      self.chap_btn):
                b.setEnabled(True)
            self.status.setText(f"{len(self.studio.built)} clip render(s) — drag to "
                                f"arrange, Add variant for parameterized instances")
            self.frame = 0
            self._sync()

        def _set_frame(self, i):
            if not self.studio or not self.timeline:
                self.canvas.set_image(None)
                self.lbl.setText("empty playlist")
                return
            i = max(0, min(i, self.total - 1))
            self.frame = i
            self.slider.blockSignals(True)
            self.slider.setValue(i); self.slider.blockSignals(False)
            self.strip.set_frame(i)
            for j, b in enumerate(self.timeline):
                if not (b["pos"] <= i < b["pos"] + b["span"]):
                    continue
                c = self.studio.built[b["key"]]
                off_local = i - b["pos"]
                blend_start = b["span"] - b["d_next"]
                if b["d_next"] and off_local >= blend_start:
                    d = b["d_next"]
                    off = off_local - blend_start
                    a_img = c["scene"].paint_snapshot(
                        c["snaps"][b["F"] - d + off], use_cache=True)
                    nb = self.timeline[j + 1]
                    nc = self.studio.built[nb["key"]]
                    b_img = nc["scene"].paint_snapshot(nc["snaps"][off], use_cache=True)
                    self.canvas.set_image(
                        xfade_composite(a_img, b_img, b["ttype"], (off + 0.5) / d))
                    self.lbl.setText(f"{i+1}/{self.total}  ({i/self.fps:.2f}s)"
                                     f"  [{b['key']} \N{MULTIPLICATION X} {b['ttype']} "
                                     f"{off+1}/{d}]")
                else:
                    self.canvas.set_image(c["scene"].paint_snapshot(
                        c["snaps"][b["consumed"] + off_local], use_cache=True))
                    self.lbl.setText(f"{i+1}/{self.total}  "
                                     f"({i/self.fps:.2f}s)  [{b['key']}]")
                break
            seg = next((txt for s0, e0, txt in self._chapters()
                        if s0 <= i < e0), None)
            self.seg_lbl.setText(f"segment: {seg}" if seg else "segment: —")

        def _scrub(self, v):
            if not self.playing: self._set_frame(v)

        def _toggle(self):
            if not self.studio or not self.timeline: return
            self.playing = not self.playing
            self.play_btn.setText("⏸" if self.playing else "▶")
            if self.playing:
                if self.frame + 1 >= self.total: self._set_frame(0)
                self.timer.start(int(1000 / self.fps))
            else:
                self.timer.stop()

        def _advance(self):
            if self.frame + 1 >= self.total: self._toggle()
            else: self._set_frame(self.frame + 1)

        # -- export ------------------------------------------------------------------
        def render_mp4(self):
            if self.worker and self.worker.isRunning(): return
            order = self._order()
            if not order:
                self.status.setText("enable at least one clip"); return
            path, _ = QFileDialog.getSaveFileName(self, "Render MP4",
                                                  "movie.mp4", "MP4 (*.mp4)")
            if not path: return
            self._busy(True)
            self.status.setText("assembling… (cut boundaries copy; "
                                "new/changed transitions encode)")
            self.worker = AssembleWorker(self.studio, order, path,
                                         dict(self.transitions))
            self.worker.done.connect(self._rendered)
            self.worker.start()

        def _rendered(self, ok, info):
            self._busy(False)
            self.status.setText(f"rendered -> {info}" if ok else info)

        def _busy(self, on):
            for b in (self.build_btn, self.render_btn, self.combo, self.add_btn,
                      self.var_btn, self.tr_btn, self.dup_btn, self.del_btn,
                      self.chap_btn):
                b.setEnabled(not on)

    win = Win(); win.show()
    return win

# ---------------------------------------------------------------- gallery
def open_example_gallery(parent=None):
    from PySide6.QtWidgets import QScrollArea
    try:
        import svglab_examples as SX
    except ImportError:
        QMessageBox.warning(parent, "Examples",
                            "svglab_examples.py was not found next to "
                            "svglab.py — the gallery lists examples from that file.")
        return None

    TW, TH = 480, 270
    # resolve BEFORE the thumb worker chdirs into a temp dir (cache persistence)
    cache_dir = os.path.abspath(os.path.join(CACHE_DIR, "gallery"))
    os.makedirs(cache_dir, exist_ok=True)
    try:
        with open(__file__, "rb") as f:
            engine_stamp = hashlib.sha256(f.read()).hexdigest()[:10]
    except OSError:
        engine_stamp = "unknown"

    def thumb_path(name, cls):
        try:
            src = inspect.getsource(cls)
        except Exception:
            src = name
        h = hashlib.sha256((engine_stamp + src).encode()).hexdigest()[:10]
        return os.path.join(cache_dir, f"{name}_{h}.png")

    def render_thumb(name, cls):
        tp = thumb_path(name, cls)
        if os.path.exists(tp):
            img = QImage(tp)
            if not img.isNull():
                return img
        if SX.is_movie(cls):
            proj = cls()
            first_fn = proj.clips()[0][1]
            sc = proj.SceneClass(width=TW, height=TH, fps=10)
            snaps = sc.record_playable(first_fn)
        else:
            sc = cls(width=TW, height=TH, fps=10)
            snaps = sc.record_preview()
        idx = max(0, min(int(len(snaps) * 0.6), len(snaps) - 1))
        img = sc.paint_snapshot(snaps[idx])
        img.save(tp)
        return img

    class ThumbWorker(QThread):
        got = Signal(str, QImage)
        step = Signal(str)
        def run(self):
            old = os.getcwd()
            tmp = tempfile.mkdtemp(prefix="svglab_gallery_")
            try:
                os.chdir(tmp)
                items = list(SX.EXAMPLES.items())
                for i, (name, cls) in enumerate(items, 1):
                    self.step.emit(f"thumbnail {i}/{len(items)} — {name}")
                    try:
                        img = render_thumb(name, cls)
                    except Exception:
                        import traceback; traceback.print_exc()
                        img = QImage()
                    self.got.emit(name, img)
            finally:
                os.chdir(old)
                shutil.rmtree(tmp, ignore_errors=True)

    class RenderWorker(QThread):
        tick = Signal(str)
        done = Signal(bool, str)
        def __init__(self, name, cls, quality, out):
            super().__init__()
            self.name, self.cls = name, cls
            self.quality, self.out = quality, out
        def run(self):
            try:
                def prog(a, b=None):
                    self.tick.emit(f"{self.name}: {b + ' ' if b else ''}frame {a}")
                SX.render_example(self.name, self.cls, self.quality,
                                  self.out, progress=prog)
                self.done.emit(True, self.out)
            except Exception as e:
                import traceback; traceback.print_exc()
                self.done.emit(False, f"{type(e).__name__}: {e}")

    dlg = QDialog(parent)
    dlg.setWindowTitle("svglab examples")
    dlg.resize(1000, 600)
    chosen = {"name": None}
    ready, busy = set(), {"on": False}
    rw = {"w": None}

    grid_host = QWidget()
    grid = QGridLayout(grid_host)
    grid.setSpacing(12)
    cards = {}
    for i, (name, cls) in enumerate(SX.EXAMPLES.items()):
        kind = "movie" if SX.is_movie(cls) else "scene"
        doc = ((cls.__doc__ or "").strip().splitlines() or [""])[0]
        b = QToolButton()
        b.setText(f"{name}\n{kind}")
        b.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        b.setIconSize(QSize(200, 112))
        b.setFixedSize(224, 170)
        b.setToolTip(doc + "\n(left-click opens · right-click for render/source)")
        b.setEnabled(False)
        b.setContextMenuPolicy(Qt.CustomContextMenu)
        b.clicked.connect(lambda _=False, n=name:
                          (chosen.__setitem__("name", n), dlg.accept()))
        b.customContextMenuRequested.connect(
            lambda pos, n=name, btn=b: _menu(n, btn.mapToGlobal(pos)))
        grid.addWidget(b, i // 4, i % 4)
        cards[name] = b

    scroll = QScrollArea()
    scroll.setWidget(grid_host)
    scroll.setWidgetResizable(True)

    status = QLabel("generating thumbnails…  (left-click opens · right-click to render)")
    qual = QComboBox(); qual.addItems(list(QUAL)); qual.setCurrentText("720p30")

    def _set_busy(on):
        busy["on"] = on
        for n, b in cards.items():
            b.setEnabled((n in ready) and not on)
        write_all.setEnabled(not on)

    def _render(name):
        if rw["w"] and rw["w"].isRunning(): return
        out, _f = QFileDialog.getSaveFileName(
            dlg, "Render MP4", os.path.abspath(f"{name}.mp4"), "MP4 (*.mp4)")
        if not out: return
        _set_busy(True)
        status.setText(f"rendering {name} ({qual.currentText()})…")
        w = RenderWorker(name, SX.EXAMPLES[name], qual.currentText(), out)
        rw["w"] = w
        w.tick.connect(status.setText)
        w.done.connect(_render_done)
        w.start()

    def _render_done(ok, info):
        _set_busy(False)
        status.setText(f"rendered -> {info}" if ok else info)

    def _menu(name, global_pos):
        if rw["w"] and rw["w"].isRunning(): return
        m = QMenu(dlg)
        a_open = m.addAction("Open editor…")
        a_rend = m.addAction("Render MP4…")
        a_src = m.addAction("Write source to examples/")
        ch = m.exec(global_pos)
        if ch is None: return
        if ch is a_open:
            chosen["name"] = name
            dlg.accept()
        elif ch is a_rend:
            _render(name)
        else:
            p = SX.write_examples("examples", names=[name])[0]
            status.setText(f"wrote {p}")

    row = QHBoxLayout()
    write_all = QPushButton("Write all sources to examples/")
    def _write_all():
        paths = SX.write_examples("examples")
        QMessageBox.information(dlg, "Examples", "wrote:\n" + "\n".join(paths))
    write_all.clicked.connect(_write_all)
    close = QPushButton("Close")
    close.clicked.connect(dlg.reject)
    row.addWidget(write_all)
    row.addWidget(QLabel("render quality:"))
    row.addWidget(qual)
    row.addStretch(1)
    row.addWidget(close)

    v = QVBoxLayout(dlg)
    v.addWidget(scroll, 1)
    v.addWidget(status)
    v.addLayout(row)

    wk = ThumbWorker()
    def on_got(name, img):
        b = cards.get(name)
        if b is None: return
        ready.add(name)
        if not img.isNull():
            b.setIcon(QIcon(QPixmap.fromImage(img)))
        else:
            b.setText(f"{name}\n(thumbnail failed)")
        b.setEnabled(not busy["on"])
    wk.got.connect(on_got)
    wk.step.connect(status.setText)
    wk.start()

    dlg.exec()
    wk.wait()

    name = chosen["name"]
    if not name: return None
    SX.write_examples("examples", names=[name])
    path = os.path.abspath(os.path.join("examples", name + ".py"))
    try:
        cls, kind = load_project(path)
    except RuntimeError as e:
        QMessageBox.warning(parent, "Examples", str(e))
        return None
    if kind == "movie":
        return _launch_clip_gui(cls, path)
    return _launch_scene_gui(cls, path)


def launch_gui(project_cls, project_path=None):
    is_movie = (callable(getattr(project_cls, "clips", None))
                and getattr(project_cls, "SceneClass", None) is not None)
    if is_movie:
        return _launch_clip_gui(project_cls, project_path)
    return _launch_scene_gui(project_cls, project_path)

# ---------------------------------------------------------------- main
def main():
    argv = sys.argv[1:]
    if "--new-movie" in argv:
        i = argv.index("--new-movie")
        path = argv[i + 1] if len(argv) > i + 1 else "movie.py"
        if not os.path.exists(path):
            with open(path, "w", encoding="utf-8") as f:
                f.write(MOVIE_TEMPLATE)
            print(f"wrote {path}")
        os.environ.pop("QT_QPA_PLATFORM", None)
        cls, kind = load_project(path)
        if kind != "movie":
            sys.exit(f"{path} is not a Movie project")
        launch_gui(cls, os.path.abspath(path))
        return
    if "--gui" in argv:
        os.environ.pop("QT_QPA_PLATFORM", None)
        pos = [a for a in argv if not a.startswith("-")]
        cls, scene_path = SCENE_CLASS, None
        try:
            if pos and pos[0].lower().endswith(".zip"):
                target, tmp = _read_project(pos[0]); os.chdir(tmp)
                cls, scene_path = load_project(target)[0], target
            elif pos and pos[0].lower().endswith(".py"):
                cls, scene_path = load_project(pos[0])[0], os.path.abspath(pos[0])
            else:
                gen = os.path.abspath("svglab_demo_scene.py")
                with open(gen, "w", encoding="utf-8") as f:
                    f.write("from svglab import *\n\n\n"
                            + inspect.getsource(SCENE_CLASS) + "\n")
                cls, scene_path = load_scene_cls(gen), gen
        except RuntimeError as e:
            sys.exit(str(e))
        launch_gui(cls, scene_path)
        return
    if "--pack" in argv:
        i = argv.index("--pack")
        if len(argv) < i + 3:
            sys.exit("usage: python svglab.py --pack scene.py out.zip")
        pack_project(argv[i + 1], argv[i + 2]); return
    if "--unpack" in argv:
        i = argv.index("--unpack")
        if len(argv) < i + 2:
            sys.exit("usage: python svglab.py --unpack proj.zip")
        unpack_project(argv[i + 1]); return
    if "--clean" in argv:
        shutil.rmtree(CACHE_DIR, ignore_errors=True)
        print("cache cleared")
    os.environ.setdefault("QT_QPA_PLATFORM", "offscreen")

    srt_path = None
    if "--srt" in argv:
        i = argv.index("--srt")
        if len(argv) < i + 2:
            sys.exit("usage: python svglab.py scene.py --srt chapters.srt")
        srt_path = argv[i + 1]
        argv = argv[:i] + argv[i + 2:]

    quality = {"l": (854, 480, 15, 28), "m": (1280, 720, 30, 23),
               "h": (1920, 1080, 60, 20), "k": (3840, 2160, 60, 18)}
    q = next((a[2:] for a in argv if a.startswith("-q")), "m")
    pos = [a for a in argv if not a.startswith("-")]
    w, h, fps, crf = quality.get(q, quality["m"])
    target = None
    try:
        if pos and pos[0].lower().endswith(".zip"):
            target, tmp = _read_project(pos[0])
            os.chdir(tmp)
        elif pos and pos[0].lower().endswith(".py"):
            target = pos[0]
    except RuntimeError as e:
        sys.exit(str(e))
    app = QGuiApplication(sys.argv)
    if target:
        cls, kind = load_project(target)
        base = os.path.splitext(os.path.basename(target))[0]
    else:
        cls, kind, base = SCENE_CLASS, "scene", "demo"
    out = pos[1] if len(pos) > 1 else None
    if out and out.lower().endswith(".srt"):
        srt_path, out = out, None

    if kind == "movie":
        proj = cls()
        studio = ClipStudio(proj, width=w, height=h, fps=fps, crf=crf)
        names = studio.names()
        transitions = {}
        if out and out.lower().endswith(".json"):
            with open(out, encoding="utf-8") as f:
                data = json.load(f)
            plan = data if isinstance(data, list) else data.get("order", [])
            tlist = [] if isinstance(data, list) else data.get("transitions", [])
            order = []
            for ent in plan:
                if isinstance(ent, str):
                    order.append(studio.ensure_spec(ent))
                elif isinstance(ent, dict) and "clip" in ent:
                    order.append(studio.ensure_spec(ent["clip"], ent.get("args", {})))
                else:
                    sys.exit(f"bad playlist entry: {ent!r}")
            for t in tlist:
                i = int(t.get("after", -1))
                if not (0 <= i < len(order) - 1):
                    sys.exit(f"transition 'after' index {i} out of range")
                typ = t.get("type", "fade")
                if typ not in XFADE_TYPES:
                    sys.exit(f"unknown transition type {typ!r}")
                transitions[(order[i], order[i + 1])] = (typ, float(t.get("dur", 1.0)))
            out = None
        else:
            order = [studio.ensure_spec(n) for n in names]
        print(f"building {len(set(order))} clip render(s)…")
        studio.ensure_all(progress=lambda c, s: print(
            f"\r  {s} frame {c}", end="", flush=True))
        print()
        if srt_path:
            write_srt(srt_path, movie_srt_entries(studio, order, transitions, fps))
            print(f"chapters -> {srt_path}")
        if out is None:
            if not srt_path:
                out = f"{base}_{q}.mp4"
            else:
                return
        studio.assemble(order, out, transitions)
        print(f"done -> {out}")
        return

    scene = cls(width=w, height=h, fps=fps)
    path = out or f"{base}_{q}.mp4"
    if srt_path and not out:
        print("writing chapters (no video)…")
        scene.record_playable(scene.build)
        write_srt(srt_path, scene_srt_entries(scene, fps))
        print(f"done -> {srt_path}")
        return
    print(f"rendering {path}  ({w}x{h} @ {fps}fps)")
    scene.render(path, crf=crf)
    print(f"\ndone -> {path}")
    if srt_path:
        scene.record_playable(scene.build)
        write_srt(srt_path, scene_srt_entries(scene, fps))
        print(f"chapters -> {srt_path}")


if __name__ == "__main__":
    main()
