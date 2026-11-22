"""
svglab_examples.py — generate example scenes & movies for svglab.

    python svglab_examples.py --list
    python svglab_examples.py --write [outdir]      # default: examples/
    python svglab_examples.py network -qh           # render one
    python svglab_examples.py all -qm               # render everything

Written examples are standalone (import svglab) — open with:
    python svglab.py --gui examples/network.py
"""
import os, sys, inspect

from svglab import *


# ══════════════════════════════════════════════════════════════════════
# Examples — class-self-contained so inspect.getsource yields runnable files
# ══════════════════════════════════════════════════════════════════════


class NetworkFlow(Scene):
    """Nodes pop in, a wire draws itself, a packet rides it; morph, camera."""
    background = "#101014"

    @staticmethod
    def _write_svg(path):
        svg = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 480 270">
  <rect width="480" height="270" rx="14" fill="#15151f"/>
  <path id="wire" d="M96,190 C160,110 320,110 384,190" fill="none"
        stroke="#4aa8ff" stroke-width="4" stroke-linecap="round"/>
  <circle class="node" id="n1" cx="96"  cy="190" r="18" fill="#f6c445"/>
  <circle class="node" id="n2" cx="240" cy="128" r="18" fill="#e05a5a"/>
  <circle class="node" id="n3" cx="384" cy="190" r="18" fill="#59d499"/>
  <circle id="packet" cx="96" cy="190" r="7" fill="#ffffff"/>
</svg>"""
        with open(path, "w") as f:
            f.write(svg)

    def build(self):
        self._write_svg("network.svg")
        svg = self.load("network.svg")
        title = self.text("packet switching", size=46)
        title.move_to(0, -self.h / 2 + 70)
        self.play(FadeIn(svg), run_time=0.6)
        nodes = svg.select(".node")
        wire = svg.select("#wire")[0]
        pkt = svg.select("#packet")[0]
        self.remove(*nodes)
        self.play(Stagger(*[FadeIn(n) for n in nodes], lag_ratio=0.25), run_time=1.4)
        self.play(Draw(wire), run_time=1.4)
        self.play(Typewriter(title), run_time=1.1)
        pct = self.text("0%", size=44)
        pct.move_to(0, self.h / 2 - 70)
        pkt.opacity = 0.0
        self.add(pkt, pct)
        tr = Tracker(0.0)
        pct.add_updater(lambda p, t: p.set_text(f"{tr.value * 100:.0f}%"))
        self.play(ValueTo(tr, 1.0), MoveAlongPath(pkt, wire, orient=True),
                  run_time=2.4, easing=linear)
        pct.remove_updater(pct.updaters[0])
        pct.set_text("100%")
        self.play(Recolor(nodes[1], fill="#7c5cff"), run_time=0.5)
        ring = ring_around(nodes[1], color="#7c5cff")
        self.add(ring)
        self.play(FadeIn(ring), Indicate(nodes[1]), run_time=0.8)
        self.play(FadeOut(ring), run_time=0.4)
        ar = arrow((nodes[0].x, nodes[0].y - 42),
                   (nodes[0].x, nodes[0].y - 26), color="#f6c445")
        self.add(ar)
        self.play(FadeIn(ar), run_time=0.4)
        self.play(Tween(self.camera.animate
                        .move_to(nodes[2].x, nodes[2].y).zoom(2.2)), run_time=1.0)
        tag = self.text("exit node", size=26)
        tag.move_to(nodes[2].x, nodes[2].y + 52)
        self.play(FadeIn(tag), run_time=0.4)
        self.wait(0.4)
        self.play(FadeOut(tag),
                  Tween(self.camera.animate.move_to(0, 0).zoom(1)), run_time=0.8)
        self.play(Morph(wire, "M96,190 C150,110 210,250 240,128 S330,60 384,190"),
                  run_time=1.4)
        self.play(Shake(title, intensity=7), run_time=0.5)
        grp = Group(*nodes)
        self.remove(*nodes)
        self.add(grp)
        self.play(grp.animate.shift(0, 30), run_time=0.8)
        self.play(*[FadeOut(o) for o in list(self.objects)], run_time=0.7)


class BarChart(Scene):
    """Bars grow from the axis via Trackers + bounce_out; labels stagger in."""
    background = "#101014"

    @staticmethod
    def _bar_svg(bw, bh, color):
        return (f'<svg xmlns="{SVG_NS}" viewBox="0 0 {bw} {bh}">'
                f'<rect width="{bw}" height="{bh}" rx="8" fill="{color}"/></svg>')

    @staticmethod
    def _axis_svg(w, h, x0, ybot):
        return (f'<svg xmlns="{SVG_NS}" viewBox="{-w/2} {-h/2} {w} {h}">'
                f'<line x1="{x0}" y1="{ybot}" x2="{w/2-100}" y2="{ybot}" '
                f'stroke="#3a3a4c" stroke-width="3"/>'
                f'<line x1="{x0}" y1="{ybot}" x2="{x0}" y2="{-h/2+110}" '
                f'stroke="#3a3a4c" stroke-width="3"/></svg>')

    def build(self):
        w, h = self.w, self.h
        data = [("Q1", 0.38, "#4aa8ff"), ("Q2", 0.56, "#59d499"),
                ("Q3", 0.82, "#f6c445"), ("Q4", 0.66, "#e05a5a")]
        ybot = h / 2 - 130
        top = -h / 2 + 140
        x0 = -w / 2 + 230
        bw, gap = 100, 70
        span = ybot - top
        axis = GeneratedObj(self._axis_svg(w, h, x0, ybot))
        title = self.text("Quarterly Revenue", size=54)
        title.move_to(0, -h / 2 + 80)
        self.play(FadeIn(axis), Typewriter(title), run_time=1.4)
        bars, anims, geo = [], [], []
        for i, (lab, v, col) in enumerate(data):
            bh = v * span
            cx = x0 + 60 + i * (bw + gap)
            bar = GeneratedObj(self._bar_svg(bw, bh, col))
            bar.move_to(cx, ybot - bh / 2)
            bar.scale = 0.001
            tr = Tracker(0.001)
            def pin(b, t, tr=tr, yb=ybot, bh=bh):
                s = max(tr.value, 0.001)
                b.scale = s
                b.y = yb - bh * s / 2
            bar.add_updater(pin)
            bars.append(bar)
            anims.append(ValueTo(tr, 1.0, easing=bounce_out))
            geo.append((cx, bh, lab, v, col))
        self.add(*bars)
        self.play(Stagger(*anims, lag_ratio=0.18))
        caps = []
        for cx, bh, lab, v, col in geo:
            q = self.text(lab, size=30, color="#8a90a8")
            q.move_to(cx, ybot + 44)
            val = self.text(f"{int(v * 100)}", size=34, color=col)
            val.move_to(cx, ybot - bh - 32)
            caps += [FadeIn(q), FadeIn(val)]
        self.play(Stagger(*caps, lag_ratio=0.12))
        self.wait(0.9)
        self.play(*[FadeOut(o) for o in list(self.objects)], run_time=0.7)


class Orbits(Scene):
    """Pure-updater physics: planets + moon are functions of scene time."""
    background = "#0b0b12"

    @staticmethod
    def _disc(r, color):
        return (f'<svg xmlns="{SVG_NS}" viewBox="{-2*r} {-2*r} {4*r} {4*r}">'
                f'<circle cx="0" cy="0" r="{r}" fill="{color}"/></svg>')

    @staticmethod
    def _orbit_svg(r):
        pad = 14
        return (f'<svg xmlns="{SVG_NS}" viewBox="{-r-pad} {-r-pad} '
                f'{2*(r+pad)} {2*(r+pad)}">'
                f'<circle cx="0" cy="0" r="{r}" fill="none" '
                f'stroke="#26262f" stroke-width="2"/></svg>')

    @staticmethod
    def _sun_svg():
        return (f'<svg xmlns="{SVG_NS}" viewBox="-120 -120 240 240">'
                f'<circle cx="0" cy="0" r="72" fill="#f6c445" opacity="0.15"/>'
                f'<circle cx="0" cy="0" r="46" fill="#f6c445"/></svg>')

    def build(self):
        sun = GeneratedObj(self._sun_svg())
        sun.move_to(0, 0)
        self.play(FadeIn(sun), run_time=0.5)
        specs = [(120, 2.1, 13, "#4aa8ff"),
                 (210, 1.2, 19, "#59d499"),
                 (300, 0.75, 15, "#e05a5a")]
        rings, planets = [], []
        for R, om, r, col in specs:
            orb = GeneratedObj(self._orbit_svg(R))
            rings.append(orb)
            p = GeneratedObj(self._disc(r, col))
            p.move_to(R, 0)
            p.add_updater(lambda o, t, R=R, om=om:
                          o.move_to(R * math.cos(om * t), R * math.sin(om * t)))
            planets.append(p)
        self.play(Stagger(*[FadeIn(o) for o in rings], lag_ratio=0.2), run_time=1.0)
        self.add(*planets)
        self.play(Stagger(*[FadeIn(p) for p in planets], lag_ratio=0.2), run_time=0.8)
        host = planets[0]
        moon = GeneratedObj(self._disc(6, "#c9c9d8"))
        moon.add_updater(lambda o, t: o.move_to(
            host.x + 34 * math.cos(6 * t), host.y + 34 * math.sin(6 * t)))
        self.add(moon)
        self.play(FadeIn(moon), run_time=0.3)
        self.play(Tween(self.camera.animate.move_to(70, 0).zoom(1.18)),
                  run_time=2.0, easing=smooth)
        self.wait(2.6)
        self.play(Tween(self.camera.animate.move_to(0, 0).zoom(1)), run_time=1.4)
        self.play(*[FadeOut(o) for o in list(self.objects)], run_time=0.8)


class MorphShapes(Scene):
    """One path morphs circle -> square -> triangle -> star -> circle."""
    background = "#101014"

    @staticmethod
    def _poly_d(pts):
        return "M" + " L".join(f"{x:.1f},{y:.1f}" for x, y in pts) + " Z"

    @staticmethod
    def _circle_pts(r, n=72, cx=0.0, cy=0.0):
        return [(cx + r * math.cos(2 * math.pi * i / n),
                 cy + r * math.sin(2 * math.pi * i / n)) for i in range(n)]

    @staticmethod
    def _ngon(r, k, rot=-math.pi / 2, cx=0.0, cy=0.0):
        return [(cx + r * math.cos(rot + 2 * math.pi * i / k),
                 cy + r * math.sin(rot + 2 * math.pi * i / k)) for i in range(k)]

    @staticmethod
    def _star_pts(r1, r2, k=5, rot=-math.pi / 2, cx=0.0, cy=0.0):
        pts = []
        for i in range(2 * k):
            r = r1 if i % 2 == 0 else r2
            a = rot + math.pi * i / k
            pts.append((cx + r * math.cos(a), cy + r * math.sin(a)))
        return pts

    def build(self):
        CX, CY = 260, 170
        seq = [("circle",   self._poly_d(self._circle_pts(118, 72, CX, CY))),
               ("square",   self._poly_d(self._ngon(118, 4, math.pi / 4, CX, CY))),
               ("triangle", self._poly_d(self._ngon(132, 3, -math.pi / 2, CX, CY))),
               ("star",     self._poly_d(self._star_pts(132, 56, 5, -math.pi / 2, CX, CY))),
               ("circle",   self._poly_d(self._circle_pts(118, 72, CX, CY)))]
        svg_str = (f'<svg xmlns="{SVG_NS}" viewBox="0 0 520 340">'
                   f'<path id="shape" d="{seq[0][1]}" fill="none" '
                   f'stroke="#4aa8ff" stroke-width="6" '
                   f'stroke-linejoin="round"/></svg>')
        with open("morph.svg", "w") as f:
            f.write(svg_str)
        svg = self.load("morph.svg")
        shape = svg.select("#shape")[0]
        self.play(Draw(shape), run_time=1.3)
        label = self.text("circle", size=40)
        label.move_to(0, -self.h / 2 + 90)
        self.play(FadeIn(label), run_time=0.3)
        for name, d in seq[1:]:
            nxt = self.text(name, size=40)
            nxt.move_to(0, -self.h / 2 + 90)
            self.play(FadeOut(label, run_time=0.22))
            self.play(Morph(shape, d), run_time=1.1)
            label = nxt
            self.play(FadeIn(label), run_time=0.22)
        self.wait(0.5)
        self.play(FadeOut(shape), FadeOut(label), run_time=0.5)


class TitleKit(Scene):
    """Typography toolkit: typewriter, pulse, ring, arrow, crossfade, camera."""
    background = "#101014"

    def build(self):
        w, h = self.w, self.h
        t1 = self.text("svglab", size=110, weight="bold")
        t1.move_to(0, -20)
        sub = self.text("script -> motion -> video", size=30, color="#8a90a8")
        sub.move_to(0, 62)
        self.play(Typewriter(t1), run_time=1.4)
        self.play(FadeIn(sub), run_time=0.4)
        self.play(Indicate(t1, amp=0.06), run_time=0.7)
        ring = ring_around(t1, pad=28, color="#f6c445", width=4, radius=18)
        self.add(ring)
        self.play(FadeIn(ring), run_time=0.5)
        edge = t1.x - t1.content_size()[0] / 2 - 34
        ar = arrow((-w / 2 + 150, h / 2 - 150), (edge, t1.y + 12), color="#f6c445")
        note = self.text("this one", size=26, color="#f6c445")
        note.move_to(-w / 2 + 205, h / 2 - 172)
        self.play(FadeIn(ar), FadeIn(note), run_time=0.5)
        self.wait(0.5)
        self.play(FadeOut(ar), FadeOut(note), FadeOut(ring), run_time=0.4)
        err = self.text("404", size=64, color="#e05a5a")
        err.move_to(0, 158)
        self.play(FadeIn(err), run_time=0.3)
        self.play(Shake(err, intensity=12), run_time=0.6)
        ok = self.text("200", size=64, color="#59d499")
        ok.move_to(0, 158)
        ok.opacity = 0.0
        self.add(ok)
        self.play(err.animate.set_opacity(0.0),
                  ok.animate.set_opacity(1.0), run_time=0.45)
        self.play(Tween(self.camera.animate.move_to(t1.x, t1.y).zoom(1.8)),
                  run_time=0.9)
        self.wait(0.3)
        self.play(Tween(self.camera.animate.move_to(0, 0).zoom(1)),
                  FadeOut(err), FadeOut(ok), run_time=0.8)
        self.play(sub.animate.shift(0, 22), run_time=0.7,
                  easing=cubic_bezier(0.34, 1.56, 0.64, 1.0))
        badge = self.text("v14", size=42, color="#7c5cff", weight="bold")
        badge.move_to(w / 2 - 150, -h / 2 + 120)
        badge.scale = 0.01
        self.play(badge.animate.scale_by(100), run_time=0.6, easing=overshoot)
        self.wait(0.6)
        self.play(*[FadeOut(o) for o in list(self.objects)], run_time=0.6)


class WaveRide(Scene):
    """Draw a wave, ride it with arc-length motion, morph, ride oriented."""
    background = "#101014"

    @staticmethod
    def _wave_d(x0, x1, y0, amp, k, phase, n=120):
        pts = []
        for i in range(n + 1):
            x = x0 + (x1 - x0) * i / n
            pts.append(f"{x:.1f},{y0 + amp * math.sin(k * x + phase):.1f}")
        return "M" + " L".join(pts)

    def build(self):
        W, H = 960, 540
        d1 = self._wave_d(60, 900, 270, 90, 2 * math.pi / 240, 0.0)
        svg_str = (f'<svg xmlns="{SVG_NS}" viewBox="0 0 {W} {H}">'
                   f'<path id="wave" d="{d1}" fill="none" stroke="#4aa8ff" '
                   f'stroke-width="5" stroke-linecap="round"/>'
                   f'<circle id="dot" cx="60" cy="270" r="11" fill="#f6c445"/></svg>')
        with open("wave.svg", "w") as f:
            f.write(svg_str)
        s = self.load("wave.svg")
        wave = s.select("#wave")[0]
        dot = s.select("#dot")[0]
        self.play(Draw(wave), run_time=1.6)
        title = self.text("arc-length motion", size=40, color="#8a90a8")
        title.move_to(0, -self.h / 2 + 70)
        self.play(FadeIn(title), run_time=0.4)
        dot.opacity = 0.0
        self.add(dot)
        self.play(MoveAlongPath(dot, wave), run_time=3.2, easing=linear)
        d2 = self._wave_d(60, 900, 270, 130, 2 * math.pi / 140, 1.2)
        self.play(Morph(wave, d2), run_time=1.4)
        self.play(MoveAlongPath(dot, wave, orient=True), run_time=3.2, easing=linear)
        self.wait(0.4)
        self.play(FadeOut(s), FadeOut(dot), FadeOut(title), run_time=0.6)


class LogoReveal(Scene):
    """Hexagon and bolt draw on, fill in, group, tagline typewrites."""
    background = "#101014"

    @staticmethod
    def _logo_svg():
        cx, cy, r = 200, 200, 150
        pts = [(cx + r * math.cos(math.radians(a)),
                cy + r * math.sin(math.radians(a)))
               for a in (-90, -30, 30, 90, 150, 210)]
        hexd = "M" + " L".join(f"{x:.1f},{y:.1f}" for x, y in pts) + " Z"
        bolt = "M218,96 L148,224 L196,224 L178,306 L258,170 L206,170 Z"
        return (f'<svg xmlns="{SVG_NS}" viewBox="0 0 400 400">'
                f'<path id="hex" d="{hexd}" fill="none" stroke="#4aa8ff" '
                f'stroke-width="10" stroke-linejoin="round"/>'
                f'<path id="bolt" d="{bolt}" fill="#f6c445" '
                f'stroke="#f6c445" stroke-width="6" stroke-linejoin="round"/></svg>')

    def build(self):
        with open("logo.svg", "w") as f:
            f.write(self._logo_svg())
        svg = self.load("logo.svg", canvas=(0.62 * self.h,))
        hexagon = svg.select("#hex")[0]
        bolt = svg.select("#bolt")[0]
        self.play(Draw(hexagon), run_time=1.2)
        self.play(Draw(bolt), run_time=0.8)
        self.play(FillIn(bolt), run_time=0.6)
        self.play(Indicate(svg, amp=0.05), run_time=0.6)
        grp = Group(hexagon, bolt)
        self.remove(hexagon, bolt)
        self.add(grp)
        self.play(grp.animate.shift(0, -70), run_time=0.7)
        tag = self.text("svglab", size=64, weight="bold")
        tag.move_to(0, self.h / 2 - 150)
        self.play(Typewriter(tag), run_time=1.0)
        self.play(Tween(self.camera.animate.move_to(bolt.x, bolt.y).zoom(1.9)),
                  run_time=0.9)
        self.wait(0.3)
        self.play(Tween(self.camera.animate.move_to(0, 0).zoom(1)), run_time=0.8)
        self.wait(0.4)
        self.play(FadeOut(grp), FadeOut(tag), run_time=0.6)


class FlowSteps(Movie):
    """Clip variants + transitions showcase (GUI: --gui flowsteps.py)."""
    DEFAULT_TRANSITIONS = {
        ("title", "step1"): ("fade", 0.5),
        ("step1", "step2"): ("wipeleft", 0.5),
        ("step2", "step3"): ("wipeleft", 0.5),
        ("step3", "outro"): ("fadeblack", 0.6),
    }

    def clip_title(self, s):
        t = s.text("Three Steps", size=64, weight="bold")
        sub = s.text("a clip-variants showcase", size=28, color="#8a90a8")
        t.move_to(0, -40)
        sub.move_to(0, 44)
        s.play(FadeIn(t), run_time=0.5)
        s.play(Typewriter(sub), run_time=0.8)
        s.wait(0.6)
        s.play(FadeOut(t), FadeOut(sub), run_time=0.5)

    def clip_step(self, s, n=1, label="Step", color="#4aa8ff"):
        num = s.text(str(n), size=150, color=color, weight="bold")
        lab = s.text(label, size=44)
        num.move_to(0, -40)
        lab.move_to(0, 118)
        ring = ring_around(num, pad=34, color=color, width=5, radius=26)
        s.play(FadeIn(num), run_time=0.35)
        s.play(FadeIn(ring), run_time=0.4)
        s.play(Typewriter(lab), run_time=0.7)
        s.wait(0.5)
        s.play(FadeOut(num), FadeOut(lab), FadeOut(ring), run_time=0.45)

    def clip_outro(self, s):
        t = s.text("svglab", size=64, color="#59d499", weight="bold")
        s.play(FadeIn(t), run_time=0.5)
        s.wait(0.8)
        s.play(FadeOut(t), run_time=0.5)

    def clips(self):
        return [("title", self.clip_title),
                ("step", self.clip_step),
                ("step1", lambda s: self.clip_step(s, 1, "Plan",   "#4aa8ff")),
                ("step2", lambda s: self.clip_step(s, 2, "Build",  "#59d499")),
                ("step3", lambda s: self.clip_step(s, 3, "Ship",   "#f6c445")),
                ("outro", self.clip_outro)]


# ══════════════════════════════════════════════════════════════════════
EXAMPLES = {
    "network":   NetworkFlow,
    "barchart":  BarChart,
    "orbits":    Orbits,
    "morph":     MorphShapes,
    "titles":    TitleKit,
    "wave":      WaveRide,
    "logo":      LogoReveal,
    "flowsteps": FlowSteps,
}

QUAL = {"l": (854, 480, 15, 28), "m": (1280, 720, 30, 23),
        "h": (1920, 1080, 60, 20), "k": (3840, 2160, 60, 18)}
_QMAP = {"480p15": "l", "720p30": "m", "1080p60": "h", "4K60": "k"}

HEADER = ('"""{name} — svglab example (generated by svglab_examples.py).\n'
          'Run:   python svglab.py {name}.py -qm\n'
          'GUI:   python svglab.py --gui {name}.py\n"""\n'
          'import math\n'
          'from svglab import *\n\n\n')


def is_movie(cls):
    return (callable(getattr(cls, "clips", None))
            and getattr(cls, "SceneClass", None) is not None)


def _progress(prefix):
    def fn(a, b=None):
        if b is None:
            print(f"\r  {prefix} frame {a}", end="", flush=True)
        else:
            print(f"\r  {prefix} {b} frame {a}   ", end="", flush=True)
    return fn


def write_examples(outdir="examples", names=None):
    os.makedirs(outdir, exist_ok=True)
    written = []
    for name, cls in EXAMPLES.items():
        if names and name not in names:
            continue
        path = os.path.join(outdir, name + ".py")
        src = inspect.getsource(cls)
        if not src.endswith("\n"):
            src += "\n"
        with open(path, "w", encoding="utf-8") as f:
            f.write(HEADER.format(name=name))
            f.write(src)
        written.append(path)
    return written


def render_example(name, cls, quality="m", out=None, progress=None):
    quality = _QMAP.get(quality, quality)
    w, h, fps, crf = QUAL.get(quality, QUAL["m"])
    out = out or f"{name}_{quality}.mp4"
    prog = progress or _progress("  ")
    if is_movie(cls):
        proj = cls()
        studio = ClipStudio(proj, width=w, height=h, fps=fps, crf=crf)
        names = studio.names()
        keys = [studio.ensure_spec(n) for n in names]
        print(f"building {len(names)} clip render(s) for '{name}'…")
        studio.ensure_all(progress=prog)
        trans = {(studio.ensure_spec(a), studio.ensure_spec(b)): v
                 for (a, b), v in getattr(proj, "DEFAULT_TRANSITIONS", {}).items()}
        studio.assemble(keys, out, trans)
    else:
        sc = cls(width=w, height=h, fps=fps)
        sc.progress_fn = prog
        print(f"rendering '{name}' ({w}x{h} @ {fps}fps)…")
        sc.render(out, crf=crf)
        print()
    print(f"done -> {out}")


def main():
    argv = sys.argv[1:]
    if not argv or argv[0] in ("-h", "--help"):
        print(__doc__)
        print("examples: " + ", ".join(EXAMPLES))
        return
    if "--list" in argv:
        for name, cls in EXAMPLES.items():
            kind = "movie" if is_movie(cls) else "scene"
            doc = (cls.__doc__ or "").strip().splitlines()[0] if cls.__doc__ else ""
            print(f"  {name:10s} {kind:5s}  {doc}")
        return
    if argv[0] == "--write":
        outdir = argv[1] if len(argv) > 1 and not argv[1].startswith("-") else "examples"
        paths = write_examples(outdir)
        print(f"wrote {len(paths)} example(s) -> {outdir}/")
        print("try:  python svglab.py --gui " + paths[0].replace("\\", "/"))
        return
    q = next((a[2:] for a in argv if a.startswith("-q") and len(a) > 2), "m")
    positional = [a for a in argv if not a.startswith("-")]
    if not positional:
        print("no example name given — try --list")
        return
    name = positional[0]
    if name == "all":
        os.environ.setdefault("QT_QPA_PLATFORM", "offscreen")
        app = QGuiApplication(sys.argv)
        for n, cls in EXAMPLES.items():
            render_example(n, cls, q)
        return
    cls = EXAMPLES.get(name)
    if cls is None:
        print(f"unknown example '{name}' — choices: {', '.join(EXAMPLES)}")
        return
    os.environ.setdefault("QT_QPA_PLATFORM", "offscreen")
    app = QGuiApplication(sys.argv)
    out = next((a for a in positional[1:] if "." in a), None)
    render_example(name, cls, q, out)


if __name__ == "__main__":
    main()
