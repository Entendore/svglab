# svglab

Script-driven SVG animation -> MP4. Python scenes are the timeline; rendering
is deterministic (frame i is a pure function of progress), so previews scrub
instantly and exports match exactly.

## Quick start

```bash
python -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt      # + ffmpeg on PATH (or: pip install imageio-ffmpeg)
./demo.sh                            # renders demo + writes example sources

Commands
command
what it does
python svglab.py -qm	render built-in demo
python svglab.py scene.py -qh out.mp4	render a scene (l/m/h/k quality)
python svglab.py scene.py chapters.srt	chapters only (no video)
python svglab.py scene.py -qm --srt ch.srt	render + chapters
python svglab.py movie.py -qm	clip project (declared order)
python svglab.py movie.py order.json -qm	custom order + variants + transitions
python svglab.py --gui [scene.py]	editor: scrub, inspect, drag-to-patch
python svglab.py --new-movie	scaffold + open the clips GUI
python svglab.py --gallery	example gallery with thumbnails
python svglab.py --pack scene.py out.zip	portable project zip
python svglab.py --clean	wipe segment cache

GUI (scene)
Build preview -> snapshots record per frame -> scrub/step/play. Click selects
(inspector shows state + selector); drag generates move_to(...) and can
Patch into file; drag a segment's right edge on the timeline to retime;
Chapters… lists every play()/wait() (click to jump, Export SRT);
right-click an object in Examples… gallery to render directly.

GUI (clips)
clip_* methods become reorderable clips on fresh scenes. Drag to arrange,
Duplicate to repeat, Add variant… instantiates parameterized clips
(clip_card(s, color=..., word=...)), Transitions… sets per-boundary
xfade (cuts stay -c copy; transitions encode once, cached). Scrubbing a
seam previews the real transition geometry.

from svglab import *

class MyScene(Scene):
    def build(self):
        svg = self.load("diagram.svg")        # or generate SVG strings
        self.play(FadeIn(svg), run_time=0.6)
        node = svg.select("#node-1")[0]
        self.play(Draw(node), run_time=1.0)
        t = self.text("hello", size=48)
        self.play(Typewriter(t), run_time=1.0)
        self.play(Shake(t), run_time=0.5)

Animations: Tween (.animate chains), FadeIn/Out, Draw, FillIn, MoveAlongPath, Stagger, Sequence, Recolor, Indicate, Shake, Morph, Typewriter, ValueTo+Tracker.
Easings: linear smooth ease_in ease_out ping_pong overshoot bounce_out elastic_out cubic_bezier(...). Export: .mp4 .gif .webm(alpha) or a folder
for a PNG sequence. Audio: self.soundtrack("music.mp3", fade_out=1.0).

See svglab_examples.py (8 examples) — python svglab_examples.py --list.
