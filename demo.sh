#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
echo "== rendering built-in demo =="
python svglab.py -qm
echo "== writing example sources =="
python svglab_examples.py --write examples
echo
echo "Try:"
echo "  python svglab.py --gui                          # demo editor"
echo "  python svglab.py --gui examples/network.py      # scrub + inspect + patch"
echo "  python svglab.py --gui examples/flowsteps.py    # clips GUI"
echo "  python svglab.py --gallery                      # example gallery"
