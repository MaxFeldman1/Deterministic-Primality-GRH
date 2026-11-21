#!/bin/bash
# Usage: bin/check.sh DetPrimality/Foo.lean   (path relative to lean/)
#        bin/check.sh --build                 (lake build whole lib)
# Syncs lean/ to the AWS box and compiles there (CPUs 184-191, nice 19). Never builds Mathlib from source.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
rsync -az --exclude .lake --exclude '*.olean' "$ROOT/lean/" chub-build:maths/detprimality/
if [ "${1:-}" = "--build" ]; then
  CMD="lake build"
else
  MOD="${1%.lean}"; MOD="${MOD//\//.}"
  CMD="lake build $MOD"   # builds the module and its imports (Mathlib from cache)
fi
ssh chub-build "cd ~/maths/detprimality && export PATH=\$HOME/.elan/bin:\$PATH && nice -n 19 taskset -c 184-191 $CMD"
