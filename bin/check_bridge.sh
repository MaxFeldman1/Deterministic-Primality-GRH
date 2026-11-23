#!/bin/bash
# Compiles grh-bridge/GRHBridge.lean on the box against the GRH archive's oleans and this project's.
# Usage: bin/check_bridge.sh            (compile + #print axioms)
#        bin/check_bridge.sh --replay   (also leanchecker replay of the whole environment; hours)
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
rsync -az "$ROOT/grh-bridge/" chub-build:maths/grh-bridge/
ssh chub-build 'bash -s' -- "${1:-}" <<'REMOTE'
set -euo pipefail
export PATH=$HOME/.elan/bin:$PATH
A=$HOME/maths/grh-archive; D=$HOME/maths/detprimality
LP=$A/.lake/build/lib/lean
for p in $A/.lake/packages/*/.lake/build/lib/lean; do LP=$LP:$p; done
LP=$LP:$D/.lake/build/lib/lean
export LEAN_PATH=$LP
cd $HOME/maths/grh-bridge
nice -n 19 $HOME/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -o GRHBridge.olean GRHBridge.lean
if [ "${1:-}" = "--replay" ]; then
  nice -n 19 $HOME/.elan/toolchains/leanprover--lean4---v4.33.1/bin/leanchecker GRHBridge 2>&1 | tail -5; echo "leanchecker rc=${PIPESTATUS[0]}"
fi
REMOTE
