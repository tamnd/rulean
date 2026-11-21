#!/usr/bin/env bash
# Checks the proof package with the official kernel.
#
# leanchecker replays its modules in parallel tasks, and with two or more modules it crashes with exit code 139 in most runs (issue #15). With --fresh it replays one module, and every constant that the module imports, in one task. The root module RuleanProof imports every module of the package, so one run checks all of them, and also con-leche and the Lean core. Run `lake build` in proof/ first.

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root/proof"

# A module that the root does not import is not built and not checked, so each module must be imported by the root.
missing=0
while IFS= read -r file; do
  module="${file%.lean}"
  module="${module//\//.}"
  if ! grep -qxF "import $module" RuleanProof.lean; then
    echo "leanchecker: RuleanProof.lean does not import $module" >&2
    missing=1
  fi
done < <(find RuleanProof -name '*.lean' | LC_ALL=C sort)
if [ "$missing" -ne 0 ]; then
  exit 1
fi

lake env leanchecker --fresh RuleanProof
echo "leanchecker: RuleanProof and all of its imports pass"
