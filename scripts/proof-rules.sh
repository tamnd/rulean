#!/usr/bin/env bash
# Checks the rules of spec 10.9 on the Lean sources in proof/.
#
# A proof must not contain sorry, admit, a new axiom, native_decide, bv_decide or implemented_by. A file must not turn off the heartbeat limit. The axiom audit of the proof job checks the compiled environment. This script checks the source, so it also finds a hole in a file that no target imports.

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
pattern='\b(sorry|admit|native_decide|bv_decide|implemented_by)\b|^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)?axiom\b|maxHeartbeats[[:space:]]+0\b'

found=0
while IFS= read -r -d '' file; do
  if grep -nE "$pattern" "$file" | sed "s|^|${file#"$root"/}:|"; then
    found=1
  fi
done < <(find "$root/proof" -name .lake -prune -o -name '*.lean' -print0)

if [ "$found" -ne 0 ]; then
  echo "proof-rules: the lines above break spec 10.9" >&2
  exit 1
fi
echo "proof-rules: no sorry, admit, axiom, native_decide, bv_decide, implemented_by or maxHeartbeats 0 in proof/"
