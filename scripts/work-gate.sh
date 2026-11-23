#!/usr/bin/env bash
# The work gate of the quick suite on Init and Std of a Lean release (spec 08.7.4).
#
# Usage: scripts/work-gate.sh BASELINE [RULEAN [BENCH]]
#
# BASELINE is the baseline file, normally docs/bench/work.json. RULEAN is the rulean binary, and the default is target/release/rulean. BENCH is the rulean-bench binary, and the default is target/release/rulean-bench. The `leanexport` of the release must be on PATH. The script exports Init and Std with leanexport, checks each export with one thread, and compares the work count of each report with the baseline. If the gate fails, the script prints the baseline that the run gives, so that a pull request that changes the work on purpose can update the file. With WRITE=1, the script writes the counts into BASELINE and does not compare.

set -euo pipefail

if [ "$#" -lt 1 ] || [ "$#" -gt 3 ]; then
  echo "usage: $0 BASELINE [RULEAN [BENCH]]" >&2
  exit 64
fi
here="$(cd "$(dirname "$0")/.." && pwd)"
baseline="$1"
rulean="${2:-$here/target/release/rulean}"
bench="${3:-$here/target/release/rulean-bench}"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

reports=()
for m in Init Std; do
  (cd "$work" && leanexport "$m" >"$work/$m.ndjson")
  echo "leanexport $m: $(wc -l <"$work/$m.ndjson") lines"
  "$rulean" check --threads 1 --format text --report "$work/$m.json" "$work/$m.ndjson"
  rm -f "$work/$m.ndjson"
  reports+=("$m=$work/$m.json")
done

if [ "${WRITE:-0}" = 1 ]; then
  "$bench" work --write "$baseline" "${reports[@]}"
  exit 0
fi
if ! "$bench" work "$baseline" "${reports[@]}"; then
  cp "$baseline" "$work/new.json" 2>/dev/null || true
  "$bench" work --write "$work/new.json" "${reports[@]}" >/dev/null
  echo "$0: the work gate failed. If the change of the work is on purpose, put this text in $baseline:" >&2
  cat "$work/new.json" >&2
  exit 1
fi
