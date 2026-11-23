#!/usr/bin/env bash
# Runs `rulean check` on every export of a tests directory one time with one thread and one time with `--threads N`, and compares the two reports (spec 08.3.4).
#
# Usage: scripts/arena-threads.sh TESTS [N] [RULEAN]
#
# TESTS is the tests directory of scripts/arena-fetch.sh or the output directory of scripts/arena-build.py. N is the thread count, and the default is 4. RULEAN is the rulean binary, and the default is target/release/rulean. The script compares the exit code, the verdict, the error, the rejected declaration, the summary without `wall_ms`, `steps` and `interns`, the quarantine and the pin mismatches. It does not compare the step and intern counts of the summary or the session and engine counts, because each worker has its own store and caches, so these counts depend on the job split. It prints one line for each export with a difference, and exits with 1 if there is one. Each export has a limit of ARENA_TIMEOUT seconds (default 600) if the `timeout` command is installed. The script does not run a test with the pinned verdict either in docs/arena/either-v4.35.tsv, as scripts/arena-check.sh does.

set -euo pipefail

if [ "$#" -lt 1 ] || [ "$#" -gt 3 ]; then
  echo "usage: $0 TESTS [N] [RULEAN]" >&2
  exit 64
fi
tests="$1"
threads="${2:-4}"
here="$(cd "$(dirname "$0")/.." && pwd)"
rulean="${3:-$here/target/release/rulean}"
limit="${ARENA_TIMEOUT:-600}"
either="$here/docs/arena/either-v4.35.tsv"

run=("$rulean")
if command -v timeout >/dev/null; then
  run=(timeout "$limit" "$rulean")
fi

# The fields of the report that must not change with the thread count.
fields='[.verdict, .error, .failed_decl, (.summary | del(.wall_ms, .steps, .interns)), .quarantine, .pin_mismatch]'

total=0
diff=0
skipped=0
while IFS= read -r -d '' f; do
  rel="${f#"$tests/"}"
  name="${rel#*/}"
  name="${name%.ndjson}"
  pinned="$(awk -F'\t' -v n="$name" '$1 == n { print $2 }' "$either")"
  if [ "$pinned" = either ]; then
    skipped=$((skipped + 1))
    continue
  fi
  total=$((total + 1))
  a=0
  b=0
  one="$("${run[@]}" check --format json "$f" 2>/dev/null)" || a=$?
  many="$("${run[@]}" check --format json --threads "$threads" "$f" 2>/dev/null)" || b=$?
  one="$a $(printf '%s' "$one" | jq -cS "$fields" 2>/dev/null || true)"
  many="$b $(printf '%s' "$many" | jq -cS "$fields" 2>/dev/null || true)"
  if [ "$one" != "$many" ]; then
    diff=$((diff + 1))
    echo "DIFFERENCE $rel"
    echo "  one thread: $one"
    echo "  $threads threads: $many"
  fi
done < <(find "$tests" -name '*.ndjson' -print0 | sort -z)

echo "$total exports, $diff with a difference, $skipped not run."
if [ "$diff" != 0 ]; then
  exit 1
fi
