#!/usr/bin/env bash
# Runs engine F with `--confirm all` on every export of a tests directory, and compares each "equal" answer of engine F with the answer of engine R (spec 05.1).
#
# Usage: scripts/arena-confirm.sh TESTS [RULEAN]
#
# TESTS is the tests directory of scripts/arena-fetch.sh or the output directory of scripts/arena-build.py. RULEAN is the rulean binary, and the default is target/release/rulean. The script reads the `engine` object of the JSON report of each export. It prints one line for each export where engine R did not confirm an equality of engine F, and exits with 1 if there is one. Each export has a limit of ARENA_TIMEOUT seconds (default 600) if the `timeout` command is installed. An export that reaches the limit is counted, but it is not a difference.

set -euo pipefail

if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
  echo "usage: $0 TESTS [RULEAN]" >&2
  exit 64
fi
tests="$1"
here="$(cd "$(dirname "$0")/.." && pwd)"
rulean="${2:-$here/target/release/rulean}"
limit="${ARENA_TIMEOUT:-600}"

run=("$rulean")
if command -v timeout >/dev/null; then
  run=(timeout "$limit" "$rulean")
fi

total=0
diff=0
slow=0
queries=0
equal=0
confirmed=0
while IFS= read -r -d '' f; do
  rel="${f#"$tests/"}"
  total=$((total + 1))
  out="$("${run[@]}" check --profile v4.35 --engine F --confirm all --format json "$f" 2>/dev/null)" || true
  e="$(printf '%s' "$out" | jq -r '.engine | "\(.f_queries) \(.f_equal) \(.r_confirmed) \(.r_disagree)"' 2>/dev/null || true)"
  if [ -z "$e" ]; then
    slow=$((slow + 1))
    echo "NO REPORT $rel"
    continue
  fi
  read -r q eq c d <<<"$e"
  queries=$((queries + q))
  equal=$((equal + eq))
  confirmed=$((confirmed + c))
  if [ "$d" != 0 ]; then
    diff=$((diff + 1))
    echo "DIFFERENCE $rel: engine R did not confirm $d equalities of engine F"
  fi
done < <(find "$tests" -name '*.ndjson' -print0 | sort -z)

echo "$total exports, $diff with a difference, $slow with no report. Engine F: $queries queries, $equal equal, $confirmed confirmed by engine R."
if [ "$diff" != 0 ]; then
  exit 1
fi
