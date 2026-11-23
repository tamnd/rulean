#!/usr/bin/env bash
# Runs the official kernel on each "either" test and compares its verdict with a pinned verdict file (spec 11.3.3).
#
# Usage: scripts/arena-official.sh TESTS PINNED [LEANCHECKER]
#
# TESTS is the output directory of scripts/arena-build.py. PINNED is a file such as docs/arena/either-v4.37.tsv. LEANCHECKER is the `leanchecker` binary of the Lean release of the profile, and the default is the `leanchecker` on PATH. The script runs `leanchecker --from-export` on each export in TESTS/either, as the Arena runs the official checker. Exit code 0 is accept, and each other exit code is reject. Each export has a limit of ARENA_TIMEOUT seconds (default 600) if the `timeout` command is installed, and a test that reaches the limit has the verdict either. The script prints one line for each verdict that is not the pinned verdict, and exits with 1 if there is one.

set -euo pipefail

if [ "$#" -lt 2 ] || [ "$#" -gt 3 ]; then
  echo "usage: $0 TESTS PINNED [LEANCHECKER]" >&2
  exit 64
fi
tests="$1"
pinned_file="$2"
checker="${3:-leanchecker}"
limit="${ARENA_TIMEOUT:-600}"

run=("$checker")
if command -v timeout >/dev/null; then
  run=(timeout "$limit" "$checker")
fi

total=0
wrong=0
while IFS= read -r -d '' f; do
  name="${f#"$tests/either/"}"
  name="${name%.ndjson}"
  pinned="$(awk -F'\t' -v n="$name" '$1 == n { print $2 }' "$pinned_file")"
  total=$((total + 1))
  code=0
  out="$("${run[@]}" --from-export "$f" 2>&1)" || code=$?
  case "$code" in
    0) got=accept ;;
    124) got=either ;;
    *) got=reject ;;
  esac
  echo "$name: $got (exit $code)"
  if [ "$got" != "$pinned" ]; then
    wrong=$((wrong + 1))
    echo "WRONG $name: the official kernel gives $got, and $pinned_file has ${pinned:-no verdict}"
    printf '%s\n' "$out" | tail -n 3
  fi
done < <(find "$tests/either" -name '*.ndjson' -print0 | sort -z)

if [ "$total" -eq 0 ]; then
  echo "$0: no .ndjson files in $tests/either" >&2
  exit 1
fi
echo "$((total - wrong)) of $total either tests give the pinned verdict of $pinned_file"
test "$wrong" -eq 0
