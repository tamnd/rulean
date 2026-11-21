#!/usr/bin/env bash
# Runs the Arena entry on every test of the Lean Kernel Arena and compares the verdict with the expected verdict (spec 11.3).
#
# Usage: scripts/arena-check.sh TESTS [RULEAN]
#
# TESTS is the tests directory of scripts/arena-fetch.sh or the output directory of scripts/arena-build.py. A test in good/ must exit with 0, and a test in bad/ must exit with 1. A test in docs/arena/either-v4.35.tsv must have the verdict of that file, and a test in either/ must be in that file. The script does not run a test with the pinned verdict either, because the official kernel did not give a verdict for it. RULEAN is the rulean binary, and the default is target/release/rulean. Each test has a limit of ARENA_TIMEOUT seconds (default 600) if the `timeout` command is installed. The script prints one line for each wrong verdict, and exits with 1 if there is one.

set -euo pipefail

if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
  echo "usage: $0 TESTS [RULEAN]" >&2
  exit 64
fi
tests="$1"
here="$(cd "$(dirname "$0")/.." && pwd)"
rulean="${2:-$here/target/release/rulean}"
limit="${ARENA_TIMEOUT:-600}"
either="$here/docs/arena/either-v4.35.tsv"

run=("$here/scripts/arena-run.sh")
if command -v timeout >/dev/null; then
  run=(timeout "$limit" "$here/scripts/arena-run.sh")
fi

total=0
wrong=0
skipped=0
declined=0
start=$(date +%s)
while IFS= read -r -d '' f; do
  rel="${f#"$tests/"}"
  name="${rel#*/}"
  name="${name%.ndjson}"
  case "$rel" in
    good/*) want=0 ;;
    bad/*) want=1 ;;
    either/*) want=none ;;
    *) continue ;;
  esac
  pinned="$(awk -F'\t' -v n="$name" '$1 == n { print $2 }' "$either")"
  case "$pinned" in
    accept) want=0 ;;
    reject) want=1 ;;
    either) want=any ;;
  esac
  if [ "$want" = none ]; then
    total=$((total + 1))
    wrong=$((wrong + 1))
    echo "WRONG $rel: the test has no pinned verdict in $either"
    continue
  fi
  if [ "$want" = any ]; then
    skipped=$((skipped + 1))
    continue
  fi
  total=$((total + 1))
  code=0
  "${run[@]}" "$f" "$rulean" >/dev/null 2>&1 || code=$?
  if [ "$code" = 2 ]; then
    declined=$((declined + 1))
  fi
  if [ "$code" != "$want" ]; then
    wrong=$((wrong + 1))
    echo "WRONG $rel: exit $code, expected $want"
  fi
done < <(find "$tests" -name '*.ndjson' -print0 | sort -z)

if [ "$total" -eq 0 ] && [ "$skipped" -eq 0 ] && [ "$wrong" -eq 0 ]; then
  echo "$0: no .ndjson files in $tests" >&2
  exit 1
fi
echo "$((total - wrong)) of $total Arena tests give the expected verdict, $declined decline, $skipped not run, $(($(date +%s) - start)) s"
test "$wrong" -eq 0
