#!/usr/bin/env bash
# Runs `rulean check --parse-only` on every test of the Lean Kernel Arena. All tests must parse: the bad tests are bad for the type checker, not for the parser.
#
# Usage: scripts/arena-parse.sh TESTS [RULEAN]
#
# TESTS is the tests directory of scripts/arena-fetch.sh. RULEAN is the rulean binary, and the default is target/release/rulean. The script prints one line for each test that does not parse, and exits with 1 if there is one.

set -euo pipefail

if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
  echo "usage: $0 TESTS [RULEAN]" >&2
  exit 64
fi
tests="$1"
rulean="${2:-target/release/rulean}"

total=0
failed=0
while IFS= read -r -d '' f; do
  total=$((total + 1))
  if ! out=$("$rulean" check --parse-only "$f" 2>&1); then
    failed=$((failed + 1))
    echo "FAIL $out"
  fi
done < <(find "$tests" -name '*.ndjson' -print0 | sort -z)

if [ "$total" -eq 0 ]; then
  echo "$0: no .ndjson files in $tests" >&2
  exit 1
fi
echo "$((total - failed)) of $total Arena tests parse"
test "$failed" -eq 0
