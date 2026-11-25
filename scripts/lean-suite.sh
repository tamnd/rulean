#!/usr/bin/env bash
# Runs the elab tests of the Lean test suite with two lean binaries and compares the results (spec 09.6.5).
#
# Usage: scripts/lean-suite.sh SRC CPP RULEAN OUT [JOBS]
#
# SRC is a checkout of the Lean source at v4.36.0 that has tests/elab and tests/elab_fail. CPP is the lean of the release, and RULEAN is the lean that scripts/lean-build.sh makes. The script writes the results to the directory OUT. JOBS is the number of tests that run at the same time, and the default is 4.
#
# Each test runs in its directory with the arguments of the run_test.sh of the directory. The script skips a test that has an init.sh, before.sh or serial file, because these tests need the harness of the suite. The two binaries must give the same output and the same exit code. If the test has an out.ignored file, only the exit codes must be the same. A test that runs for more than 600 seconds gets the exit code 142.
#
# OUT/results.txt has one line for each test: same, differ or skip, and the name of the test. The script prints the counts, and it exits with 1 if a test differs.

set -euo pipefail

if [ "$#" -lt 4 ] || [ "$#" -gt 5 ]; then
  echo "usage: $0 SRC CPP RULEAN OUT [JOBS]" >&2
  exit 2
fi
src="$(cd "$1" && pwd)"
cpp="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
rulean="$(cd "$(dirname "$3")" && pwd)/$(basename "$3")"
mkdir -p "$4"
out="$(cd "$4" && pwd)"
jobs="${5:-4}"
mkdir -p "$out/cpp" "$out/rulean"
: > "$out/results.txt"

# Runs the test $2 of the directory $1 with the two binaries and writes one line to results.txt.
run_one() {
  local dir="$1" f="$2" suite key extra=() k bin
  suite="$(basename "$dir")"
  key="$suite.$f"
  if [ -e "$dir/$f.init.sh" ] || [ -e "$dir/$f.before.sh" ] || [ -e "$dir/$f.serial" ]; then
    echo "skip $suite/$f" >> "$out/results.txt"
    return 0
  fi
  if [ "$suite" = elab ]; then
    extra=(-Dcompiler.postponeCompile=false)
  fi
  for k in cpp rulean; do
    if [ "$k" = cpp ]; then bin="$cpp"; else bin="$rulean"; fi
    local rc=0
    (cd "$dir" && perl -e 'alarm shift; exec @ARGV or die' 600 "$bin" --root=.. -DprintMessageEndPos=true -Dlinter.all=false -DElab.inServer=true ${extra[@]+"${extra[@]}"} "$f") > "$out/$k/$key.out" 2>&1 || rc=$?
    echo "$rc" > "$out/$k/$key.rc"
  done
  if ! cmp -s "$out/cpp/$key.rc" "$out/rulean/$key.rc"; then
    echo "differ $suite/$f" >> "$out/results.txt"
  elif [ ! -e "$dir/$f.out.ignored" ] && ! cmp -s "$out/cpp/$key.out" "$out/rulean/$key.out"; then
    echo "differ $suite/$f" >> "$out/results.txt"
  else
    echo "same $suite/$f" >> "$out/results.txt"
  fi
}
export -f run_one
export out cpp rulean

# The single quotes of the xargs command are correct: the arguments expand in the new bash, not here.
# shellcheck disable=SC2016
for suite in elab elab_fail; do
  dir="$src/tests/$suite"
  find "$dir" -maxdepth 1 -name '*.lean' -exec basename {} \; | LC_ALL=C sort | while IFS= read -r f; do
    printf '%s\0%s\0' "$dir" "$f"
  done
done | xargs -0 -n 2 -P "$jobs" bash -c 'run_one "$1" "$2"' _

same="$(grep -c '^same ' "$out/results.txt" || true)"
differ="$(grep -c '^differ ' "$out/results.txt" || true)"
skip="$(grep -c '^skip ' "$out/results.txt" || true)"
echo "lean-suite: $same same, $differ differ, $skip skipped"
if [ "$differ" -ne 0 ]; then
  grep '^differ ' "$out/results.txt" | LC_ALL=C sort
  exit 1
fi
