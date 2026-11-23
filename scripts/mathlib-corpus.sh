#!/usr/bin/env bash
# The Mathlib corpus run (spec 11.2 and 07.3.6): the Mathlib test of the Lean Kernel Arena, checked from the export and from the oleans.
#
# Usage: scripts/mathlib-corpus.sh STEP WORK
#
# WORK is the work directory. STEP is one of these steps, in this order:
#
# - fetch: gets mathlib4 at the commit of the Arena test and its oleans with `lake exe cache get`.
# - export: exports the module Mathlib with leanexport into WORK/Mathlib.ndjson, and compares its SHA-256 digest with the digest of the Arena export.
# - check: runs `rulean check` on the export, with a JSON report in WORK/out/check.json.
# - olean: runs `rulean olean` on the oleans of Mathlib, with a JSON report in WORK/out/olean.json.
# - compare: runs olean_compare on the export and the oleans, with the output in WORK/out/compare.txt.
#
# The `lean`, `lake` and `leanexport` of Lean v4.36.0 must be on PATH. RULEAN is the rulean binary, and the default is target/release/rulean. COMPARE is the example olean_compare of rulean-olean, and the default is target/release/examples/olean_compare. THREADS is the number of threads of the checks, and the default is 1. Each worker has its own copy of the store, so more threads need more memory. The steps check and olean write the output of GNU time into WORK/out, so the peak memory is in the output.

set -euo pipefail

# The Mathlib test of the Arena (tests/mathlib.yaml at dbb57ce5e5b03608f491930c995a651eadd3cd0f).
rev=fc4f59e577feb1a4956671bc04ac18aaaf8cd842
arena_sha256=f749dfd084fc0727d107c7aaded7d492cebfc0b517cfaa7337d8a7578a6c0dec

if [ "$#" -ne 2 ]; then
  echo "usage: $0 fetch|export|check|olean|compare WORK" >&2
  exit 64
fi
here="$(cd "$(dirname "$0")/.." && pwd)"
step="$1"
mkdir -p "$2/out"
work="$(cd "$2" && pwd)"
rulean="${RULEAN:-$here/target/release/rulean}"
compare="${COMPARE:-$here/target/release/examples/olean_compare}"
threads="${THREADS:-1}"
src="$work/mathlib4"

# The search path of the oleans: the directories of the Lake workspace, and then lib/lean of the Lean release.
search_path() {
  local lib
  lib="$(lean --print-prefix)/lib/lean"
  (cd "$src" && lake env printenv LEAN_PATH | tr -d '\n')
  printf ':%s' "$lib"
}

case "$step" in
  fetch)
    if [ ! -d "$src/.git" ]; then
      git init -q "$src"
      git -C "$src" remote add origin https://github.com/leanprover-community/mathlib4
    fi
    git -C "$src" fetch -q --depth 1 origin "$rev"
    git -C "$src" checkout -q FETCH_HEAD
    echo "mathlib4 at $(git -C "$src" rev-parse HEAD), toolchain $(cat "$src/lean-toolchain")"
    (cd "$src" && lake exe cache get)
    du -sh "$src/.lake"
    ;;
  export)
    (cd "$src" && lake env leanexport Mathlib) >"$work/Mathlib.ndjson"
    echo "leanexport Mathlib: $(wc -l <"$work/Mathlib.ndjson") lines, $(stat -c %s "$work/Mathlib.ndjson") bytes"
    got="$(sha256sum "$work/Mathlib.ndjson" | cut -d ' ' -f 1)"
    echo "$got" >"$work/out/export.sha256"
    if [ "$got" = "$arena_sha256" ]; then
      echo "the export has the SHA-256 digest of the Arena export"
    else
      echo "the export does not have the SHA-256 digest of the Arena export: $got, Arena $arena_sha256"
    fi
    ;;
  check)
    /usr/bin/time -v -o "$work/out/check.time" "$rulean" check --threads "$threads" --format text --report "$work/out/check.json" "$work/Mathlib.ndjson"
    ;;
  olean)
    LEAN_PATH="$(search_path)" /usr/bin/time -v -o "$work/out/olean.time" "$rulean" olean --threads "$threads" --format text --report "$work/out/olean.json" Mathlib
    ;;
  compare)
    if ! /usr/bin/time -v -o "$work/out/compare.time" "$compare" "$work/Mathlib.ndjson" "$(search_path)" Mathlib >"$work/out/compare.txt"; then
      cat "$work/out/compare.txt"
      echo "$0: the .olean reader and lean4export do not agree on Mathlib" >&2
      exit 1
    fi
    tail -n 1 "$work/out/compare.txt"
    ;;
  *)
    echo "$0: unknown step $step" >&2
    exit 64
    ;;
esac
