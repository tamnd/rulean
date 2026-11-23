#!/usr/bin/env bash
# The corpus run of spec 11.2 and 07.3.6: a large test of the Lean Kernel Arena, checked from the export and from the oleans.
#
# Usage: scripts/corpus.sh TEST STEP WORK
#
# TEST is mathlib, cslib or cedar. These are the large tests of the Arena that use Lean v4.36.0. The test navier-stokes-euler uses Lean 4.34.0-rc2, which is out of scope (spec 02.5). WORK is the work directory. STEP is one of these steps, in this order:
#
# - fetch: gets the project at the commit of the Arena test, does the pre-build step of the Arena test, and builds the module with `lake build`, as the Arena does.
# - export: exports the module with leanexport into WORK/export.ndjson, and compares its SHA-256 digest with the digest of the Arena export.
# - check: runs `rulean check` on the export, with a JSON report in WORK/out/check.json.
# - olean: runs `rulean olean` on the oleans of the module, with a JSON report in WORK/out/olean.json.
# - compare: runs olean_compare on the export and the oleans, with the output in WORK/out/compare.txt.
#
# The `lean`, `lake` and `leanexport` of Lean v4.36.0 must be on PATH. RULEAN is the rulean binary, and the default is target/release/rulean. COMPARE is the example olean_compare of rulean-olean, and the default is target/release/examples/olean_compare. THREADS is the number of threads of the checks, and the default is 1. Each worker has its own copy of the store, so more threads need more memory. The steps check, olean and compare write the output of GNU time into WORK/out, so the peak memory is in the output.

set -euo pipefail

if [ "$#" -ne 3 ]; then
  echo "usage: $0 mathlib|cslib|cedar fetch|export|check|olean|compare WORK" >&2
  exit 64
fi

# The Arena tests at dbb57ce5e5b03608f491930c995a651eadd3cd0f of leanprover/lean-kernel-arena, and the SHA-256 digests of the Arena exports.
case "$1" in
  mathlib)
    url=https://github.com/leanprover-community/mathlib4
    rev=fc4f59e577feb1a4956671bc04ac18aaaf8cd842
    module=Mathlib
    arena_sha256=f749dfd084fc0727d107c7aaded7d492cebfc0b517cfaa7337d8a7578a6c0dec
    ;;
  cslib)
    url=https://github.com/leanprover/cslib
    rev=e60b7760d6300ca790bc6a9adf6ded47f5773953
    module=Cslib
    arena_sha256=09d1225013197983fe16b7078f6475707ce13da8f7e92d7c41ab1bc354522567
    ;;
  cedar)
    url=https://github.com/cedar-policy/cedar-spec
    rev=326d93c24490c90607a3e257318e9c6a049c8116
    module=Cedar
    arena_sha256=787b0e0790186f14f79f450896650fe120cd64efcdb4ca9220667612519f0a79
    ;;
  *)
    echo "$0: unknown test $1" >&2
    exit 64
    ;;
esac

# The pre-build step of the Arena test (the key `pre-build` of the test file).
pre_build() {
  case "$1" in
    mathlib | cslib)
      lake exe cache get
      ;;
    cedar)
      # The Lean project is in the directory cedar-lean. The Arena also removes .git, and this script keeps it for the log.
      shopt -s dotglob
      find . -mindepth 1 -maxdepth 1 ! -name cedar-lean ! -name .git -exec rm -rf {} +
      mv cedar-lean/* .
      rmdir cedar-lean
      ;;
  esac
}

here="$(cd "$(dirname "$0")/.." && pwd)"
test="$1"
step="$2"
mkdir -p "$3/out"
work="$(cd "$3" && pwd)"
rulean="${RULEAN:-$here/target/release/rulean}"
compare="${COMPARE:-$here/target/release/examples/olean_compare}"
threads="${THREADS:-1}"
src="$work/src"
export="$work/export.ndjson"

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
      git -C "$src" remote add origin "$url"
    fi
    git -C "$src" fetch -q --depth 1 origin "$rev"
    git -C "$src" checkout -q FETCH_HEAD
    (cd "$src" && pre_build "$test")
    (cd "$src" && lake build "$module")
    echo "$test at $(git -C "$src" rev-parse HEAD), toolchain $(cat "$src/lean-toolchain")"
    du -sh "$src/.lake"
    ;;
  export)
    (cd "$src" && lake env leanexport "$module") >"$export"
    echo "leanexport $module: $(wc -l <"$export") lines, $(stat -c %s "$export") bytes"
    got="$(sha256sum "$export" | cut -d ' ' -f 1)"
    echo "$got" >"$work/out/export.sha256"
    if [ "$got" = "$arena_sha256" ]; then
      echo "the export has the SHA-256 digest of the Arena export"
    else
      echo "the export does not have the SHA-256 digest of the Arena export: $got, Arena $arena_sha256"
    fi
    ;;
  check)
    /usr/bin/time -v -o "$work/out/check.time" "$rulean" check --threads "$threads" --format text --report "$work/out/check.json" "$export"
    ;;
  olean)
    LEAN_PATH="$(search_path)" /usr/bin/time -v -o "$work/out/olean.time" "$rulean" olean --threads "$threads" --format text --report "$work/out/olean.json" "$module"
    ;;
  compare)
    if ! /usr/bin/time -v -o "$work/out/compare.time" "$compare" "$export" "$(search_path)" "$module" >"$work/out/compare.txt"; then
      cat "$work/out/compare.txt"
      echo "$0: the .olean reader and lean4export do not agree on $module" >&2
      exit 1
    fi
    tail -n 1 "$work/out/compare.txt"
    ;;
  *)
    echo "$0: unknown step $step" >&2
    exit 64
    ;;
esac
