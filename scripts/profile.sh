#!/usr/bin/env bash
# An instruction profile of `rulean check` on a module of a Lean release (spec 08.7.3).
#
# Usage: scripts/profile.sh MODULE OUT [RULEAN]
#
# MODULE is a module of the release, or an Arena test such as perf/magma-list-deep-n21. For an Arena test, ARENA_DIR must be the directory of scripts/arena-fetch.sh, and the script uses the export of the test and does not run leanexport. ENGINE selects the engine of `rulean check`, R by default. ENGINE=parse runs `rulean check --parse-only`, which parses the export and checks nothing.
#
# The script exports MODULE with leanexport, runs `rulean check` with one thread under valgrind, and writes the profile and its annotation to the directory OUT. The `leanexport` of the release must be on PATH. RULEAN is the rulean binary, and the default is target/release/rulean. TOOL selects the valgrind tool: callgrind (the default) gives the cost of each function with the cost of the functions that it calls, and cachegrind is about two times faster and gives only the cost of each function. The counts are instructions, as the Arena counts, but the machine is not the Arena machine.

set -euo pipefail

if [ "$#" -lt 2 ] || [ "$#" -gt 3 ]; then
  echo "usage: $0 MODULE OUT [RULEAN]" >&2
  exit 64
fi
here="$(cd "$(dirname "$0")/.." && pwd)"
module="$1"
out="$2"
rulean="${3:-$here/target/release/rulean}"
tool="${TOOL:-callgrind}"
engine="${ENGINE:-R}"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

if [ "$engine" = parse ]; then
  mode=(--parse-only)
else
  mode=(--engine "$engine")
fi

mkdir -p "$out"
case "$module" in
  */*)
    input=""
    for kind in good bad; do
      if [ -f "${ARENA_DIR:?ARENA_DIR must be set for an Arena test}/tests/$kind/$module.ndjson" ]; then
        input="$ARENA_DIR/tests/$kind/$module.ndjson"
      fi
    done
    if [ -z "$input" ]; then
      echo "$0: no Arena test $module in $ARENA_DIR/tests" >&2
      exit 64
    fi
    echo "Arena test $module: $(wc -l <"$input") lines"
    ;;
  *)
    input="$work/export.ndjson"
    (cd "$work" && leanexport "$module" >"$input")
    echo "leanexport $module: $(wc -l <"$input") lines"
    ;;
esac

case "$tool" in
  callgrind)
    valgrind --tool=callgrind --callgrind-out-file="$out/callgrind.out" \
      "$rulean" check --threads 1 "${mode[@]}" --format text --report "$out/report.json" "$input"
    callgrind_annotate --inclusive=yes "$out/callgrind.out" >"$out/inclusive.txt"
    callgrind_annotate --inclusive=no "$out/callgrind.out" >"$out/self.txt"
    ;;
  cachegrind)
    valgrind --tool=cachegrind --cache-sim=no --cachegrind-out-file="$out/cachegrind.out" \
      "$rulean" check --threads 1 "${mode[@]}" --format text --report "$out/report.json" "$input"
    cg_annotate "$out/cachegrind.out" >"$out/self.txt"
    ;;
  *)
    echo "$0: TOOL must be callgrind or cachegrind" >&2
    exit 64
    ;;
esac
head -40 "$out/self.txt"
