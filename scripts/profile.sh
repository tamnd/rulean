#!/usr/bin/env bash
# An instruction profile of `rulean check` on a module of a Lean release (spec 08.7.3).
#
# Usage: scripts/profile.sh MODULE OUT [RULEAN]
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
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

mkdir -p "$out"
(cd "$work" && leanexport "$module" >"$work/export.ndjson")
echo "leanexport $module: $(wc -l <"$work/export.ndjson") lines"

case "$tool" in
  callgrind)
    valgrind --tool=callgrind --callgrind-out-file="$out/callgrind.out" \
      "$rulean" check --threads 1 --format text --report "$out/report.json" "$work/export.ndjson"
    callgrind_annotate --inclusive=yes "$out/callgrind.out" >"$out/inclusive.txt"
    callgrind_annotate --inclusive=no "$out/callgrind.out" >"$out/self.txt"
    ;;
  cachegrind)
    valgrind --tool=cachegrind --cache-sim=no --cachegrind-out-file="$out/cachegrind.out" \
      "$rulean" check --threads 1 --format text --report "$out/report.json" "$work/export.ndjson"
    cg_annotate "$out/cachegrind.out" >"$out/self.txt"
    ;;
  *)
    echo "$0: TOOL must be callgrind or cachegrind" >&2
    exit 64
    ;;
esac
head -40 "$out/self.txt"
