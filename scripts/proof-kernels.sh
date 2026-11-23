#!/usr/bin/env bash
# Exports the proof package and checks the export with three kernels: rulean, nanoda and con-leche (spec 10.9 and rule 5 of the release gate in 11.7).
#
# Usage: scripts/proof-kernels.sh OUT RULEAN NANODA CONLECHE
#
# Run the script after `lake build` in proof/. OUT is a new directory for the export and the logs. RULEAN is the rulean binary. NANODA is the `nanoda_bin` binary of nanoda_lib. CONLECHE is the `con-leche` binary. The script exports the module RuleanProof and all of its imports with `lake env leanexport`, so `leanexport` of the toolchain of proof/ must be on PATH through lake. Each kernel must accept the export. nanoda reads the export on standard input, with the configuration that the Lean Kernel Arena uses. con-leche runs in verified mode, which is the mode that its theorem is about. The script prints one line for each kernel, and exits with 1 if a kernel does not accept.

set -euo pipefail

if [ "$#" -ne 4 ]; then
  echo "usage: $0 OUT RULEAN NANODA CONLECHE" >&2
  exit 64
fi
out="$1"
rulean="$2"
nanoda="$3"
conleche="$4"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

mkdir -p "$out"
out="$(cd "$out" && pwd)"
export_file="$out/RuleanProof.ndjson"
(cd "$root/proof" && lake env leanexport RuleanProof >"$export_file")
echo "export: $(wc -l <"$export_file") lines, sha256 $(sha256sum "$export_file" | cut -d' ' -f1)"

cat >"$out/nanoda.json" <<'EOF'
{
  "use_stdin": true,
  "nat_extension": true,
  "string_extension": true,
  "unpermitted_axiom_hard_error": false,
  "unsafe_permit_all_axioms": true,
  "num_threads": 4,
  "stack_size_bytes": 268435456
}
EOF

failed=0
check() {
  local name="$1"
  shift
  local code=0
  local start
  start=$(date +%s)
  "$@" >"$out/$name.log" 2>&1 || code=$?
  if [ "$code" -eq 0 ]; then
    echo "$name: accept, $(($(date +%s) - start)) s"
  else
    echo "$name: exit $code, $(($(date +%s) - start)) s"
    tail -n 20 "$out/$name.log"
    failed=1
  fi
}

run_nanoda() {
  "$nanoda" "$out/nanoda.json" <"$export_file"
}

check rulean "$rulean" check --format text "$export_file"
check nanoda run_nanoda
check con-leche "$conleche" --verified --jobs=4 "$export_file"

if [ "$failed" -ne 0 ]; then
  echo "$0: a kernel did not accept the export of RuleanProof" >&2
  exit 1
fi
echo "proof-kernels: rulean, nanoda and con-leche accept the export of RuleanProof"
