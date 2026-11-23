#!/usr/bin/env bash
# Cross-validates the .olean reader with lean4export on modules of a Lean release (spec 07.3.6).
#
# Usage: scripts/olean-xval.sh LIB [RULEAN [COMPARE]]
#
# LIB is the directory lib/lean of the release. RULEAN is the rulean binary, and the default is target/release/rulean. COMPARE is the example olean_compare of rulean-olean, and the default is target/release/examples/olean_compare. The `lean` and `leanexport` of the same release must be on PATH. MODULES is the list of modules, and the default is `Init Std`. For each module, the script does three things. It exports the module to NDJSON with leanexport, and requires that `rulean check` accepts the export. It requires that `rulean olean` accepts the oleans of the module. It requires that olean_compare finds each declaration of the export in the oleans, with the same content.
#
# Set NO_PROFILE=1 for a release that rulean has no profile for yet. Then `rulean check` must decline the export with `unsupported-version` and the exit code 2 (spec 05.2), and `rulean olean --parse-only` must load the oleans. The comparison with olean_compare is the same.

set -euo pipefail

if [ "$#" -lt 1 ] || [ "$#" -gt 3 ]; then
  echo "usage: $0 LIB [RULEAN [COMPARE]]" >&2
  exit 64
fi
here="$(cd "$(dirname "$0")/.." && pwd)"
lib="$1"
rulean="${2:-$here/target/release/rulean}"
compare="${3:-$here/target/release/examples/olean_compare}"
read -r -a modules <<<"${MODULES:-Init Std}"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

for m in "${modules[@]}"; do
  (cd "$work" && leanexport "$m" >"$work/$m.ndjson")
  echo "leanexport $m: $(wc -l <"$work/$m.ndjson") lines"
  if [ "${NO_PROFILE:-0}" = 1 ]; then
    rc=0
    "$rulean" check --format text "$work/$m.ndjson" >"$work/check.txt" 2>&1 || rc=$?
    cat "$work/check.txt"
    if [ "$rc" -ne 2 ] || ! grep -q 'unsupported-version' "$work/check.txt"; then
      echo "$0: rulean check must decline $m with unsupported-version and the exit code 2, the exit code is $rc" >&2
      exit 1
    fi
    "$rulean" olean --parse-only --path "$lib" "$m"
  else
    "$rulean" check --format text "$work/$m.ndjson"
    "$rulean" olean --format text --path "$lib" "$m"
  fi
  if ! "$compare" "$work/$m.ndjson" "$lib" "$m" >"$work/compare.txt"; then
    cat "$work/compare.txt"
    echo "$0: the .olean reader and lean4export do not agree on $m" >&2
    exit 1
  fi
  tail -n 1 "$work/compare.txt"
  rm -f "$work/$m.ndjson"
  echo "the .olean reader and lean4export give the same declarations of $m"
done
