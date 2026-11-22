#!/usr/bin/env bash
# Runs rulean as an external kernel of `lake comparator` on the project in tests/lake (spec 09.5).
#
# Usage: scripts/lake-comparator.sh [RULEAN]
#
# RULEAN is the rulean binary, and the default is target/release/rulean. The `lake` and `leanexport` of the toolchain in tests/lake/lean-toolchain must be on PATH. The script does three things. It runs `lake comparator` with the `external_kernels` entry of tests/lake/comparator.json, and requires that rulean accepts the solution. It exports the theorem `uses_sorry` and requires that `rulean check --axioms std` gives exit code 5 on it. It requires that `rulean check` with no `--axioms` accepts the same export. `lake comparator` needs `bwrap` on Linux. Set LAKE_NO_SANDBOX=1 to run it with `--inadvisably-no-sandbox`, for example on macOS, where there is no `bwrap`.

set -euo pipefail

if [ "$#" -gt 1 ]; then
  echo "usage: $0 [RULEAN]" >&2
  exit 64
fi
here="$(cd "$(dirname "$0")/.." && pwd)"
rulean="$(cd "$(dirname "${1:-$here/target/release/rulean}")" && pwd)/$(basename "${1:-$here/target/release/rulean}")"
project="$here/tests/lake"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# comparator.json names the kernel `rulean`, and lake finds it on PATH.
mkdir -p "$work/bin"
ln -s "$rulean" "$work/bin/rulean"
export PATH="$work/bin:$PATH"

flags=()
if [ "${LAKE_NO_SANDBOX:-0}" = 1 ]; then
  flags=(--inadvisably-no-sandbox)
fi

cd "$project"
lake build
code=0
lake comparator ${flags[@]+"${flags[@]}"} >"$work/comparator.txt" 2>&1 || code=$?
cat "$work/comparator.txt"
if [ "$code" != 0 ]; then
  echo "$0: lake comparator exited with $code" >&2
  exit 1
fi
if ! grep -q '^rulean kernel accepts the solution$' "$work/comparator.txt"; then
  echo "$0: lake comparator did not run rulean" >&2
  exit 1
fi

lake env leanexport Sorry -- uses_sorry >"$work/sorry.ndjson"
code=0
rulean check --format text --axioms std "$work/sorry.ndjson" || code=$?
if [ "$code" != 5 ]; then
  echo "$0: rulean check --axioms std exited with $code on uses_sorry, expected 5" >&2
  exit 1
fi
rulean check --format text "$work/sorry.ndjson"
echo "rulean works as an external kernel of lake comparator"
