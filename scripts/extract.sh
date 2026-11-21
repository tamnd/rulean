#!/usr/bin/env bash
# Extracts the crates of the verified core to Lean with Charon and Aeneas (spec 10.3).
#
# Run it in the shell of flake.nix: nix develop --command scripts/extract.sh
#
# The output goes to _tmp/extract/. For each crate there is an LLBC file from Charon and the Lean files from Aeneas. The script fails if Charon or Aeneas fails on a crate.

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
work="$root/_tmp/extract"
crates=(rulean-store rulean-nat rulean-format rulean-core)

if [ "$#" -ne 0 ]; then
  echo "usage: $0" >&2
  exit 64
fi

for tool in cargo charon aeneas; do
  if ! command -v "$tool" >/dev/null; then
    echo "extract: $tool is not on PATH; run in the shell of flake.nix" >&2
    exit 1
  fi
done

# The cfg turns on the `aeneas::rename` attributes of the core crates. It goes to every crate of the build, so a crate and its users see the same names.
export RUSTFLAGS="${RUSTFLAGS:-} --cfg rulean_extract"

rm -rf "$work"
mkdir -p "$work/llbc" "$work/lean"

for crate in "${crates[@]}"; do
  name="${crate//-/_}"
  # The Lean namespace of a crate: rulean-core becomes Rulean.Generated.Core.
  part="${crate#rulean-}"
  module="$(printf '%s' "${part:0:1}" | tr '[:lower:]' '[:upper:]')${part:1}"
  llbc="$work/llbc/$name.llbc"

  echo "extract: charon on $crate"
  (cd "$root/crates/$crate" && charon cargo --preset=aeneas --dest-file "$llbc")
  if [ ! -f "$llbc" ]; then
    echo "extract: charon made no LLBC file for $crate" >&2
    exit 1
  fi

  echo "extract: aeneas on $crate"
  aeneas -backend lean -split-files -loops-to-rec -use-lean-modules false \
    -dest "$work/lean" -subdir "Rulean/Generated/$module" -namespace "Rulean.Generated.$module" \
    -no-progress-bar "$llbc"
done

echo "extract: the Lean files are in ${work#"$root"/}/lean"
find "$work/lean" -name '*.lean' | sort | sed "s|^$root/||"
