#!/usr/bin/env bash
# Downloads the test tarball and the results of the Lean Kernel Arena, for the baseline of spec 08.7.1.
#
# Usage: scripts/arena-fetch.sh DIR
#
# DIR/tests gets the tests in the good/ and bad/ layout. DIR/results.json gets the published results. The Arena builds both files again on each deploy, so the script checks the SHA-256 of each test against the hash in results.json. It deletes a test whose hash is different, because its Arena numbers are for another export. DIR/sources.txt records the hashes of the two downloads.

set -euo pipefail

base_url="https://arena.lean-lang.org"

if [ "$#" -ne 1 ]; then
  echo "usage: $0 DIR" >&2
  exit 64
fi
dir="$1"

for tool in curl jq tar; do
  if ! command -v "$tool" >/dev/null; then
    echo "$0: $tool is not installed" >&2
    exit 1
  fi
done

if command -v sha256sum >/dev/null; then
  sha256() { sha256sum "$1" | cut -d' ' -f1; }
else
  sha256() { shasum -a 256 "$1" | cut -d' ' -f1; }
fi

rm -rf "$dir"
mkdir -p "$dir/tests"
curl -sSfL --retry 3 -o "$dir/tests.tar.gz" "$base_url/lean-arena-tests.tar.gz"
curl -sSfL --retry 3 -o "$dir/results.json" "$base_url/results.json"
tar -xzf "$dir/tests.tar.gz" -C "$dir/tests"

{
  echo "tarball $(sha256 "$dir/tests.tar.gz")"
  echo "results $(sha256 "$dir/results.json")"
  jq -r '"arena \(.meta.git_revision) \(.meta.timestamp)"' "$dir/results.json"
} >"$dir/sources.txt"

jq -r '.tests[] | select(.sha256 != null) | "\(.name)\t\(.sha256)"' "$dir/results.json" >"$dir/hashes.tsv"

kept=0
dropped=0
while IFS= read -r -d '' file; do
  rel="${file#"$dir/tests/"}"
  name="${rel#*/}"
  name="${name%.ndjson}"
  want="$(awk -F'\t' -v n="$name" '$1 == n { print $2 }' "$dir/hashes.tsv")"
  if [ -n "$want" ] && [ "$(sha256 "$file")" = "$want" ]; then
    kept=$((kept + 1))
  else
    echo "$0: $name: the export is not the one of results.json, so it is not used" >&2
    rm "$file"
    dropped=$((dropped + 1))
  fi
done < <(find "$dir/tests" -name '*.ndjson' -print0)

echo "kept $kept tests, dropped $dropped" | tee -a "$dir/sources.txt"
if [ "$kept" -eq 0 ]; then
  exit 1
fi
