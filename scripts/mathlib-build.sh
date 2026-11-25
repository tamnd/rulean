#!/usr/bin/env bash
# Builds Mathlib at the tag v4.36.0 with a lean that has rulean as its kernel (spec 09.6 and 11.3.1).
#
# Usage: scripts/mathlib-build.sh WORK TOOLCHAIN MINUTES
#
# TOOLCHAIN is a copy of the Lean v4.36.0 release in which bin/lean is the lean of scripts/lean-build.sh. The lake of the release runs the lean of its own directory, so each module of Mathlib and of its packages gets the kernel of that lean. The oleans of Init, Std and Lean come from the release. The script does not run `lake exe cache get`, so lake builds each module from its source.
#
# WORK/mathlib is the project. If it does not exist, the script clones it. If it exists, lake continues the build of an earlier run, so a build that is longer than one CI job can use more than one job. The script stops lake after MINUTES minutes.
#
# The script writes WORK/out/status with one word: done if lake built all the modules, timeout if the time limit stopped lake, and failed if lake finished with an error. It also writes the output of lake to WORK/out/lake.log and the count of built modules to WORK/out/built. The exit code is 0 for done and timeout, and 1 for failed.

set -euo pipefail

if [ "$#" -ne 3 ]; then
  echo "usage: $0 WORK TOOLCHAIN MINUTES" >&2
  exit 64
fi
work="$1"
toolchain="$2"
minutes="$3"
url=https://github.com/leanprover-community/mathlib4
rev=fc4f59e577feb1a4956671bc04ac18aaaf8cd842

mkdir -p "$work/out"
if [ ! -d "$work/mathlib/.git" ]; then
  git init -q "$work/mathlib"
  git -C "$work/mathlib" fetch -q --depth 1 "$url" "$rev"
  git -C "$work/mathlib" checkout -q FETCH_HEAD
fi
if [ "$(git -C "$work/mathlib" rev-parse HEAD)" != "$rev" ]; then
  echo "mathlib-build: $work/mathlib is not at commit $rev" >&2
  exit 1
fi

export PATH="$toolchain/bin:$PATH"
lean --version

status=0
(cd "$work/mathlib" && timeout "${minutes}m" lake build Mathlib) >> "$work/out/lake.log" 2>&1 || status=$?
case "$status" in
  0) result="done" ;;
  124) result=timeout ;;
  *) result=failed ;;
esac
echo "$result" > "$work/out/status"
find "$work/mathlib/.lake" -name '*.olean' | wc -l | tr -d ' ' > "$work/out/built"
echo "mathlib-build: $result after $minutes minutes or less, lake exit code $status, $(cat "$work/out/built") oleans"
[ "$result" != failed ]
