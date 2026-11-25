#!/usr/bin/env bash
# Builds the lean binary of Lean v4.36.0 with rulean as its kernel (spec 09.6.2).
#
# Usage: scripts/lean-build.sh OUT [TOOLCHAIN]
#
# TOOLCHAIN is the directory of the Lean v4.36.0 release. The default is the prefix of the lean on PATH. The script makes OUT/bin/lean. OUT/lib and OUT/include are links to the directories of TOOLCHAIN, so the new lean finds the oleans of the release.
#
# The release has the static libraries of Lean, and the C++ kernel is in libleancpp.a. The script makes a copy of libleancpp.a in which each kernel symbol has the suffix _cpp. Then it links the libraries of the release with the static library of rulean-ffi, which defines the kernel symbols. The functions of the C++ kernel stay in the binary with the new names, and no object refers to them. The release does not have the object of lean_main, so the script compiles src/util/shell.cpp and src/shell/lean.cpp of the Lean source at the commit of the release.
#
# The script works on macOS only. It needs git, a C++ compiler, cargo, llvm-objcopy and llvm-nm. Set CXX, OBJCOPY or NM to use a different tool.

set -euo pipefail

if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
  echo "usage: $0 OUT [TOOLCHAIN]" >&2
  exit 2
fi
if [ "$(uname -s)" != Darwin ]; then
  echo "lean-build: only macOS is supported" >&2
  exit 1
fi

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mkdir -p "$1"
out="$(cd "$1" && pwd)"
toolchain="${2:-$(lean --print-prefix)}"
toolchain="$(cd "$toolchain" && pwd -P)"
githash=611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9

got="$("$toolchain/bin/lean" --githash)"
if [ "$got" != "$githash" ]; then
  echo "lean-build: $toolchain is not Lean v4.36.0 (commit $got)" >&2
  exit 1
fi

# The nm of Xcode cannot read the bitcode objects of the Rust library, and an older LLVM cannot read them either. The first choice is the llvm-tools component of the Rust toolchain, which has the LLVM of rustc. The script uses the llvm-nm next to llvm-objcopy.
objcopy="${OBJCOPY:-}"
if [ -z "$objcopy" ]; then
  tools="$(cd "$root" && rustc --print sysroot)/lib/rustlib/$(cd "$root" && rustc -vV | sed -n 's/^host: //p')/bin"
  if [ -x "$tools/llvm-objcopy" ]; then
    objcopy="$tools/llvm-objcopy"
  elif command -v llvm-objcopy > /dev/null; then
    objcopy="$(command -v llvm-objcopy)"
  elif command -v brew > /dev/null && [ -x "$(brew --prefix llvm)/bin/llvm-objcopy" ]; then
    objcopy="$(brew --prefix llvm)/bin/llvm-objcopy"
  else
    echo "lean-build: llvm-objcopy is not found, run 'rustup component add llvm-tools' or set OBJCOPY" >&2
    exit 1
  fi
fi
llvm_nm="${NM:-$(dirname "$objcopy")/llvm-nm}"
if [ ! -x "$llvm_nm" ]; then
  echo "lean-build: $llvm_nm is not found, set NM" >&2
  exit 1
fi
cxx="${CXX:-c++}"

# The source files of the shell, at the commit of the release. The checkout has only the directories that the two files include.
src="$out/src/lean4"
if [ ! -d "$src/.git" ]; then
  git init -q "$src"
  git -C "$src" sparse-checkout set src/util src/runtime src/kernel src/library src/initialize src/include src/shell
  git -C "$src" fetch -q --depth 1 --filter=blob:none https://github.com/leanprover/lean4 "$githash"
  git -C "$src" checkout -q FETCH_HEAD
fi
if [ "$(git -C "$src" rev-parse HEAD)" != "$githash" ]; then
  echo "lean-build: $src is not at commit $githash" >&2
  exit 1
fi

build="$out/build"
mkdir -p "$build/gen" "$out/bin"
printf '#define LEAN_GITHASH "%s"\n' "$githash" > "$build/gen/githash.h"
flags=(-std=c++20 -O2 -DLEAN_MULTI_THREAD -DNDEBUG -I"$build/gen" -I"$src/src" -I"$toolchain/include" -I"$toolchain/include/lean")
"$cxx" "${flags[@]}" -c -o "$build/shell.o" "$src/src/util/shell.cpp"
"$cxx" "${flags[@]}" -c -o "$build/main.o" "$src/src/shell/lean.cpp"

# The static library of rulean-ffi with the kernel symbols.
(cd "$root" && cargo rustc --locked -q -p rulean-ffi --release --features export --crate-type staticlib)
rulean="${CARGO_TARGET_DIR:-$root/target}/release/librulean_ffi.a"

lib="$toolchain/lib/lean"
syms=(lean_add_decl lean_add_decl_without_checking lean_elab_add_decl lean_elab_add_decl_without_checking lean_kernel_is_def_eq lean_kernel_whnf lean_kernel_check)
rename=()
for s in "${syms[@]}"; do
  rename+=(--redefine-sym "_${s}=_${s}_cpp")
done
"$objcopy" "${rename[@]}" "$lib/libleancpp.a" "$build/libleancpp-rulean.a"

# Each kernel symbol must have the C++ function with the new name and the rulean function with the old name, and no object of Lean may refer to the new name.
"$llvm_nm" -g --defined-only "$build/libleancpp-rulean.a" | awk '{print $3}' | sort -u > "$build/cpp-defined.txt"
"$llvm_nm" -g --defined-only "$rulean" 2> /dev/null | awk '{print $3}' | sort -u > "$build/rulean-defined.txt"
"$llvm_nm" -u "$build/libleancpp-rulean.a" "$lib/libLean.a" "$lib/libStd.a" "$lib/libInit.a" | awk '{print $NF}' | sort -u > "$build/lean-undefined.txt"
for s in "${syms[@]}"; do
  if ! grep -qxF "_${s}_cpp" "$build/cpp-defined.txt"; then
    echo "lean-build: libleancpp.a does not define $s" >&2
    exit 1
  fi
  if grep -qxF "_${s}" "$build/cpp-defined.txt"; then
    echo "lean-build: the copy of libleancpp.a still defines $s" >&2
    exit 1
  fi
  if ! grep -qxF "_${s}" "$build/rulean-defined.txt"; then
    echo "lean-build: rulean-ffi does not define $s" >&2
    exit 1
  fi
  if grep -qxF "_${s}_cpp" "$build/lean-undefined.txt"; then
    echo "lean-build: an object of Lean refers to ${s}_cpp" >&2
    exit 1
  fi
done

"$cxx" -o "$out/bin/lean" "$build/main.o" "$build/shell.o" \
  "$lib/libLean.a" "$lib/libStd.a" "$lib/libInit.a" "$build/libleancpp-rulean.a" "$lib/libleanrt.a" "$lib/libcadical.a" \
  "$toolchain/lib/libgmp.a" "$toolchain/lib/libuv.a" "$toolchain/lib/libssl.a" "$toolchain/lib/libcrypto.a" \
  "$rulean" -Wl,-export_dynamic -lc++
ln -sfn "$toolchain/lib" "$out/lib"
ln -sfn "$toolchain/include" "$out/include"
echo "lean-build: $out/bin/lean has rulean as its kernel"
