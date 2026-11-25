#!/usr/bin/env bash
# Builds the lean binary of Lean v4.36.0 with rulean as its kernel (spec 09.6.2).
#
# Usage: scripts/lean-build.sh [--dual] OUT [TOOLCHAIN]
#
# TOOLCHAIN is the directory of the Lean v4.36.0 release. The default is the prefix of the lean on PATH. The script makes OUT/bin/lean. OUT/lib and OUT/include are links to the directories of TOOLCHAIN, so the new lean finds the oleans of the release. OUT/bin/cadical is a link to the cadical of TOOLCHAIN.
#
# The release has the static libraries of Lean, and the C++ kernel is in libleancpp.a. The script makes a copy of libleancpp.a in which each kernel symbol has the suffix _cpp. Then it links the libraries of the release with the static library of rulean-ffi, which defines the kernel symbols. The functions of the C++ kernel stay in the binary with the new names, and no object refers to them. The release does not have the object of lean_main, so the script compiles src/util/shell.cpp and src/shell/lean.cpp of the Lean source at the commit of the release.
#
# With --dual, the script makes the dual-kernel build of spec 11.3. The static library of rulean-ffi then has the feature dual: each kernel symbol also calls the C++ function with the suffix _cpp and compares the two results. If they differ, the process writes the difference to the standard error and stops. The binary exports the _cpp functions, and rulean finds them when the program runs.
#
# The script works on macOS and on Linux. It needs git, a C++ compiler, cargo, llvm-objcopy and llvm-nm. Set CXX, OBJCOPY or NM to use a different tool. The release of Lean uses libc++ on the two systems. On Linux, the release has the static libraries of libc++ but not its headers, so the default compiler is clang++ with -stdlib=libc++, and the headers of libc++ must be installed (the Ubuntu package libc++-dev).

set -euo pipefail

features="export"
if [ "${1:-}" = --dual ]; then
  features="dual"
  shift
fi
if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
  echo "usage: $0 [--dual] OUT [TOOLCHAIN]" >&2
  exit 2
fi
# The C names of Mach-O symbols have the prefix _, and the C names of ELF symbols have no prefix.
os="$(uname -s)"
case "$os" in
  Darwin) p=_ ;;
  Linux) p= ;;
  *)
    echo "lean-build: only macOS and Linux are supported" >&2
    exit 1
    ;;
esac

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
if [ "$os" = Darwin ]; then
  cxx="${CXX:-c++}"
  stdlib=()
else
  cxx="${CXX:-clang++}"
  stdlib=(-stdlib=libc++)
fi

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
flags=(${stdlib[@]+"${stdlib[@]}"} -std=c++20 -O2 -DLEAN_MULTI_THREAD -DNDEBUG -I"$build/gen" -I"$src/src" -I"$toolchain/include" -I"$toolchain/include/lean")
"$cxx" "${flags[@]}" -c -o "$build/shell.o" "$src/src/util/shell.cpp"
"$cxx" "${flags[@]}" -c -o "$build/main.o" "$src/src/shell/lean.cpp"

# The static library of rulean-ffi with the kernel symbols.
(cd "$root" && cargo rustc --locked -q -p rulean-ffi --release --features "$features" --crate-type staticlib)
rulean="${CARGO_TARGET_DIR:-$root/target}/release/librulean_ffi.a"

lib="$toolchain/lib/lean"
syms=(lean_add_decl lean_add_decl_without_checking lean_elab_add_decl lean_elab_add_decl_without_checking lean_kernel_is_def_eq lean_kernel_whnf lean_kernel_check)
rename=()
for s in "${syms[@]}"; do
  rename+=(--redefine-sym "${p}${s}=${p}${s}_cpp")
done
"$objcopy" "${rename[@]}" "$lib/libleancpp.a" "$build/libleancpp-rulean.a"

# Each kernel symbol must have the C++ function with the new name and the rulean function with the old name, and no object of Lean may refer to the new name.
"$llvm_nm" -g --defined-only "$build/libleancpp-rulean.a" | awk '{print $3}' | sort -u > "$build/cpp-defined.txt"
"$llvm_nm" -g --defined-only "$rulean" 2> /dev/null | awk '{print $3}' | sort -u > "$build/rulean-defined.txt"
"$llvm_nm" -u "$build/libleancpp-rulean.a" "$lib/libLean.a" "$lib/libStd.a" "$lib/libInit.a" | awk '{print $NF}' | sort -u > "$build/lean-undefined.txt"
for s in "${syms[@]}"; do
  if ! grep -qxF "${p}${s}_cpp" "$build/cpp-defined.txt"; then
    echo "lean-build: libleancpp.a does not define $s" >&2
    exit 1
  fi
  if grep -qxF "${p}${s}" "$build/cpp-defined.txt"; then
    echo "lean-build: the copy of libleancpp.a still defines $s" >&2
    exit 1
  fi
  if ! grep -qxF "${p}${s}" "$build/rulean-defined.txt"; then
    echo "lean-build: rulean-ffi does not define $s" >&2
    exit 1
  fi
  if grep -qxF "${p}${s}_cpp" "$build/lean-undefined.txt"; then
    echo "lean-build: an object of Lean refers to ${s}_cpp" >&2
    exit 1
  fi
done

# The order of the libraries is the order of the release (src/CMakeLists.txt of Lean). The linker of macOS finds the symbols of all the libraries. The linker of Linux reads each library one time, so the libraries that refer to each other are in a group, and the static library of rulean-ffi is in the same group as libLean.a, which refers to the kernel symbols.
libs=("$lib/libcadical.a")
for l in libgmp.a libuv.a libssl.a libcrypto.a; do
  if [ -f "$toolchain/lib/$l" ]; then
    libs+=("$toolchain/lib/$l")
  elif [ -f "$lib/$l" ]; then
    libs+=("$lib/$l")
  fi
done
if [ "$os" = Darwin ]; then
  "$cxx" -o "$out/bin/lean" "$build/main.o" "$build/shell.o" \
    "$lib/libLean.a" "$lib/libStd.a" "$lib/libInit.a" "$build/libleancpp-rulean.a" "$lib/libleanrt.a" "${libs[@]}" \
    "$rulean" -Wl,-export_dynamic -lc++
else
  "$cxx" -o "$out/bin/lean" "$build/main.o" "$build/shell.o" \
    -Wl,--start-group "$build/libleancpp-rulean.a" "$lib/libLean.a" "$rulean" -Wl,--end-group "$lib/libStd.a" \
    -Wl,--start-group "$lib/libInit.a" "$lib/libleanrt.a" -Wl,--end-group "${libs[@]}" \
    -nostdlib++ -L"$toolchain/lib" -Wl,-Bstatic -lc++ -lc++abi -Wl,-Bdynamic -rdynamic -lpthread -ldl -lrt -lm
fi
if [ "$features" = dual ]; then
  "$llvm_nm" -g --defined-only "$out/bin/lean" | awk '{print $3}' | sort -u > "$build/lean-defined.txt"
  for s in "${syms[@]}"; do
    if ! grep -qxF "${p}${s}_cpp" "$build/lean-defined.txt"; then
      echo "lean-build: the binary does not export ${s}_cpp" >&2
      exit 1
    fi
  done
fi
ln -sfn "$toolchain/lib" "$out/lib"
# Lean runs the SAT solver cadical from the directory of the lean binary.
if [ -x "$toolchain/bin/cadical" ]; then
  ln -sfn "$toolchain/bin/cadical" "$out/bin/cadical"
fi
ln -sfn "$toolchain/include" "$out/include"
if [ "$features" = dual ]; then
  echo "lean-build: $out/bin/lean has rulean and the C++ kernel, and it compares their results"
else
  echo "lean-build: $out/bin/lean has rulean as its kernel"
fi
