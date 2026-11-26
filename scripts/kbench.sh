#!/usr/bin/env bash
# Runs rulean and the popular kernels of a Lean toolchain on one export, and prints the instructions and the peak memory of each kernel (spec perf/03.1 and perf/07.3).
#
# Usage: scripts/kbench.sh EXPORT [KERNEL...]
#
# EXPORT is an NDJSON export. KERNEL is one of rulean-R, rulean-F, nanoda, con-ron and official. With no KERNEL, the script runs each kernel. TOOLCHAIN is the bin directory of the Lean toolchain that has the kernels, and the default is the directory of `lean` on PATH. RULEAN is the rulean binary, and the default is target/release/rulean. OUT is the directory for the output of each run, and the default is a new directory under TMPDIR.
#
# The script prints one line for each kernel, with tabs between the fields: the name, the exit code, the instructions and the peak memory in bytes. Each kernel runs with one thread. On macOS the count is the line "instructions retired" of `/usr/bin/time -l`, and it includes the system calls. On Linux the count is `perf stat -e instructions:u`, as on the Arena. A count is valid only for the process that the script starts, so the script starts each kernel directly and not through a shell. The count of one machine is not the count of the Arena machine. Use the counts for a ratio between two kernels on one machine.
#
# lean4lean is also a popular kernel, but the toolchain binary reads `.olean` files and not an export, so the script does not run it.

set -uo pipefail

if [ "$#" -lt 1 ]; then
  echo "usage: $0 EXPORT [KERNEL...]" >&2
  exit 64
fi
here="$(cd "$(dirname "$0")/.." && pwd)"
in="$1"
shift
if [ ! -f "$in" ]; then
  echo "kbench: no file $in" >&2
  exit 66
fi
if [ -n "${TOOLCHAIN:-}" ]; then
  tc="$TOOLCHAIN"
else
  lean="$(command -v lean || true)"
  if [ -z "$lean" ]; then
    echo "kbench: set TOOLCHAIN, or put lean on PATH" >&2
    exit 64
  fi
  tc="$(lean --print-prefix)/bin"
fi
rulean="${RULEAN:-$here/target/release/rulean}"
tmp="${TMPDIR:-/tmp}"
out="${OUT:-$(mktemp -d "${tmp%/}/kbench.XXXXXX")}"
mkdir -p "$out"
kernels=("$@")
if [ "${#kernels[@]}" -eq 0 ]; then
  kernels=(rulean-R rulean-F nanoda con-ron official)
fi

# nanoda reads its options from a JSON file, and the export from stdin.
nanoda_cfg="$out/nanoda.json"
printf '%s\n' '{"use_stdin": true, "nat_extension": true, "string_extension": true, "unpermitted_axiom_hard_error": false, "unsafe_permit_all_axioms": true, "num_threads": 1, "stack_size_bytes": 268435456}' >"$nanoda_cfg"

os="$(uname -s)"

# Runs one kernel. The first argument is the name, then "stdin" or "arg", then the command.
run() {
  local name="$1" mode="$2"
  shift 2
  local log="$out/$name.txt"
  local cnt="$out/$name.count"
  local rc
  if [ "$os" = Darwin ]; then
    if [ "$mode" = stdin ]; then
      /usr/bin/time -l "$@" <"$in" >"$log" 2>&1
    else
      /usr/bin/time -l "$@" >"$log" 2>&1
    fi
    rc=$?
    local ins mem
    ins="$(awk '/instructions retired/ {print $1}' "$log")"
    mem="$(awk '/maximum resident set size/ {print $1}' "$log")"
  else
    if [ "$mode" = stdin ]; then
      perf stat -x, -e instructions:u -o "$cnt" -- /usr/bin/time -f 'maxrss %M' -o "$log.rss" "$@" <"$in" >"$log" 2>&1
    else
      perf stat -x, -e instructions:u -o "$cnt" -- /usr/bin/time -f 'maxrss %M' -o "$log.rss" "$@" >"$log" 2>&1
    fi
    rc=$?
    ins="$(awk -F, '/instructions/ {print $1}' "$cnt")"
    mem="$(awk '/maxrss/ {print $2 * 1024}' "$log.rss")"
  fi
  printf '%s\t%s\t%s\t%s\n' "$name" "$rc" "${ins:-NA}" "${mem:-NA}"
}

for k in "${kernels[@]}"; do
  case "$k" in
    rulean-R) run rulean-R arg "$rulean" check "$in" --engine R ;;
    rulean-F) run rulean-F arg "$rulean" check "$in" --engine F ;;
    nanoda) run nanoda stdin "$tc/nanoda_bin" "$nanoda_cfg" ;;
    con-ron) run con-ron arg "$tc/con-ron" --jobs=1 "$in" ;;
    official) run official arg env PATH="$tc:$PATH" "$tc/leanchecker" --from-export "$in" ;;
    *)
      echo "kbench: no kernel $k" >&2
      exit 64
      ;;
  esac
done
echo "kbench: the output of each run is in $out" >&2
