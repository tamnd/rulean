#!/usr/bin/env bash
# The gates of the full suite of spec 08.7.2 on one corpus test, from the output of GNU time of the steps check and official of scripts/corpus.sh.
#
# Usage: scripts/corpus-gate.sh TEST WORK
#
# TEST is mathlib, cslib or cedar, and WORK is the work directory of scripts/corpus.sh. The script writes WORK/out/gate.json and exits with code 1 if a gate fails. The gates are:
#
# - verdict: rulean check and the official kernel both exit with status 0, because each test of the corpus is accepted.
# - ratio: the CPU time of the official kernel divided by the CPU time of rulean check is at least 10. The CPU time is the user time and the system time of all threads. This is P1.a on Mathlib and P1.c on the other tests. A GitHub-hosted runner has no hardware counters, so the ratio of CPU times takes the place of the ratio of instructions, and it is not the Arena measure.
# - memory: the peak memory of rulean check is at most 4 GiB (P1.f).
#
# P1.b needs the official nightly, and P1.e needs 8 threads on a workstation, so the script does not measure them.

set -euo pipefail

if [ "$#" -ne 2 ]; then
  echo "usage: $0 mathlib|cslib|cedar WORK" >&2
  exit 64
fi

test="$1"
out="$2/out"
case "$test" in
  mathlib) ratio_target=P1.a ;;
  cslib | cedar) ratio_target=P1.c ;;
  *)
    echo "$0: unknown test $test" >&2
    exit 64
    ;;
esac

for f in check.time official.time; do
  if [ ! -f "$out/$f" ]; then
    echo "$0: $out/$f is missing" >&2
    exit 1
  fi
done

# The user time and the system time in seconds, from the output of GNU time -v.
cpu() {
  awk -F': ' '/User time \(seconds\)|System time \(seconds\)/ { s += $2 } END { printf "%.2f", s }' "$1"
}

# A field of the output of GNU time -v, for example "Exit status".
field() {
  awk -F': ' -v k="$2" '{ sub(/^[[:space:]]+/, "", $1) } $1 == k { print $2; exit }' "$1"
}

r_cpu="$(cpu "$out/check.time")"
o_cpu="$(cpu "$out/official.time")"
r_status="$(field "$out/check.time" "Exit status")"
o_status="$(field "$out/official.time" "Exit status")"
r_kib="$(field "$out/check.time" "Maximum resident set size (kbytes)")"
o_kib="$(field "$out/official.time" "Maximum resident set size (kbytes)")"
r_wall="$(field "$out/check.time" "Elapsed (wall clock) time (h:mm:ss or m:ss)")"
o_wall="$(field "$out/official.time" "Elapsed (wall clock) time (h:mm:ss or m:ss)")"
ratio="$(awk -v o="$o_cpu" -v r="$r_cpu" 'BEGIN { if (r > 0) printf "%.2f", o / r; else print "0" }')"
r_mib=$((r_kib / 1024))
o_mib=$((o_kib / 1024))

fail=0
gate() {
  if [ "$2" = pass ]; then
    echo "pass: $1"
  else
    echo "fail: $1"
    fail=1
  fi
}

if [ "$r_status" = 0 ] && [ "$o_status" = 0 ]; then v=pass; else v=fail; fi
gate "verdict: rulean exit status $r_status, official exit status $o_status" "$v"
if awk -v x="$ratio" 'BEGIN { exit !(x >= 10) }'; then v=pass; else v=fail; fi
gate "ratio ($ratio_target): official $o_cpu s, rulean $r_cpu s of CPU time, ratio $ratio, target at least 10" "$v"
if [ "$r_mib" -le 4096 ]; then v=pass; else v=fail; fi
gate "memory (P1.f): rulean $r_mib MiB, official $o_mib MiB, target at most 4096 MiB" "$v"
echo "wall time: rulean $r_wall, official $o_wall, ${THREADS:-1} threads of rulean"

cat >"$out/gate.json" <<JSON
{
  "test": "$test",
  "threads": ${THREADS:-1},
  "rulean": { "exit_status": $r_status, "cpu_seconds": $r_cpu, "wall": "$r_wall", "max_rss_mib": $r_mib },
  "official": { "exit_status": $o_status, "cpu_seconds": $o_cpu, "wall": "$o_wall", "max_rss_mib": $o_mib },
  "ratio": $ratio,
  "ratio_target": "$ratio_target",
  "pass": $([ "$fail" = 0 ] && echo true || echo false)
}
JSON
exit "$fail"
