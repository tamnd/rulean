#!/usr/bin/env bash
# The entry of rulean in the Lean Kernel Arena (spec 09.5). The Arena runs it as `scripts/arena-run.sh "$IN"` after `cargo build --release --locked --bin rulean`.
#
# Usage: scripts/arena-run.sh EXPORT [RULEAN]
#
# The Arena reads only the exit codes 0 (accept), 1 (reject) and 2 (decline). The script maps the other codes of spec 09.3 to those three. An input error (4) and an axiom policy failure (5) are a reject. A resource limit (3) and a usage error (64) are a decline, because they are not a verdict.
#
# The Arena gives one fixed verdict for each test, and some tests are exports from Lean releases before v4.35.0. So the script uses the v4.35 profile, and not the profile of the export. A direct call of `rulean check` declines for these exports (spec 05.2). Set ARENA_PROFILE to use another profile, as scripts/arena-check.sh does for the "either" tests of v4.37.

set -uo pipefail

if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
  echo "usage: $0 EXPORT [RULEAN]" >&2
  exit 2
fi
here="$(cd "$(dirname "$0")/.." && pwd)"
rulean="${2:-$here/target/release/rulean}"

code=0
"$rulean" check --profile "${ARENA_PROFILE:-v4.35}" "$1" || code=$?
case "$code" in
  0 | 1 | 2) exit "$code" ;;
  4 | 5) exit 1 ;;
  *) exit 2 ;;
esac
