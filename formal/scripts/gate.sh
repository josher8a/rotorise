#!/usr/bin/env bash
# The commit gate: every check, in order, gated on exit codes.
#
#   scripts/gate.sh              all seven checks
#   scripts/gate.sh --no-build   the four Python guards only
#
# `--no-build` skips the build, the emit and the bridge, and is honest only when no `.lean`
# file changed.
#
# Run the gate inside the devcontainer. Only one `lake build` may run at a time across the
# sessions sharing this tree.
#
# Every check runs even after one fails, so one invocation reports the whole state of the
# tree rather than its first symptom. The exit code is 1 if any check failed and 0 only when
# all of them passed.

set -uo pipefail

FORMAL_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$FORMAL_DIR" || exit 2

REPO_DIR="$(cd "$FORMAL_DIR/.." && pwd)"
RUN_BUILD=1

for arg in "$@"; do
  case "$arg" in
    --no-build) RUN_BUILD=0 ;;
    -h|--help)  sed -n '2,15p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "gate.sh: unknown argument: $arg" >&2
       echo "usage: gate.sh [--no-build]" >&2
       exit 2 ;;
  esac
done

fail=0
first_failure=""

# run <label> <command…> — the one place an exit code is read, so there is one
# place to get it wrong.
run() {
  local label="$1"; shift
  local start elapsed rc
  start=$SECONDS
  "$@" >/dev/null 2>&1
  rc=$?
  elapsed=$((SECONDS - start))
  if [ $rc -eq 0 ]; then
    printf 'PASS  %-28s (%ds)\n' "$label" "$elapsed"
  else
    printf 'FAIL  %-28s (%ds, exit %d)\n' "$label" "$elapsed" "$rc"
    fail=1
    [ -z "$first_failure" ] && first_failure="$label (exit $rc)"
  fi
}

run 'guard_reach.py'        python3 scripts/guard_reach.py
run 'name_drift.py'         python3 scripts/name_drift.py
run 'ratchet.py'            python3 scripts/ratchet.py
run 'docstring_anchor.py'   python3 scripts/docstring_anchor.py

if [ "$RUN_BUILD" -eq 1 ]; then
  run 'lake build' lake build
  run 'vector emit' bash -c \
    "cd \"$REPO_DIR\" && EMIT_LEAN_REFUSALS=1 npx --no-install vitest run src/codec/lean/lean.spec.ts --reporter=dot"
  run 'vector bridge' bash -c \
    'for f in lean.sample.check.lean lean.sample.lean .vectors.full.lean \
              .separations.lean .readverdicts.lean .resolutions.lean \
              .readvectors.lean; do
       [ -f "$f" ] || { echo "missing $f"; exit 1; }
       out=$(lake env lean "$f" 2>&1) || { echo "$out"; exit 1; }
       # warnings are failures here: the generated files are machine-written, so a warning is
       # the emitter being sloppy rather than a human judgement call, and `Calculus/` itself
       # builds warning-free
       [ -z "$out" ] || { echo "$f: $out"; exit 1; }
     done'
else
  printf 'SKIP  %-28s (--no-build)\n' 'lake build'
  printf 'SKIP  %-28s (--no-build)\n' 'vector emit'
  printf 'SKIP  %-28s (--no-build)\n' 'vector bridge'
fi

echo
if [ $fail -eq 0 ]; then
  if [ "$RUN_BUILD" -eq 1 ]; then
    echo 'ALL_GREEN'
  else
    echo 'ALL_GREEN (guards only — the build did not run)'
  fi
  exit 0
fi

echo "FIRST FAILURE: $first_failure"
echo 'Re-run that check alone, without the output redirected, to see why.'
exit 1
