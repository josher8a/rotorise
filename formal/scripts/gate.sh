#!/usr/bin/env bash
# The commit gate: HANDOFF's Landmines checks, in order, gated on exit codes.
#
# It exists because the gate used to be a paste block in a file that is deleted
# once read, and pasting it wrong is not hypothetical: `eed1b58` and `e3bd71f`
# both claim all guards pass over a red tree. They ran the checks as
# `…; echo "$g=$?"; done && git commit` — `echo` always succeeds, so the chain
# gated on nothing and the printed output was true while the verdict was false.
# Printing an exit code is not checking it. This script checks it.
#
#   scripts/gate.sh              all six checks
#   scripts/gate.sh --no-build   the four Python guards only
#
# `--no-build` skips the two checks that need the container — the build and the vector
# bridge — and is NOT for comments-only commits in the sense of "docs are exempt". Editing any `Calculus/*.lean`, comments included, can move a
# `doc_counts` count, because §5 and §8 cite file lengths and a span runs to the
# last non-blank line before the next declaration — so a re-wrapped signature
# moves a number in a file you did not edit. `doc_counts.py --check` runs under
# `--no-build` for exactly that reason. What `--no-build` skips is the ~12-minute
# Docker build, and it is honest only when nothing you touched can reach the
# elaborator: a change confined to `docs/`, `README.md`, `ARCHITECTURE.md`,
# `HANDOFF.md` or `scripts/`. If you edited a `.lean` file at all — even a
# docstring, even a blank line — run the full gate. A docstring is elaborated.
# And if you edited `src/lean.ts` or a `Calculus/` *constructor*, the bridge is
# what will tell you, so do not skip it there either.
#
# The four Python guards run on the HOST, from `formal/`. There is no Python in
# `rotorise-lean-dev` at all. The build runs in the container, and only one
# `lake build` may run at a time across the sessions sharing this tree — your
# build rewrites oleans under someone else's `lake env lean`.
#
# Every check runs even after one fails, so one invocation reports the whole
# state of the tree rather than its first symptom. The exit code is 1 if any
# check failed and 0 only when all of them passed.

set -uo pipefail

FORMAL_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$FORMAL_DIR" || exit 2

CONTAINER=rotorise-lean-dev
RUN_BUILD=1

for arg in "$@"; do
  case "$arg" in
    --no-build) RUN_BUILD=0 ;;
    -h|--help)  sed -n '2,40p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
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
run 'doc_counts.py --check' python3 scripts/doc_counts.py --check
run 'ratchet.py'            python3 scripts/ratchet.py

if [ "$RUN_BUILD" -eq 1 ]; then
  run 'lake build' docker exec "$CONTAINER" bash -lc 'cd /workspaces/Rotorise/formal && lake build'
  # The vector bridge, and it is here because it was broken for a day with every other check
  # green. `src/lean.ts` emitted the pre-`Body` three-argument `Term.object` after `db444e3`
  # changed the arity, and nothing reported it: the committed samples are generated *by* that
  # emitter, so `lean.spec.ts`'s byte comparison agreed with a stale generator, and no gate ran
  # a generated file through Lean. A test that compares a generator against its own output
  # cannot see the generator being wrong. This runs the emitted theorems against `Calculus/`.
  run 'vector bridge' docker exec "$CONTAINER" bash -lc \
    'cd /workspaces/Rotorise/formal && lake env lean ../src/lean.sample.check.lean && lake env lean ../src/lean.sample.lean'
else
  printf 'SKIP  %-28s (--no-build)\n' 'lake build'
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
