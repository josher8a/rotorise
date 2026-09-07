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
#   scripts/gate.sh              all eight checks
#   scripts/gate.sh --no-build   the five Python guards only
#
# `--no-build` skips the two checks that need the container — the build and the vector
# bridge — and is NOT for comments-only commits in the sense of "docs are exempt". Editing any `Calculus/*.lean`, comments included, can move a
# `doc_counts` count, because §4c and §5 cite file lengths and a span runs to the
# last non-blank line before the next declaration — so a re-wrapped signature
# moves a number in a file you did not edit. `doc_counts.py --check` runs under
# `--no-build` for exactly that reason. What `--no-build` skips is the ~12-minute
# Docker build, and it is honest only when nothing you touched can reach the
# elaborator: a change confined to `docs/`, `README.md`, `ARCHITECTURE.md`,
# `HANDOFF.md` or `scripts/`. If you edited a `.lean` file at all — even a
# docstring, even a blank line — run the full gate. A docstring is elaborated.
# And if you edited `src/codec/lean.ts` or a `Calculus/` *constructor*, the bridge is
# what will tell you, so do not skip it there either.
#
# The five Python guards run on the HOST, from `formal/`. There is no Python in
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
REPO_DIR="$(cd "$FORMAL_DIR/.." && pwd)"
# the TS toolchain is not on this host's PATH and neither is `node`; the bridge's generator is
# TypeScript, so the gate needs both images — this one to emit and the Lean one to elaborate
TS_IMAGE=mcr.microsoft.com/devcontainers/typescript-node:0-20
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
run 'docstring_anchor.py'   python3 scripts/docstring_anchor.py

if [ "$RUN_BUILD" -eq 1 ]; then
  run 'lake build' docker exec "$CONTAINER" bash -lc 'cd /workspaces/Rotorise/formal && lake build'
  # The vector bridge, and it is here because it was broken for a day with every other check
  # green. `src/codec/lean.ts` emitted the pre-`Body` three-argument `Term.object` after `db444e3`
  # changed the arity, and nothing reported it: the committed samples are generated *by* that
  # emitter, so `lean.spec.ts`'s byte comparison agreed with a stale generator, and no gate ran
  # a generated file through Lean. A test that compares a generator against its own output
  # cannot see the generator being wrong. This runs the emitted theorems against `Calculus/`.
  # Emit the full refusal cross product and the declaration-guard verdicts, then elaborate them
  # beside the two committed samples. `.separations.lean` is one theorem per option pair `src/`'s
  # `union` refuses, asserting the model does not certify it — the law runs that way only, `Orth`
  # being sufficient and not necessary (`ARCHITECTURE.md` §5). `.readverdicts.lean` is the
  # read-side differential: `AdmA t a` against whether `decode` accepted it, 861 of 864 pairs,
  # the other three stuck on the `Double` axiom and named in its header (§10).
  # `.readvectors.lean` is the read side of every corpus codec: the model's `p`, given the
  # attribute the library wrote, against the value the library read back. The write vectors and
  # the refusal vectors are both about `e`, and `p` was asserted only where a union had to choose,
  # so for the corpus at large one half of each pair went unproposed. Both halves here come from
  # running the library, so a change to either direction stops the file compiling.
  # `.resolutions.lean` widens the two pinned union vectors to every (union, value) and
  # (union, attribute) pair — which option the model's `select` picks against the one the
  # library's resolver did. The counts, and which pairs cannot be stated at all, are in that
  # file's own header, where the emitter that produces them keeps them true; `lean.spec.ts`
  # asserts the same numbers. A count copied to here is a count that goes stale unread, and
  # this one had: it said 226 reads against the header's 231 statable of 232.
  # The committed samples are a readable subset and say so in their header; what is *verified*
  # is all of it, which is the distinction the broken bridge was hiding — a sample regenerated
  # from a stale emitter agrees with itself, so only elaboration is evidence.
  run 'vector emit' docker run --rm -v "$REPO_DIR:/w" -w /w "$TS_IMAGE" \
    bash -lc 'EMIT_LEAN_REFUSALS=1 npx --no-install vitest run src/codec/lean/lean.spec.ts --reporter=dot'
  run 'vector bridge' docker exec "$CONTAINER" bash -lc \
    'cd /workspaces/Rotorise/formal &&
     for f in ../src/codec/lean/lean.sample.check.lean ../src/codec/lean/lean.sample.lean .vectors.full.lean \
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
