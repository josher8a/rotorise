#!/usr/bin/env bash
# The commit gate: every check, in order, gated on exit codes.
#
#   scripts/gate.sh              all nine checks
#   scripts/gate.sh --no-build   the five Python guards only
#
# `--no-build` skips the build, the gateway check, the emit, the pool pre-check and the bridge,
# and is honest only when no `.lean` file changed.
#
# Run the gate inside the devcontainer or on CI. Only one `lake build` may run at a time
# across the sessions sharing this tree, and a build from `docs/` is one of them: `calculus`
# is a path dependency there, so it writes this package's `.lake/build`.
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
run 'layer_order.py'        python3 scripts/layer_order.py

if [ "$RUN_BUILD" -eq 1 ]; then
  run 'lake build' lake build
  # The routes by which this development reaches `Classical.choice`, against the baseline.
  # A name in the output and not in the baseline is a new classical route and fails. A name
  # in the baseline and not in the output is a fall and passes.
  run 'classical gateways' bash -c \
    'out=$(lake env lean scripts/classical.lean 2>&1) || { echo "$out"; exit 1; }
     new=$(comm -23 <(printf "%s\n" "$out" | sort) \
                    <(grep -v "^#" scripts/classical_gateways.txt | sort))
     [ -z "$new" ] || { echo "new classical route(s):"; echo "$new"; exit 1; }'
  run 'vector emit' bash -c \
    "cd \"$REPO_DIR\" && EMIT_LEAN_REFUSALS=1 npx --no-install vitest run src/codec/lean/lean.spec.ts src/codec/lean/lean.pool.spec.ts --reporter=dot"
  # The generated pool, put to the model by `#eval`. A row prints only on a mismatch, and Lean
  # exits 0 after a print, so the check reads the output: the sentinel line must be all of it.
  # The two pre-checks and the vector bridge run as one set of parallel jobs, longest first: the
  # kernel checks the theorems of one file in sequence, so the wall time of the set is the time of
  # its longest file. A job writes its output to a file, and the step reads every file after the
  # set ends, so one failure does not hide another. GATE_JOBS bounds the memory of the set.
  run 'pool pre-check + bridge' bash -c '
    jobs=${GATE_JOBS:-6}; out=$(mktemp -d); trap "rm -rf $out" EXIT
    printf "%s\n" .pool.separations.lean .pool.slices.lean .pool.disjoints.lean .corpus.eval.lean \
      .pool.paths0.lean .pool.paths1.lean .pool.paths3.lean .pool.paths2.lean .pool.eval.lean \
      .legacyreads.lean .separations.lean .readverdicts.lean .disjoints.lean .vectors.full.lean \
      .resolutions.lean lean.sample.lean lean.sample.check.lean .readvectors.lean .pool.guards.lean |
    xargs -P "$jobs" -I{} sh -c "
      [ -f {} ] || { echo missing > $out/x{}.rc; exit 0; }
      lake env lean {} > $out/x{}.out 2>&1; echo \$? > $out/x{}.rc"
    fail=0
    for rc in "$out"/*.rc; do
      f=$(basename "$rc" .rc); f=${f#x}; o=$(cat "$out/x$f.out" 2>/dev/null)
      if [ "$(cat "$rc")" != 0 ]; then echo "$f: exit $(cat "$rc")"; echo "$o"; fail=1; continue; fi
      if [ "$f" = .pool.eval.lean ] || [ "$f" = .corpus.eval.lean ]; then
        printf "%s\n" "$o" | grep -qxE "(pool: [0-9]+ pairs|corpus: [0-9]+ vectors) checked" \
          && [ "$(printf "%s\n" "$o" | wc -l)" -eq 1 ] || { echo "$f: $o"; fail=1; }
      elif [ -n "$o" ]; then echo "$f: $o"; fail=1; fi
    done
    [ "$(ls "$out"/*.rc | wc -l)" -eq 19 ] || { echo "a job did not report"; fail=1; }
    exit $fail'
else
  printf 'SKIP  %-28s (--no-build)\n' 'lake build'
  printf 'SKIP  %-28s (--no-build)\n' 'classical gateways'
  printf 'SKIP  %-28s (--no-build)\n' 'vector emit'
  printf 'SKIP  %-28s (--no-build)\n' 'pool pre-check + bridge'
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
