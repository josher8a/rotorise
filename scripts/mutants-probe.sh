#!/usr/bin/env bash
# The contract of `scripts/mutants.sh`, on a small tree that this script writes: each outcome of a
# row prints its word and gives its exit, a selection of no row is an error, and a directory with a
# `.git` is refused. Exit 0 where each probe holds.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RUNNER="$HERE/mutants.sh"

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$WORK/tree"
printf 'alpha\n' > "$WORK/tree/a.txt"
printf 'beta\n' > "$WORK/tree/b.txt"

# One row of a table: the id, the file, the expression, the check, the text, separated by a tab.
CHECK='grep -q alpha a.txt || { echo "alpha is gone"; exit 1; }'
row() { printf '%s\t%s\t%s\t%s\t%s\n' "$@"; }
row died   a.txt 's/alpha/gamma/' "$CHECK" 'alpha is gone'  > "$WORK/died.tsv"
row noop   a.txt 's/zzz/yyy/'     "$CHECK" 'alpha is gone'  > "$WORK/noop.tsv"
row wrong  a.txt 's/alpha/gamma/' "$CHECK" 'other words'    > "$WORK/wrong.tsv"
row alive  a.txt 's/alpha/gamma/' 'true'   'alpha is gone'  > "$WORK/alive.tsv"
{ row died a.txt 's/alpha/gamma/' "$CHECK" 'alpha is gone'
  row other b.txt 's/beta/gamma/' 'grep -q beta b.txt || { echo "beta is gone"; exit 1; }' 'beta is gone'
} > "$WORK/two.tsv"

failed=0
# probe <name> <the exit that the run must give> <a word that the output must hold> <arguments of the runner>
probe() {
  local name="$1" want="$2" word="$3"
  shift 3
  local out ec
  out=$("$RUNNER" "$@" 2>&1)
  ec=$?
  if [ "$ec" -eq "$want" ] && printf '%s\n' "$out" | grep -qF -- "$word"; then
    printf 'PASS  %s\n' "$name"
  else
    printf 'FAIL  %s\n' "$name"
    printf '      | exit %s, want %s, and the word `%s`\n' "$ec" "$want" "$word"
    printf '%s\n' "$out" | sed 's/^/      | /' | head -8
    failed=1
  fi
}

probe 'a row that dies gives DIED and exit 0'                  0 'DIED' "$WORK/tree" --table "$WORK/died.tsv"
probe 'a row that changes nothing gives NOOP, and the run fails' 1 'NOOP' "$WORK/tree" --table "$WORK/noop.tsv"
probe 'a wrong text gives WRONG_DEATH, and the run fails'       1 'WRONG_DEATH' "$WORK/tree" --table "$WORK/wrong.tsv"
probe 'a check that passes gives SURVIVED, and the run fails'   1 'SURVIVED' "$WORK/tree" --table "$WORK/alive.tsv"
probe 'a selection of no row is an error'                       2 'holds no row' "$WORK/tree" --table "$WORK/died.tsv" --files nothing.txt
probe 'a selection by file runs that row only'                  0 'selected=1 ' "$WORK/tree" --table "$WORK/two.tsv" --files b.txt
# The seeded table: one row of each outcome, a failing control, and a slow first row, so that the rows
# finish in another order than the table. The output of N workers must equal the output of one.
printf 'gamma\n' > "$WORK/tree/c.txt"
SLOW='sleep 1; grep -q alpha a.txt || { echo "alpha is gone"; exit 1; }'
BETA='grep -q beta b.txt || { echo "beta is gone"; exit 1; }'
GAMMA='grep -q gamma c.txt || { echo "gamma is gone"; exit 1; }'
FAILING='echo "control output"; grep -q nothere a.txt'
{ row slow_died a.txt 's/alpha/zzz/' "$SLOW" 'alpha is gone'
  row fast_died b.txt 's/beta/zzz/' "$BETA" 'beta is gone'
  row survived c.txt 's/gamma/zzz/' 'true' 'gamma is gone'
  row noop c.txt 's/nomatch/x/' "$GAMMA" 'gamma is gone'
  row wrong_death c.txt 's/gamma/zzz/' "$GAMMA" 'other words'
  row invalid_no_file nofile.txt 's/a/b/' "$GAMMA" 'gamma is gone'
  row invalid_bad_expression c.txt 's/(/x/' "$GAMMA" 'gamma is gone'
  row invalid_failing_control c.txt 's/gamma/zzz/' "$FAILING" 'x'
  row invalid_failing_control_again b.txt 's/beta/zzz/' "$FAILING" 'x'
  row died_after b.txt 's/beta/yyy/' "$BETA" 'beta is gone'
} > "$WORK/seeded.tsv"
seeded() { "$RUNNER" "$WORK/tree" --table "$WORK/seeded.tsv" "$@" 2>&1; echo "exit=$?"; }
one=$(seeded)
for word in 'DIED         slow_died' 'SURVIVED     survived' 'NOOP         noop' 'WRONG_DEATH  wrong_death' \
  'INVALID      invalid_no_file' 'INVALID      invalid_bad_expression' 'INVALID      invalid_failing_control:' \
  'CONTROL FAIL' 'MUTANTS selected=10 died=3 survived=1 noop=1 wrong_death=1 invalid=4' 'exit=1'; do
  if printf '%s\n' "$one" | grep -qF -- "$word"; then
    printf 'PASS  the seeded table gives the word `%s`\n' "$word"
  else
    printf 'FAIL  the seeded table gives the word `%s`\n' "$word"; failed=1
  fi
done
for jobs in 1 3 3; do
  if [ "$(seeded --jobs "$jobs")" = "$one" ]; then
    printf 'PASS  the output at --jobs %s equals the output at the default\n' "$jobs"
  else
    printf 'FAIL  the output at --jobs %s equals the output at the default\n' "$jobs"; failed=1
  fi
done
row killed a.txt 's/alpha/gamma/' 'grep -q alpha a.txt || kill -9 $$' 'alpha is gone' > "$WORK/killed.tsv"
probe 'a check killed with exit 137 gives INVALID with the cause, and the run fails' 1 'exit 137, the check was killed, memory' "$WORK/tree" --table "$WORK/killed.tsv"
probe '--help prints the header to its end, memory line included' 0 'times 5 GB of free memory' --help
probe 'a --jobs of 0 is refused'                                2 'positive number' "$WORK/tree" --table "$WORK/died.tsv" --jobs 0
probe 'a --jobs that is no number is refused'                   2 'positive number' "$WORK/tree" --table "$WORK/died.tsv" --jobs many
# --noop-only runs no check and no control: it names the rows that change nothing, and the rows that cannot run.
noop_out=$("$RUNNER" "$WORK/tree" --table "$WORK/seeded.tsv" --noop-only 2>&1; echo "exit=$?")
for word in 'NOOP         noop' 'INVALID      invalid_no_file' 'INVALID      invalid_bad_expression' \
  'NOOP-ONLY selected=10 noop=1 invalid=2' 'exit=1'; do
  if printf '%s\n' "$noop_out" | grep -qF -- "$word"; then
    printf 'PASS  --noop-only gives the word `%s`\n' "$word"
  else
    printf 'FAIL  --noop-only gives the word `%s`\n' "$word"; failed=1
  fi
done
for word in 'DIED' 'SURVIVED' 'CONTROL' 'WRONG_DEATH'; do
  if printf '%s\n' "$noop_out" | grep -qF -- "$word"; then
    printf 'FAIL  --noop-only gives no word `%s`, because it runs no check\n' "$word"; failed=1
  else
    printf 'PASS  --noop-only gives no word `%s`, because it runs no check\n' "$word"
  fi
done
probe '--noop-only on rows that change something gives exit 0'  0 'NOOP-ONLY selected=1 noop=0 invalid=0' "$WORK/tree" --table "$WORK/died.tsv" --noop-only
mkdir "$WORK/tree/.git"
probe 'a directory that holds .git is refused'                  2 'holds .git' "$WORK/tree" --table "$WORK/died.tsv"
exit "$failed"
