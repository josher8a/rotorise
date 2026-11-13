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
mkdir "$WORK/tree/.git"
probe 'a directory that holds .git is refused'                  2 'holds .git' "$WORK/tree" --table "$WORK/died.tsv"
exit "$failed"
