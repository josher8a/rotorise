#!/usr/bin/env bash
# The witnesses of the tests: each row of `scripts/mutants.tsv` changes one file of a copy of the tree,
# and the check of the row must fail with the text of the row.
#
#   scripts/mutants.sh <tree>                   run each row on a copy of <tree>
#   scripts/mutants.sh <tree> --files a,b       run the rows whose file field is in the list
#   scripts/mutants.sh <tree> --table <file>    read another table
#
# <tree> holds the files of the repository and no `.git`: the script refuses a directory that holds
# one, because the check of a row builds and writes in the copy, and the copy must never be a
# working tree. The copy takes each file of <tree> but `node_modules`, which the copy links.
#
# A row has five fields, separated by a tab: the id, the file, a `sed -E` expression, the check, and a
# text. The outcome of a row is one of:
#
#   DIED         the check fails, and its output holds the text
#   SURVIVED     the check passes: no test pins the rule
#   NOOP         the expression changes nothing: the rule moved, and the row needs a new expression
#   WRONG_DEATH  the check fails, and its output lacks the text
#   INVALID      the row cannot run: no such file, a bad expression, or a check that fails with no change
#
# A control is a check that runs on the copy with no change. Each control must exit 0. The check of
# a row runs through `bash -c` at the root of the copy. A selection of no row is an error.
# Exit 0 where each control exits 0 and each selected row DIED. Exit 1 on any other outcome, and
# exit 2 on a wrong call or a failure of the script.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TABLE="$HERE/mutants.tsv"
TREE=""
FILES=""

usage() { echo "usage: mutants.sh <tree> [--files a,b] [--table <file>]" >&2; exit 2; }

while [ $# -gt 0 ]; do
  case "$1" in
    --files) shift; FILES="${1:?--files needs a list}" ;;
    --table) shift; TABLE="${1:?--table needs a file}" ;;
    -h|--help) sed -n '2,25p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    -*) echo "mutants.sh: unknown argument: $1" >&2; usage ;;
    *) [ -z "$TREE" ] || usage; TREE="$1" ;;
  esac
  shift
done
[ -n "$TREE" ] || usage
[ -d "$TREE" ] || { echo "mutants.sh: $TREE is no directory" >&2; exit 2; }
TREE="$(cd "$TREE" && pwd)"
[ ! -e "$TREE/.git" ] || {
  echo "mutants.sh: $TREE holds .git; run on a copy of the files, as \`git archive\` writes them" >&2; exit 2; }
[ -f "$TABLE" ] || { echo "mutants.sh: no table at $TABLE" >&2; exit 2; }

# A row with a field that is absent or empty shifts the fields of the read, so the script refuses it.
awk -F'\t' '/^#/ || NF == 0 { next }
  NF != 5 || $1 == "" || $2 == "" || $3 == "" || $4 == "" || $5 == "" {
    printf "mutants.sh: line %d of the table has no five fields\n", NR; bad = 1 }
  END { exit bad }' "$TABLE" >&2 || exit 2

ESC="$(printf '\033')"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
mkdir "$WORK/tree"
(cd "$TREE" && tar -cf - --exclude=./node_modules .) | (cd "$WORK/tree" && tar -xf -) || {
  echo "mutants.sh: the copy of $TREE failed" >&2; exit 2; }
[ ! -d "$TREE/node_modules" ] || ln -s "$TREE/node_modules" "$WORK/tree/node_modules"

# The selected rows, in the order of the table.
rows=()
while IFS= read -r line; do
  case "$line" in ''|'#'*) continue ;; esac
  if [ -n "$FILES" ]; then
    IFS=$'\t' read -r _ file _ <<<"$line"
    case ",$FILES," in *",$file,"*) ;; *) continue ;; esac
  fi
  rows+=("$line")
done < "$TABLE"
selected=${#rows[@]}
[ "$selected" -gt 0 ] || { echo "mutants.sh: the selection holds no row" >&2; exit 2; }

run() { (cd "$WORK/tree" && bash -c "$1") > "$WORK/out" 2>&1 < /dev/null; }

# The controls: each distinct check, once.
bad_checks=$'\n'
control_failed=0
seen=$'\n'
for line in "${rows[@]}"; do
  IFS=$'\t' read -r _ _ _ check _ <<<"$line"
  case "$seen" in *$'\n'"$check"$'\n'*) continue ;; esac
  seen="$seen$check"$'\n'
  run "$check"
  ec=$?
  if [ "$ec" -eq 0 ]; then
    printf 'CONTROL ok    %s\n' "$check"
  else
    printf 'CONTROL FAIL exit=%s  %s\n' "$ec" "$check"
    sed 's/^/      | /' "$WORK/out" | tail -8
    bad_checks="$bad_checks$check"$'\n'
    control_failed=1
  fi
done

died=0; survived=0; noop=0; wrong=0; invalid=0
for line in "${rows[@]}"; do
  IFS=$'\t' read -r id file expr check text <<<"$line"
  target="$WORK/tree/$file"
  case "$bad_checks" in *$'\n'"$check"$'\n'*)
    printf 'INVALID      %s: the check fails with no change\n' "$id"; invalid=$((invalid + 1)); continue ;;
  esac
  if [ ! -f "$target" ]; then
    printf 'INVALID      %s: no file %s\n' "$id" "$file"; invalid=$((invalid + 1)); continue
  fi
  cp "$target" "$WORK/orig"
  if ! sed -E "$expr" "$WORK/orig" > "$WORK/mutant" 2> "$WORK/sed.err"; then
    printf 'INVALID      %s: the expression fails: %s\n' "$id" "$(head -1 "$WORK/sed.err")"
    invalid=$((invalid + 1)); continue
  fi
  if cmp -s "$WORK/orig" "$WORK/mutant"; then
    printf 'NOOP         %s\n' "$id"; noop=$((noop + 1)); continue
  fi
  cp "$WORK/mutant" "$target"
  run "$check"
  ec=$?
  cp "$WORK/orig" "$target"
  cmp -s "$WORK/orig" "$target" || { echo "mutants.sh: $file is not restored" >&2; exit 2; }
  sed "s/$ESC\[[0-9;]*m//g" "$WORK/out" > "$WORK/out.txt"
  if [ "$ec" -eq 0 ]; then
    printf 'SURVIVED     %s\n' "$id"; survived=$((survived + 1))
  elif grep -qF -- "$text" "$WORK/out.txt"; then
    printf 'DIED         %s\n' "$id"; died=$((died + 1))
  else
    printf 'WRONG_DEATH  %s: exit %s, and no line holds the text\n' "$id" "$ec"
    tail -8 "$WORK/out.txt" | sed 's/^/      | /'
    wrong=$((wrong + 1))
  fi
done

printf 'MUTANTS selected=%s died=%s survived=%s noop=%s wrong_death=%s invalid=%s\n' \
  "$selected" "$died" "$survived" "$noop" "$wrong" "$invalid"
[ "$died" -eq "$selected" ] && [ "$control_failed" -eq 0 ]
