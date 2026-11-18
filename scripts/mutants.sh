#!/usr/bin/env bash
# The witnesses of the tests: each row of `scripts/mutants.tsv` changes one file of a copy of the tree,
# and the check of the row must fail with the text of the row.
#
#   scripts/mutants.sh <tree>                   run each row on a copy of <tree>
#   scripts/mutants.sh <tree> --files a,b       run the rows whose file field is in the list
#   scripts/mutants.sh <tree> --table <file>    read another table
#   scripts/mutants.sh <tree> --jobs N          run N checks at one time, each in a copy of its own
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
#   INVALID      the row cannot run: no such file, a bad expression, a check that fails with no change,
#                or a check that exits 137, which is a kill for memory and no finding about a test
#
# A control is a check that runs on the copy with no change. Each control must exit 0. The check of
# a row runs through `bash -c` at the root of the copy. A selection of no row is an error.
# Exit 0 where each control exits 0 and each selected row DIED. Exit 1 on any other outcome, and
# exit 2 on a wrong call or a failure of the script.
#
# `--jobs N` changes the time of the run and no word of the output. The default is 1. Each worker owns
# one copy of the tree. A worker links each entry of `node_modules` but `.vite`, the cache of `vitest`,
# which each copy keeps for itself: a cache that two checks write at one time is the one shared file.
# The controls run first, then the rows. The output lists the controls and the rows in the order of
# the table, as each one is done, so the output of N workers equals the output of one.
# A `vitest` check takes about 5 GB. Give N times 5 GB of free memory: on a smaller machine the kernel
# kills a check, and the row reads INVALID with exit 137.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TABLE="$HERE/mutants.tsv"
TREE=""
FILES=""
JOBS=1

usage() { echo "usage: mutants.sh <tree> [--files a,b] [--table <file>] [--jobs N]" >&2; exit 2; }

while [ $# -gt 0 ]; do
  case "$1" in
    --files) shift; FILES="${1:?--files needs a list}" ;;
    --table) shift; TABLE="${1:?--table needs a file}" ;;
    --jobs) shift; JOBS="${1:?--jobs needs a number}"
      case "$JOBS" in ''|*[!0-9]*|0) echo "mutants.sh: --jobs takes a positive number: $JOBS" >&2; usage ;; esac ;;
    -h|--help) sed -n '2,/^set -uo/p' "${BASH_SOURCE[0]}" | sed '$d' | sed 's/^# \{0,1\}//'; exit 0 ;;
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
trap 'kill $(jobs -p) 2>/dev/null; rm -rf "$WORK"' EXIT

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

# The controls: each distinct check, once, in the order of the first row that holds it.
checks=()
seen=$'\n'
for line in "${rows[@]}"; do
  IFS=$'\t' read -r _ _ _ check _ <<<"$line"
  case "$seen" in *$'\n'"$check"$'\n'*) continue ;; esac
  seen="$seen$check"$'\n'
  checks+=("$check")
done

# One worker for each check or row at most.
work=$JOBS
[ "$work" -le "$selected" ] || work=$selected
[ "$work" -ge 1 ] || work=1

# The copies, one for each worker. A copy links each entry of `node_modules` but `.vite`.
w=1
while [ "$w" -le "$work" ]; do
  mkdir -p "$WORK/w$w/tree"
  (cd "$TREE" && tar -cf - --exclude=./node_modules .) | (cd "$WORK/w$w/tree" && tar -xf -) || {
    echo "mutants.sh: the copy of $TREE failed" >&2; exit 2; }
  if [ -d "$TREE/node_modules" ]; then
    mkdir "$WORK/w$w/tree/node_modules"
    for entry in "$TREE"/node_modules/* "$TREE"/node_modules/.[!.]*; do
      [ -e "$entry" ] || continue
      [ "$(basename "$entry")" != .vite ] || continue
      ln -s "$entry" "$WORK/w$w/tree/node_modules/$(basename "$entry")"
    done
  fi
  w=$((w + 1))
done

# run <worker> <command>: the command at the root of the copy of the worker, the output in `out`.
run() { (cd "$WORK/w$1/tree" && bash -c "$2") > "$WORK/w$1/out" 2>&1 < /dev/null; }

# A worker that fails outside a check writes its words here, and the run exits 2.
fatal() { printf '%s\n' "$1" > "$WORK/fatal"; exit 2; }

# control_one <worker> <index>: the lines of one control, and a mark where it failed.
control_one() {
  local w="$1" i="$2" check="${checks[$2]}" ec
  run "$w" "$check"
  ec=$?
  {
    if [ "$ec" -eq 0 ]; then
      printf 'CONTROL ok    %s\n' "$check"
    else
      printf 'CONTROL FAIL exit=%s  %s\n' "$ec" "$check"
      sed 's/^/      | /' "$WORK/w$w/out" | tail -8
    fi
  } > "$WORK/ctl/$i.out"
  [ "$ec" -eq 0 ] || : > "$WORK/ctl/$i.fail"
  : > "$WORK/ctl/$i.done"
}

# row_body <worker> <index>: print the lines of one row, and write its outcome word.
row_body() {
  local w="$1" line="${rows[$2]}" id file expr check text target ec
  local d="$WORK/w$w" res="$WORK/res/$2"
  IFS=$'\t' read -r id file expr check text <<<"$line"
  target="$d/tree/$file"
  {
    case "$bad_checks" in *$'\n'"$check"$'\n'*)
      printf 'INVALID      %s: the check fails with no change\n' "$id"; echo invalid > "$res.kind"; return ;;
    esac
    if [ ! -f "$target" ]; then
      printf 'INVALID      %s: no file %s\n' "$id" "$file"; echo invalid > "$res.kind"; return
    fi
    cp "$target" "$d/orig"
    if ! sed -E "$expr" "$d/orig" > "$d/mutant" 2> "$d/sed.err"; then
      printf 'INVALID      %s: the expression fails: %s\n' "$id" "$(head -1 "$d/sed.err")"
      echo invalid > "$res.kind"; return
    fi
    if cmp -s "$d/orig" "$d/mutant"; then
      printf 'NOOP         %s\n' "$id"; echo noop > "$res.kind"; return
    fi
    cp "$d/mutant" "$target"
    run "$w" "$check"
    ec=$?
    cp "$d/orig" "$target"
    cmp -s "$d/orig" "$target" || fatal "mutants.sh: $file is not restored"
    sed "s/$ESC\[[0-9;]*m//g" "$d/out" > "$d/out.txt"
    if [ "$ec" -eq 0 ]; then
      printf 'SURVIVED     %s\n' "$id"; echo survived > "$res.kind"
    elif [ "$ec" -eq 137 ]; then
      printf 'INVALID      %s: exit 137, the check was killed, memory\n' "$id"; echo invalid > "$res.kind"
    elif grep -qF -- "$text" "$d/out.txt"; then
      printf 'DIED         %s\n' "$id"; echo died > "$res.kind"
    else
      printf 'WRONG_DEATH  %s: exit %s, and no line holds the text\n' "$id" "$ec"
      tail -8 "$d/out.txt" | sed 's/^/      | /'
      echo wrong > "$res.kind"
    fi
  }
}

# row_one <worker> <index>: one row, with its lines in `res/<index>.out` and the mark `done` last.
row_one() {
  row_body "$1" "$2" > "$WORK/res/$2.out" || return 2
  : > "$WORK/res/$2.done"
}

# deal <prefix> <count> <function>: N workers claim the indexes one at a time. A claim is a directory,
# because mkdir is atomic. The printer reads the results in the order of the indexes.
deal() {
  local prefix="$1" count="$2" fn="$3" w i
  mkdir -p "$WORK/$prefix" "$WORK/claim-$prefix"
  w=1
  while [ "$w" -le "$work" ]; do
    (
      i=0
      while [ "$i" -lt "$count" ]; do
        if mkdir "$WORK/claim-$prefix/$i" 2>/dev/null; then "$fn" "$w" "$i" || exit 2; fi
        i=$((i + 1))
      done
    ) &
    w=$((w + 1))
  done
}

# collect <prefix> <count> <the file of a result>: print each result in order, as it is done.
collect() {
  local prefix="$1" count="$2" i=0
  while [ "$i" -lt "$count" ]; do
    while [ ! -e "$WORK/$prefix/$i.done" ]; do
      if [ -e "$WORK/fatal" ]; then cat "$WORK/fatal" >&2; exit 2; fi
      if [ -z "$(jobs -p)" ] && [ ! -e "$WORK/$prefix/$i.done" ]; then
        echo "mutants.sh: a worker ended before it wrote the result $i" >&2; exit 2
      fi
      sleep 0.2
    done
    cat "$WORK/$prefix/$i.out"
    i=$((i + 1))
  done
  wait
  if [ -e "$WORK/fatal" ]; then cat "$WORK/fatal" >&2; exit 2; fi
}

control_failed=0
bad_checks=$'\n'
deal ctl ${#checks[@]} control_one
collect ctl ${#checks[@]}
i=0
while [ "$i" -lt "${#checks[@]}" ]; do
  if [ -e "$WORK/ctl/$i.fail" ]; then
    bad_checks="$bad_checks${checks[$i]}"$'\n'
    control_failed=1
  fi
  i=$((i + 1))
done

deal res "$selected" row_one
collect res "$selected"

died=0; survived=0; noop=0; wrong=0; invalid=0
i=0
while [ "$i" -lt "$selected" ]; do
  case "$(cat "$WORK/res/$i.kind")" in
    died) died=$((died + 1)) ;;
    survived) survived=$((survived + 1)) ;;
    noop) noop=$((noop + 1)) ;;
    wrong) wrong=$((wrong + 1)) ;;
    invalid) invalid=$((invalid + 1)) ;;
  esac
  i=$((i + 1))
done

printf 'MUTANTS selected=%s died=%s survived=%s noop=%s wrong_death=%s invalid=%s\n' \
  "$selected" "$died" "$survived" "$noop" "$wrong" "$invalid"
[ "$died" -eq "$selected" ] && [ "$control_failed" -eq 0 ]
