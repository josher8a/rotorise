#!/usr/bin/env bash
# The published name set: the export set of the three entries, against a baseline.
#
#   scripts/surface-names.sh            read `dist/` as it stands, compare, print
#   scripts/surface-names.sh --build    run `npm run build` first
#   scripts/surface-names.sh --accept   rewrite the baselines, printing every move first
#
# The baselines are `scripts/surface/*.txt`, one name per line, sorted. A move is a decision:
# `--accept` prints what changed, and the commit message names it. Exit 1 on any difference.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 2

ENTRIES=(Rotorise testing native)
BASE_DIR=scripts/surface
DO_BUILD=0
ACCEPT=0

for arg in "$@"; do
  case "$arg" in
    --build)  DO_BUILD=1 ;;
    --accept) ACCEPT=1 ;;
    -h|--help) sed -n '2,9p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "surface-names.sh: unknown argument: $arg" >&2
       echo "usage: surface-names.sh [--build] [--accept]" >&2
       exit 2 ;;
  esac
done

if [ "$DO_BUILD" -eq 1 ]; then
  npm run build >/dev/null 2>&1 || {
    echo 'surface-names.sh: the build failed; run `npm run build` alone to see why' >&2; exit 2; }
fi

# The export names of a declaration file, one per line. `surface-names.mjs` asks the compiler, so
# the layout that the bundler writes (`export declare` in place, or one `export { … }` clause) does
# not change the answer.
names() { node scripts/surface-names.mjs "$1"; }

fail=0
for entry in "${ENTRIES[@]}"; do
  dts="dist/$entry.d.ts"
  base="$BASE_DIR/$entry.txt"
  if [ ! -f "$dts" ]; then
    echo "FAIL  $entry: no $dts — run with --build"; fail=1; continue
  fi
  current="$(names "$dts")"
  if [ "$ACCEPT" -eq 1 ]; then
    if [ -f "$base" ] && [ "$current" = "$(cat "$base")" ]; then
      printf 'SAME  %-10s %s names\n' "$entry" "$(printf '%s\n' "$current" | wc -l | tr -d ' ')"
    else
      printf 'MOVED %-10s %s names\n' "$entry" "$(printf '%s\n' "$current" | wc -l | tr -d ' ')"
      [ -f "$base" ] && diff "$base" <(printf '%s\n' "$current") | sed 's/^/      /'
      printf '%s\n' "$current" > "$base"
    fi
    continue
  fi
  if [ ! -f "$base" ]; then
    echo "FAIL  $entry: no baseline at $base — run with --accept"; fail=1; continue
  fi
  if [ "$current" = "$(cat "$base")" ]; then
    printf 'PASS  %-10s %s names\n' "$entry" "$(printf '%s\n' "$current" | wc -l | tr -d ' ')"
  else
    printf 'FAIL  %-10s %s names, baseline %s\n' "$entry" \
      "$(printf '%s\n' "$current" | wc -l | tr -d ' ')" "$(wc -l < "$base" | tr -d ' ')"
    diff "$base" <(printf '%s\n' "$current") | sed 's/^/      /'
    fail=1
  fi
done

echo
if [ "$ACCEPT" -eq 1 ]; then echo 'BASELINES WRITTEN'; exit 0; fi
if [ $fail -eq 0 ]; then echo 'SURFACE UNMOVED'; exit 0; fi
echo 'SURFACE MOVED — name every move in the commit message, then `--accept`'
exit 1
