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

# Every `export { … };` statement, one published name per line.
#
# In `python3` and not in `sed`, for the same reason the guards under `formal/scripts` are:
# this extraction is where the row went wrong three times, and BSD `sed` and GNU `sed` do not
# agree on `\?`. Bash runs the build and reads the exit codes; Python does the parsing.
names() {
  python3 - "$1" <<'PYEOF'
import re, sys

# A clause is one line. `tsup` writes the re-export and the local export as a line each, so this
# reads lines and does not accumulate. An earlier version accumulated to the next `};` and
# swallowed thirty-six lines of declarations, which is why it answered 145.
CLAUSE = re.compile(r"^export \{(.*?)\}(?: from .*)?;\s*$")

names = set()
for line in open(sys.argv[1], encoding="utf-8"):
    clause = CLAUSE.match(line.rstrip("\n"))
    if clause is None:
        continue
    for member in clause.group(1).split(","):
        member = member.strip()
        if not member:
            continue
        member = re.sub(r"^type\s+", "", member)
        # the published name is the right of ` as `, never the left: the re-export line aliases
        # every name (`k as AllObjects`) and the left is the bundler's mangled local, which is
        # why the row once answered 215
        member = re.sub(r"^.*\s+as\s+", "", member)
        names.add(member)
for name in sorted(names):
    print(name)
PYEOF
}

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
