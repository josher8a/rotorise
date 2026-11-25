#!/usr/bin/env bash
# The README samples: each `ts` block is compiled against `dist/` with `skipLibCheck: false`, each
# block that holds no `declare const` runs, and each `// =>` comment is compared with the value.
#
#   scripts/readme-check.sh                  read `dist/` as it stands, check README.md
#   scripts/readme-check.sh --build          run `npm run build` first
#   scripts/readme-check.sh --dist <dir>     read the `dist/` at <dir>, and `package.json` beside it
#   scripts/readme-check.sh --readme <file>  check another file, for a probe of the check
#
# The package is copied to `node_modules/rotorise` of a temporary directory, so a sample resolves
# the package as a consumer does. `scripts/readme-check.mjs` says what the check reads and refuses.
# One line for each block. Exit 1 on any failure, and 2 where the check cannot start.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 2

DO_BUILD=0
DIST="$ROOT/dist"
PKG="$ROOT/package.json"
README="$ROOT/README.md"
while [ $# -gt 0 ]; do
  case "$1" in
    --build) DO_BUILD=1 ;;
    --dist) shift; DIST="$(cd "${1:?--dist needs a directory}" && pwd)"; PKG="$DIST/../package.json" ;;
    --readme) shift; README="$(cd "$(dirname "${1:?--readme needs a file}")" && pwd)/$(basename "$1")" ;;
    -h|--help) sed -n '2,13p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "readme-check.sh: unknown argument: $1" >&2
       echo "usage: readme-check.sh [--build] [--dist <dir>] [--readme <file>]" >&2
       exit 2 ;;
  esac
  shift
done

if [ "$DO_BUILD" -eq 1 ]; then
  npm run build >/dev/null 2>&1 || {
    echo 'readme-check.sh: the build failed; run `npm run build` alone to see why' >&2; exit 2; }
fi

if [ ! -f "$DIST/Rotorise.d.ts" ] || [ ! -f "$PKG" ] || [ ! -f "$README" ]; then
  echo 'readme-check.sh: dist/, package.json or the README is absent; run with --build, or run `npm run build`' >&2
  exit 2
fi

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$WORK/node_modules/rotorise"
cp -R "$DIST" "$WORK/node_modules/rotorise/dist"
cp "$PKG" "$WORK/node_modules/rotorise/package.json"
node scripts/readme-check.mjs "$README" "$WORK"
