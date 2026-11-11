#!/usr/bin/env bash
# The declaration emit of a consumer: a project outside the package exports a codec constant, and
# the declaration emitter names each type that the declaration prints.
#
#   scripts/emit-check.sh                 read `dist/` as it stands, compile the project
#   scripts/emit-check.sh --build         run `npm run build` first
#   scripts/emit-check.sh --dist <dir>    read the `dist/` at <dir>, and `package.json` beside it
#
# The package is copied to `node_modules/rotorise` of a temporary directory, so no path of this
# repository helps the emitter to name a type. A type that the entry does not publish is an error
# there (TS2742, TS2883, TS4023 or TS2527). A type that contains itself and has no name prints as
# `any` with no error: TypeScript 5.9 and 6 write `/*elided*/ any`, and TypeScript 5.4 writes `any`
# with no mark. A clean declaration holds no `any`, so the script counts each word `any` as a
# failure. A cycle that goes through a union and a list only is such a hole: see the comment at
# the end of `scripts/emit-check/index.mts`. Every version runs and prints one line. Exit 1 on any
# failure.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 2

# The versions, which `scripts/tsc-matrix.sh` reads too.
. scripts/ts-versions.sh || exit 2

DO_BUILD=0
DIST="$ROOT/dist"
PKG="$ROOT/package.json"
while [ $# -gt 0 ]; do
  case "$1" in
    --build) DO_BUILD=1 ;;
    --dist) shift; DIST="$(cd "${1:?--dist needs a directory}" && pwd)"; PKG="$DIST/../package.json" ;;
    -h|--help) sed -n '2,16p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "emit-check.sh: unknown argument: $1" >&2
       echo "usage: emit-check.sh [--build] [--dist <dir>]" >&2
       exit 2 ;;
  esac
  shift
done

if [ "$DO_BUILD" -eq 1 ]; then
  npm run build >/dev/null 2>&1 || {
    echo 'emit-check.sh: the build failed; run `npm run build` alone to see why' >&2; exit 2; }
fi

if [ ! -f "$DIST/Rotorise.d.ts" ] || [ ! -f "$PKG" ]; then
  echo 'emit-check.sh: dist/ or package.json is absent; run with --build, or run `npm run build`' >&2
  exit 2
fi

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$WORK/node_modules/rotorise"
cp -R "$DIST" "$WORK/node_modules/rotorise/dist"
cp "$PKG" "$WORK/node_modules/rotorise/package.json"
cp scripts/emit-check/index.mts scripts/emit-check/tsconfig.json "$WORK/"

failed=0
for version in "${VERSIONS[@]}"; do
  rm -rf "$WORK/out"
  if out=$(cd "$WORK" && npx --yes --package "typescript@$version" -- tsc -p . --pretty false 2>&1); then
    # `grep -c` exits 0 for a hole, 1 for none, and 2 where the file is absent or unreadable.
    holes=$(grep -cw 'any' "$WORK/out/index.d.mts" 2>/dev/null)
    case $? in
      0) printf 'FAIL  typescript@%s\n' "$version"
         printf '      | the declaration holds %s lines with the type `any`\n' "$holes"
         failed=1 ;;
      1) printf 'PASS  typescript@%s\n' "$version" ;;
      *) printf 'FAIL  typescript@%s\n' "$version"
         printf '      | the compiler wrote no declaration file at out/index.d.mts\n'
         failed=1 ;;
    esac
  else
    printf 'FAIL  typescript@%s\n' "$version"
    printf '%s\n' "$out" | sed 's/^/      | /' | head -20
    failed=1
  fi
done
exit "$failed"
