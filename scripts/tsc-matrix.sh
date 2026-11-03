#!/usr/bin/env bash
# The consumer types: a small project compiles against the published `dist/`, once per TypeScript
# version.
#
#   scripts/tsc-matrix.sh            read `dist/` as it stands, compile the consumer project
#   scripts/tsc-matrix.sh --build    run `npm run build` first
#
# A consumer compiles the published types with its own compiler, and a type can reach a limit there
# that the compiler of the lockfile does not reach. The project resolves `rotorise` through the
# `exports` map, as a consumer does, and checks the `.d.ts` files too (`skipLibCheck` is off).
# Every version runs and prints one line. Exit 1 on any failure.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 2

# The minimum supported version (`NoInfer` in the published types needs 5.4), then the latest of
# each major.
VERSIONS=(5.4.5 5.9.3 6.0.3 7.1.0-beta)

DO_BUILD=0
for arg in "$@"; do
  case "$arg" in
    --build) DO_BUILD=1 ;;
    -h|--help) sed -n '2,6p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "tsc-matrix.sh: unknown argument: $arg" >&2
       echo "usage: tsc-matrix.sh [--build]" >&2
       exit 2 ;;
  esac
done

if [ "$DO_BUILD" -eq 1 ]; then
  npm run build >/dev/null 2>&1 || {
    echo 'tsc-matrix.sh: the build failed; run `npm run build` alone to see why' >&2; exit 2; }
fi

if [ ! -f dist/Rotorise.d.ts ] || [ ! -f dist/Rotorise.d.cts ]; then
  echo 'tsc-matrix.sh: dist/ is absent; run with --build, or run `npm run build`' >&2
  exit 2
fi

# The name `rotorise` resolves to this repository, so the `exports` map decides what a file reads.
mkdir -p scripts/consumer/node_modules
ln -sfn ../../.. scripts/consumer/node_modules/rotorise

failed=0
for version in "${VERSIONS[@]}"; do
  if out=$(npx --yes --package "typescript@$version" -- tsc -p scripts/consumer 2>&1); then
    printf 'PASS  typescript@%s\n' "$version"
  else
    printf 'FAIL  typescript@%s\n' "$version"
    printf '%s\n' "$out" | sed 's/^/      | /' | head -20
    failed=1
  fi
done
exit "$failed"
