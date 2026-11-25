#!/usr/bin/env bash
# The consumer types: a small project compiles against the published `dist/`, once per TypeScript
# version.
#
#   scripts/tsc-matrix.sh            read `dist/` as it stands, compile the consumer project
#   scripts/tsc-matrix.sh --build    run `npm run build` first
#   TSC_MATRIX_FAIL_FAST=1 scripts/tsc-matrix.sh    stop at the first compiler that fails
#
# A consumer compiles the published types with its own compiler, and a type can reach a limit there
# that the compiler of the lockfile does not reach. The project resolves `rotorise` through the
# `exports` map of the packed tarball, as a consumer does, and checks the `.d.ts` files too
# (`skipLibCheck` is off). The check copies the project and the tarball to a directory outside the
# repository, so a file that the tarball lacks is absent for the check.
# Every version runs outside the package and prints one line. A line whose compiler prints another
# version than the requested version fails. Then the published entries run under node, in ESM and
# in CJS, and one script per format checks that a class has one identity across the entries.
# Exit 1 on any failure. A row of `scripts/mutants.tsv` needs one failing line, so it sets
# TSC_MATRIX_FAIL_FAST=1: the run stops after the first line that fails, and the later compilers
# and the identity scripts do not run.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 2

# The versions, which `scripts/emit-check.sh` reads too.
. scripts/ts-versions.sh || exit 2
. scripts/packed.sh || exit 2

DO_BUILD=0
for arg in "$@"; do
  case "$arg" in
    --build) DO_BUILD=1 ;;
    -h|--help) sed -n '2,7p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
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

# Each compiler runs in a directory outside the package. Inside the package, the request for a
# version resolves to the `.bin/tsc` of the package, which is TypeScript 6, and each line would
# name a compiler that did not run. The line names the version that the compiler printed, and a
# line whose printed version differs from the requested version fails.
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
# The project sits in `$WORK/consumer`, and the tarball in `$WORK/node_modules/rotorise`: the lookup
# of a package walks up from the project to that directory.
pack_into "$WORK" || { echo 'tsc-matrix.sh: npm pack failed' >&2; exit 2; }
cp -R scripts/consumer "$WORK/consumer"

failed=0
for version in "${VERSIONS[@]}"; do
  out=$(cd "$WORK" && npx --yes --package "typescript@$version" -- \
    sh -c 'tsc --version && tsc -p "$0"' "$WORK/consumer" 2>&1)
  status=$?
  # npx can print a notice before the compiler, so the version is the first line that names one
  ran=$(printf '%s\n' "$out" | sed -n 's/^Version //p' | head -1)
  if [ "$ran" != "$version" ]; then
    printf 'FAIL  typescript@%s\n' "$version"
    printf '      | the compiler printed version `%s`, and the request was for `%s`\n' "$ran" "$version"
    failed=1
  elif [ "$status" -eq 0 ]; then
    printf 'PASS  typescript@%s\n' "$version"
  else
    printf 'FAIL  typescript@%s\n' "$version"
    printf '%s\n' "$out" | grep -v '^Version ' | sed 's/^/      | /' | head -20
    failed=1
  fi
  [ "$failed" -eq 1 ] && [ -n "${TSC_MATRIX_FAIL_FAST:-}" ] && exit 1
done
for format in mjs cjs; do
  if out=$(node "$WORK/consumer/identity.$format" 2>&1); then
    printf '%s\n' "$out"
  else
    printf '%s\n' "$out"
    failed=1
  fi
done
exit "$failed"
