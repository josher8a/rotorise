#!/usr/bin/env bash
# The contract of the version check in `scripts/tsc-matrix.sh`, on a small tree that this script
# writes. A stub of `npx` prints the version that the line requested, or the version of the
# variable STUB_RAN. A line whose compiler prints another version must fail, and the failure must
# name both versions. Exit 0 where each probe holds.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$WORK/tree/scripts/consumer" "$WORK/tree/dist" "$WORK/bin"
cp "$HERE/tsc-matrix.sh" "$HERE/ts-versions.sh" "$WORK/tree/scripts/"
touch "$WORK/tree/dist/Rotorise.d.ts" "$WORK/tree/dist/Rotorise.d.cts"
touch "$WORK/tree/scripts/consumer/identity.mjs" "$WORK/tree/scripts/consumer/identity.cjs"
printf 'VERSIONS=(5.4.5 7.1.0-beta)\n' > "$WORK/tree/scripts/ts-versions.sh"

# The stub reads the version from the argument `typescript@<version>`.
cat > "$WORK/bin/npx" <<'STUB'
#!/usr/bin/env bash
for arg in "$@"; do
  case "$arg" in typescript@*) requested="${arg#typescript@}" ;; esac
done
if [ -n "${STUB_RAN:-}" ] && [ "$requested" = 7.1.0-beta ]; then requested="$STUB_RAN"; fi
if [ -n "${STUB_NOTICE:-}" ]; then echo "npm notice New minor version of npm available"; fi
echo "Version $requested"
STUB
# The identity scripts are no part of this contract: a stub of `node` replaces them.
printf '#!/usr/bin/env bash\necho "PASS  stub $1"\n' > "$WORK/bin/node"
chmod +x "$WORK/bin/npx" "$WORK/bin/node"

failed=0
# probe <name> <the exit that the run must give> <a word that the output must hold> <STUB_RAN> [notice]
probe() {
  local name="$1" want="$2" word="$3" ran="$4" out ec
  out=$(cd "$WORK/tree" && PATH="$WORK/bin:$PATH" STUB_RAN="$ran" STUB_NOTICE="${5:-}" bash scripts/tsc-matrix.sh 2>&1)
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

probe 'a line whose compiler prints the requested version passes' 0 'PASS  typescript@7.1.0-beta' ''
probe 'a line whose compiler prints another version fails' 1 'printed version `6.0.3`, and the request was for `7.1.0-beta`' 6.0.3
probe 'a notice of npx before the version does not fail the line' 0 'PASS  typescript@7.1.0-beta' '' notice
exit "$failed"
