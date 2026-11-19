#!/usr/bin/env bash
# The contract of the decision in `setupVitest.ts`, on a small tree that this script writes: the
# setup of `@ark/attest` runs where the import closure of a selected spec reaches `@ark/attest`,
# and runs where the closure cannot be read. A spec that reaches attest through one import must
# keep the setup, because a run without the setup lets an attest row survive in silence.
# Exit 0 where each probe holds. The script runs `node`, which strips the types of the file.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
T="$WORK/tree"
mkdir -p "$T/src"
cd "$T/src" || exit 2
printf "import { it } from 'vitest'\nimport { a } from './plain'\nit('a', () => a)\n" > plain.spec.ts
printf "export const a = 1\n" > plain.ts
printf "// a comment: import(...) and require(...) name no module\nimport { it } from 'vitest'\nimport { c } from './comment.js'\nit('c', () => c)\n" > comment.spec.ts
printf "// import { attest } from '@ark/attest'\nexport const c = 1\n" > comment.ts
printf "import { it } from 'vitest'\nimport { h } from './helper'\nit('h', () => h)\n" > through.spec.ts
printf "export { attest as h } from '@ark/attest'\n" > helper.ts
printf "import { it } from 'vitest'\nimport { d } from './declared'\nit('d', () => d)\n" > declared.spec.ts
printf "export declare const d: number\n" > declared.d.ts
printf "import { it } from 'vitest'\nit('l', async () => { await import('./lazy') })\n" > lazy.spec.ts
printf "import { attest } from '@ark/attest'\nexport const l = attest\n" > lazy.ts
printf "import { it } from 'vitest'\nconst name = './plain'\nit('n', async () => { await import(name) })\n" > computed.spec.ts
printf "import { it } from 'vitest'\nimport { m } from './missing'\nit('m', () => m)\n" > missing.spec.ts
# A flag can be a substring of the path of a spec, so the script reads a flag as a flag.
printf "import { it } from 'vitest'\nit('t', () => 1)\n" > dash-t.spec.ts

cat > "$WORK/drive.mts" <<DRIVE
import { reachesAttest, selectedSpecs } from '$ROOT/setupVitest.ts'
const spec = (n: string) => '$T/src/' + n + '.spec.ts'
const want: [string, boolean][] = [
    ['plain', false], ['comment', false], ['declared', false],
    ['through', true], ['lazy', true], ['computed', true], ['missing', true],
]
for (const [n, reach] of want)
    console.log((reachesAttest([spec(n)]) === reach ? 'PASS' : 'FAIL') + '  a spec "' + n + '" ' + (reach ? 'keeps' : 'skips') + ' the setup')
const mixed = reachesAttest([spec('plain'), spec('through')])
console.log((mixed ? 'PASS' : 'FAIL') + '  one spec that reaches attest keeps the setup of the run')
const sel = (args: string[]) => selectedSpecs(args, '$T')
console.log((sel(['plain'])?.length === 1 ? 'PASS' : 'FAIL') + '  an argument selects the specs whose path holds the text')
console.log((sel([]) === null ? 'PASS' : 'FAIL') + '  no argument selects every spec')
console.log((sel(['-t', 'plain']) === null ? 'PASS' : 'FAIL') + '  a flag selects every spec')
console.log((sel(['nothing']) === null ? 'PASS' : 'FAIL') + '  an argument that matches no spec selects every spec')
DRIVE
out=$(node "$WORK/drive.mts" 2>&1)
printf '%s\n' "$out"
printf '%s\n' "$out" | grep -qE '^FAIL|rror' && exit 1
[ "$(printf '%s\n' "$out" | grep -c '^PASS')" -eq 12 ] || { echo 'FAIL  the driver printed fewer probes than expected'; exit 1; }
exit 0
