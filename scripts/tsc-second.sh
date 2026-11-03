#!/usr/bin/env bash
# Type-checks the tree on a second compiler, the newest TypeScript 5.x.
# The lockfile compiler checks the tree. A consumer compiles the published types with the
# compiler of the consumer, and a type can reach a limit there that the lockfile compiler does
# not reach.
set -euo pipefail
cd "$(dirname "$0")/.."
rm -f tsconfig.tsbuildinfo
exec npx --yes --package typescript@5.9.3 -- tsc --noEmit
