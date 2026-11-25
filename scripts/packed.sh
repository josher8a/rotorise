# The package as npm publishes it. `pack_into <dir>` runs `npm pack` in the repository and extracts
# the tarball to `<dir>/node_modules/rotorise`. A consumer check reads that directory, so a file that
# `files` or `.npmignore` drops, or an `exports` target outside the tarball, fails the check.
# `scripts/tsc-matrix.sh`, `scripts/emit-check.sh` and `scripts/readme-check.sh` source this file.
# The caller sets ROOT. `npm pack` runs no build: the package has no `prepack` and no `prepare` script.
pack_into() {
  local tarballs name
  tarballs="$(mktemp -d)"
  name="$(cd "$ROOT" && npm pack --silent --pack-destination "$tarballs" | tail -1)" || return 1
  mkdir -p "$1/node_modules/rotorise"
  tar -xzf "$tarballs/$name" -C "$1/node_modules/rotorise" --strip-components=1 || return 1
  rm -rf "$tarballs"
}
