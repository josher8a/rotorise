#!/usr/bin/env python3
"""Check that no docstring in `src/` sits above a declaration that is not its own.

JSDoc binds the *last* docstring before a declaration. So when two `/** … */` blocks
close and open with nothing between them, every block but the last describes nothing a
reader can reach: it renders in no tooltip, no `{@link}` resolves to it, and no check
in this repository reads it. It is prose that has come unmoored from its subject.

That is not hypothetical. A scripted deletion removes a declaration and leaves the
comment above it, and the comment drifts down onto whatever comes next:

  * `14b2912` deleted `admits` and its 35-line docstring came to rest above `accepts`,
    which briefly carried prose describing a function that no longer existed.
  * `6394182` found six more in one pass: `union`'s three, whose functions had moved to
    `term.ts`; `setBase`'s, resting on `constantOf`; `Encoded`'s and `EncodedBy`'s,
    fifty lines above two published types that carried no docstring at all; a deleted
    `untagged`'s; `fuelFor`'s in `lean.ts`, above `fuelForValue`; and one in
    `codec.laws.spec.ts` describing a `held` test while sitting above a `nullable` one.

Three passes in a row, and every check stayed green through all of them: `tsc` does not
read a comment, `biome` does not, `name_drift.py` reads the Lean side, and the suite
passes either way. Nothing else in this tree can see it.

WHAT THIS CHECKS, AND WHAT IT CANNOT

The signature is structural: a `*/` line followed, past blank lines, by a `/**` line.
That is a superset of the defect, because two-part prose is a real style here — a
standing note above a specific note, both about the declaration below. So a run is
allowed when its earlier blocks are marked deliberate.

THE MARKER

Put `@anchored` on a line of the *earlier* block to say it belongs to the declaration
below alongside the block that follows it:

    /**
     * Pins wording, because the message is the only channel this fact travels on.
     * @anchored
     */
    /** ... the specific note ... */
    it('...', () => {

`conformance.spec.ts` carries this pattern twice. A module docstring at the head of a file needs no marker: nothing precedes it,
so it is the file's own and is skipped by construction.

The sharper question this cannot ask is whether the first sentence names a declaration
that is not the one below it. That needs a reader. This narrows the reading to the runs
it finds.
"""

import os
import sys

SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "src")
MARKER = "@anchored"


def blocks(lines):
    """Every comment block in the file, as (start, end, is_doc) over 0-indexed lines.

    A block comment can open and close on one line — `/** text */` is the commonest
    docstring in this tree — so a scanner that looks for a bare `*/` misses the whole
    single-line form. That gap was live in the first version of this script and was
    found by planting an orphan it did not report.
    """
    out = []
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        if stripped.startswith("/*"):
            is_doc = stripped.startswith("/**")
            start = i
            # `/*` and `*/` on one line closes immediately; `/**/` is not an opener
            if stripped.endswith("*/") and len(stripped) > 3:
                out.append((start, i, is_doc))
            else:
                while i < len(lines) and not lines[i].rstrip().endswith("*/"):
                    i += 1
                out.append((start, min(i, len(lines) - 1), is_doc))
        i += 1
    return out


def unanchored(path):
    """Every docstring in `path` that another docstring follows, and that is not marked."""
    with open(path, encoding="utf-8") as handle:
        lines = handle.read().split("\n")

    found = []
    every = blocks(lines)
    for n, (start, end, is_doc) in enumerate(every):
        if not is_doc or n + 1 >= len(every):
            continue

        # what follows, past blank lines
        j = end + 1
        while j < len(lines) and not lines[j].strip():
            j += 1
        nxt_start, _, nxt_is_doc = every[n + 1]
        # only a *docstring* immediately after steals the binding; a plain `/* */`
        # section note binds to nothing itself and leaves this one attached
        if not nxt_is_doc or nxt_start != j:
            continue

        # a module docstring has nothing but blanks above it, so it is the file's own
        if all(not x.strip() for x in lines[:start]):
            continue

        if MARKER in "\n".join(lines[start : end + 1]):
            continue
        first = lines[start + 1].strip() if end > start else lines[start].strip()
        found.append((start + 1, first[:72]))
    return found


def main():
    if not os.path.isdir(SRC):
        sys.exit(f"no src/ at {SRC} — run from formal/scripts or formal/")

    # recursive: `src/` nests its directories, and a flat listing passes over a nested file in silence
    files = sorted(os.path.relpath(os.path.join(root, f), SRC)
                   for root, _, names in os.walk(SRC) for f in names if f.endswith(".ts"))
    hits = [(f, w) for f in files for w in [unanchored(os.path.join(SRC, f))] if w]

    total = sum(len(w) for _, w in hits)
    print(f"docstring_anchor: {len(files)} files in src/")

    if not total:
        print("  every docstring binds to the declaration below it.")
        print(f"  (structural only — a run marked `{MARKER}` is taken at its word)")
        return 0

    print(f"\n  UNANCHORED: {total} docstring(s) that bind to no declaration.")
    print("  JSDoc binds the last block before a declaration, so these describe nothing:")
    for name, where in hits:
        for line, first in where:
            print(f"      src/{name}:{line}  {first}")
    print(f"\n  Fix: move the block onto the declaration it describes, or delete the")
    print(f"  sentences the live declaration already carries. If the run is deliberate")
    print(f"  — a standing note above a specific one, both about the declaration below")
    print(f"  — add `{MARKER}` to the earlier block.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
