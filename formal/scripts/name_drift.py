#!/usr/bin/env python3
"""Find names the documents cite that `Calculus/` no longer defines.

`fidelity_audit.py` measures whether a theorem can be reviewed in isolation;
`vocab_audit.py` measures whether a proof reads in codec vocabulary. Neither asks
the question that a refactoring arc actually breaks:

    does every Lean name a document names still exist?

Prose does not typecheck. Deleting a declaration leaves the build green and every
citation of it dangling, and the two drift findings before the residue sweep were
both caught by luck rather than by a check.

A hit is a backticked token that *looks* like a Lean name — has a `_` or a `.`, no
spaces — and matches no identifier occurring anywhere in `Calculus/*.lean`. That is
deliberately loose on the source side: any occurrence counts, not just a declaration,
so a structure projection or a mathlib lemma used in one proof is enough to clear a
citation of it. The residue is therefore small and worth reading by hand.

Three classes of false positive are filtered. Naming *patterns* (`X_e`, `lawful_X`,
`_p_admits` in `VOCABULARY.md`) and filenames are filtered by shape. Structure
projections are cleared component-wise: `Carrier.ranP` is legitimate when `Carrier` and
`ranP` both occur, even though the sources never write the two together.

What is left is a small `EXPECTED` table, each entry carrying the reason it is not a
defect — a mathlib name cited as future work, or a name in `FIDELITY.md`'s dated
snapshot, which says in its own header that its citations are left as they were. An
entry there is a claim that the citation is deliberate. **Deleting a declaration named
in `EXPECTED` without amending the reason is the failure this file exists to catch.**

A hit in `docs/codec-formalization.md` §4 is usually not a defect: that file is the
change log, it says so, and a name there records what was reasoned with at the time.
Hits in the current-state documents — `formal/README.md`, `formal/ARCHITECTURE.md`,
`formal/FIDELITY.md`, `formal/VOCABULARY.md`, `docs/codec-calculus.md`,
`docs/structural-discipline.md` —
are broken pointers and should be fixed or explicitly marked superseded.

Usage:  python3 scripts/name_drift.py            (run from formal/)
        python3 scripts/name_drift.py --all      (include the change log)
Exit code 1 if any current-state document has a hit.
"""
import re, sys, os, glob

CURRENT = ["README.md", "ARCHITECTURE.md", "FIDELITY.md", "VOCABULARY.md",
           "../docs/codec-calculus.md", "../docs/structural-discipline.md"]
# Scanned under --all, reported, never failing. Both are part change log and part live
# document, so a name that no longer exists may be a deliberate record of a deletion —
# `codec-audit.md`'s struck queue items are exactly that — or may be real drift. A human
# reads the list; a check cannot tell the two apart.
LOG = ["../docs/codec-formalization.md", "../docs/codec-audit.md"]

IDENT = re.compile(r"[^\W\d][\w'!?⁺₀-₉]*(?:\.[^\W\d][\w'!?⁺₀-₉]*)*", re.UNICODE)
BACKTICKED = re.compile(r"`([^`\n]{2,80})`")
LEANISH = re.compile(r"^[^\W\d][\w'!?⁺₀-₉]*(?:\.[^\W\d][\w'!?⁺₀-₉]*)*$", re.UNICODE)
# naming patterns and filenames, not citations
NOISE = re.compile(r"\.(md|py|ts|lean|json|toml|sh)$|(^|[._])X([._]|$)|^_|^f_sound$")

# Cited on purpose, with the reason. Keyed by document, then name.
EXPECTED = {
    "README.md": {
        "List.Perm": "mathlib; named as the next probe, not as something proved here",
    },
    "VOCABULARY.md": {
        "List.Perm": "same, at the set-equality row",
    },
    "FIDELITY.md": {
        "List.Perm": "same",
        "denoteω_eq": "the ω layer this snapshot measures, named as deleted in its own header",
        "numericCodec_eq_restrict": "cited with its commit; `(numeric)` was removed after it",
        "ident_sound": "the proposal in a struck row; the delivered names follow it",
    },
    "../docs/codec-calculus.md": {
        "e_c": "the specification's own notation for a component codec, not a Lean name",
    },
}


def occurring():
    """Every identifier, and every dotted sub-path of one, appearing in the sources."""
    src = "".join(open(f).read() for f in sorted(glob.glob("Calculus/*.lean")))
    out = set()
    for tok in IDENT.findall(src):
        parts = tok.split(".")
        for i in range(len(parts)):
            for j in range(i + 1, len(parts) + 1):
                out.add(".".join(parts[i:j]))
    return out


def scan(path, present):
    expected = EXPECTED.get(path, {})
    hits, seen, stale = [], set(), []
    for lineno, line in enumerate(open(path).read().split("\n"), 1):
        for tok in BACKTICKED.findall(line):
            t = tok.strip()
            if not LEANISH.match(t) or NOISE.search(t):
                continue
            if "_" not in t and "." not in t:
                continue
            if t in seen:
                continue
            seen.add(t)
            # a structure projection is fine when both halves occur
            if t in present or all(part in present for part in t.split(".")):
                continue
            if t in expected:
                continue
            hits.append((lineno, t))
    for name in expected:
        if name not in seen:
            stale.append(name)
    return hits, stale


def main():
    if not glob.glob("Calculus/*.lean"):
        sys.exit("run from formal/")
    present = occurring()
    targets = CURRENT + (LOG if "--all" in sys.argv else [])
    failed = False
    for path in targets:
        if not os.path.exists(path):
            continue
        hits, stale = scan(path, present)
        label = os.path.normpath(path)
        current = path in CURRENT
        if not hits and not stale:
            print(f"  {label:38s} clean")
            continue
        if hits:
            if current:
                failed = True
            print(f"  {label:38s} {len(hits)} {'BROKEN' if current else 'in the change log'}")
            for lineno, name in hits:
                print(f"      {lineno:6d}  {name}")
        if stale:
            failed = True
            print(f"  {label:38s} {len(stale)} stale EXPECTED entr{'y' if len(stale) == 1 else 'ies'}")
            for name in stale:
                print(f"              {name}  (no longer cited — drop it from EXPECTED)")
    if "--all" not in sys.argv:
        print("\n  (--all also scans docs/codec-formalization.md, the change log)")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
