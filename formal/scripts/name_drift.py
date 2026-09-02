#!/usr/bin/env python3
"""Find names the documents cite that `Calculus/` no longer defines.

`fidelity_audit.py` measures whether a theorem can be reviewed in isolation;
`vocab_audit.py` measures whether a proof reads in codec vocabulary. Neither asks
the question that a refactoring arc actually breaks:

    does every Lean name a document names still exist?

Prose does not typecheck. Deleting a declaration leaves the build green and every
citation of it dangling, and the two drift findings before the residue sweep were
both caught by luck rather than by a check.

A hit is a backticked token that *looks* like a Lean name — no spaces, and either a `_`
or a `.` in it or else a single word that is not one of four categories that cannot be
`Calculus/` names (see `single_word_checkable`) — and matches no identifier occurring
anywhere in `Calculus/*.lean`. That is
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

**What it cannot catch is an entry keyed to a document that no longer exists.** `scan()` runs
per target, so the stale check only fires for documents still in `CURRENT`; three entries keyed
to `docs/structural-discipline.md` became unreachable the moment that file left the list, and
nothing reported them. They were removed by hand. If a document is dropped from `CURRENT`, drop
its `EXPECTED` block in the same edit.

Two defects were found by the change that turned single-word checking on, and both had been
invisible for months, so they are worth naming as evidence that the blind spot was real:
`Item` in `README.md`'s module inventory, deleted from the model on purpose in `f3bb956` and
still listed as something `Domain.lean` defines; and `lookup_rel`, cited by `FIDELITY.md` and
deleted in `e9ac3be`. The second was not a single-word citation at all — it was hidden by the
tokenizer bug described at `BACKTICKED`, which means the guard's *existing* job was also
incomplete. A guard that is loose in a way nobody has measured is a guard whose passes mean
less than they look like.

**Lean docstrings are scanned too**, and were not for most of this development's life. A
citation inside a proof's docstring is a broken pointer on exactly the same terms as one in a
document, and there are far more of them; the only reason they were not checked is that the
`CURRENT` list was written by hand from the `docs/` directory.

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
           "../docs/codec-calculus.md"]
# **The docstrings, which this guard never read.** Every module here is dense with backticked
# names and none of them was checked — 763 distinct citations, invisible. Demonstrated rather
# than assumed: writing `nullHonest_of_ownsNull_false` for `nullHonest_of_not_ownsNull` in a
# `Soundness.lean` docstring passed this guard clean. They are `CURRENT`, not a reported-only
# list, because at the time of adding them none dangled — so the bar is "keep it at zero",
# which is only meaningful if breaking it fails the build.
CURRENT += sorted(glob.glob("Calculus/*.lean"))
# `LOG` held `docs/codec-formalization.md` and `docs/codec-audit.md` — scanned under `--all`,
# reported, never failing, because a name missing from a change log may be a deliberate record
# of a deletion rather than drift and no check can tell those apart. Both files are deleted;
# `git log` is the change log now, and a commit message is not a document to scan. The list
# stays as the hook for any future reported-only target.
LOG = []

IDENT = re.compile(r"[^\W\d][\w'!?⁺₀-₉]*(?:\.[^\W\d][\w'!?⁺₀-₉]*)*", re.UNICODE)
# **`{1,80}`, and it matters.** With a `{2,80}` minimum a one-character code span (`` `7` ``,
# `` `N` ``, `` `q` ``) fails to match, the scanner resumes *inside* the pairing, and the next
# match is the prose between two spans — which `.strip()` then turned into a plausible
# identifier. That is how `becomes`, `carries` and `are` used to be reported as Lean names, and,
# far worse, how 13 real citations were swallowed into prose runs and never checked at all. One
# of the 13 was `lookup_rel`, deleted in `e9ac3be` and dangling in `FIDELITY.md` ever since.
# The token is now used exactly as captured; a capture with a space in it fails `LEANISH`.
BACKTICKED = re.compile(r"`([^`\n]{1,80})`")
LEANISH = re.compile(r"^[^\W\d][\w'!?⁺₀-₉]*(?:\.[^\W\d][\w'!?⁺₀-₉]*)*$", re.UNICODE)
# naming patterns and filenames, not citations
NOISE = re.compile(r"\.(md|py|ts|lean|json|toml|sh)$|(^|[._])X([._]|$)|^_|^f_sound$")

# Cited on purpose, with the reason. Keyed by document, then name.
EXPECTED = {
    "README.md": {
        "List.Perm": "mathlib; named as the next probe, not as something proved here",
        "mono": "the ccpo/`partial_fixpoint` obligation's conventional name; `altCodec_not_monotone` is ours",
    },
    "ARCHITECTURE.md": {
        "mono": "same as `README.md`'s — the ccpo obligation's conventional name, at §7's "
                "not-modelled row",
    },
    "VOCABULARY.md": {
        "List.Perm": "same, at the set-equality row",
        "cLitStr": "cited *as* the opaque name that `unionLiteralString` replaced — the example is the point",
        "fbDefaults": "a struck row recording a completed item; the name was retired by the same change (`c740a96` region)",
    },
    "FIDELITY.md": {
        "List.Perm": "same",
        "denoteω_eq": "the ω layer this snapshot measures, named as deleted in its own header",
        "numericCodec_eq_restrict": "cited with its commit; `(numeric)` was removed after it",
        "ident_sound": "the proposal in a struck row; the delivered names follow it",
        "termDepth": "the ω layer this snapshot measures; its own header names it as deleted",
        "checkUniqueAdmission": "`src/testing.ts`, and the sentence says so; not a `Calculus/` name",
        "numericCodec": "removed with `(numeric)` at JH's call, after `numericCodec_eq_restrict` above",
        "Item": "§1's wire type, deleted from the model in `f3bb956`; this snapshot predates that",
        "lookup_rel": "`Lists.lean`'s keyed clause, deleted in `e9ac3be` when the field table "
                      "became a key set with a function on it. **Found by fixing this script's "
                      "tokenizer** — the citation had been swallowed into a prose run since then.",
    },
    "../docs/codec-calculus.md": {
        "e_c": "the specification's own notation for a component codec, not a Lean name",
        "Encoded": "§1's own wire type, named by the specification; the model has no Lean type for it",
    },
}


# A single-word citation is checked against the same source set as a dotted one — any
# identifier occurring anywhere in `Calculus/*.lean`. Four categories can never occur there
# and are skipped by shape rather than by name, so the list cannot rot:
#
#   MODULE_NAMES  a module is a filename, not a declaration. `Denote` names a file; the dotted
#                 form `Calculus.Denote` is already cleared component-wise.
#   PRELUDE       Lean, mathlib and Batteries names, and Lean keywords, cited as *the language*
#                 rather than as this development's API. `Bool` and `structure` are not ours to
#                 define, and a linter name (`docBlame`) belongs to Batteries.
#   len <= 2      the specification's notation — `N`, `SS`, `Uν`, `lA`, `oᵢ`. A two-character
#                 token matches something almost everywhere, so checking it measures nothing.
#   commit hashes seven or more hex digits. `c66d493` is a citation of the record, not of a name.
#
# Everything else is checked. That is 194 citations the guard was blind to before, and it caught
# `Item` in `README.md`'s module inventory — deleted on purpose in `f3bb956` and still listed as
# something `Domain.lean` defines.
MODULE_NAMES = {os.path.splitext(os.path.basename(f))[0]
                for f in glob.glob("Calculus/*.lean")} | {"Calculus"}
HASH = re.compile(r"^[0-9a-f]{7,}$")
PRELUDE = set("""
Bool Prop Type Sort Nat Int String Char Unit True False And Or Not Iff Eq Option Some None
List Array Finset Set Subtype Quot Quotient Decidable DecidableEq Repr BEq Inhabited Nonempty
Function Equivalence Forall₂ Perm Prod Sum Classical Exists Std Batteries Lean Mathlib
sizeOf casesOn recOn binductionOn brecOn noConfusion propext sorry rfl decide simp omega
deriving instance structure inductive theorem lemma abbrev mutual noncomputable partial unsafe
def example where match with fun let have show this at using
docBlame unreachableTactic simpNF EXPECTED CURRENT PRELUDE LOG HEAD defaultTargets grep
""".split())


def single_word_checkable(t):
    """Is this single-word citation one the guard can hold `Calculus/` to?"""
    return not (len(t) <= 2 or HASH.match(t) or t in MODULE_NAMES or t in PRELUDE)


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
            t = tok
            if not LEANISH.match(t) or NOISE.search(t):
                continue
            if "_" not in t and "." not in t and not single_word_checkable(t):
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
    if LOG and "--all" not in sys.argv:
        print(f"\n  (--all also scans {', '.join(os.path.normpath(p) for p in LOG)})")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
