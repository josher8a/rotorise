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
`Calculus/` names (see `single_word_checkable`) — and matches no identifier occurring in
**the code** of `Calculus/*.lean`, comments and docstrings stripped (`occurring()`).
It stays deliberately loose about *where* in the code: any occurrence clears a citation, not
just a declaration, so a structure projection or a mathlib lemma appealed to in one proof is
enough. The residue is therefore small and worth reading by hand.

**Stripping the comments is what makes the check mean anything, and it is not free.** The
source set was raw file text until `6a90359`'s defect was measured, which made a name cited
only in a docstring its own evidence. Code-only closes that, and immediately raises the
question the marker convention answers: a docstring that names a *deleted* declaration on
purpose looks exactly like one that names a renamed declaration by accident. See `RETIRED`.

Three classes of false positive are filtered. Naming *patterns* (`X_e`, `lawful_X`,
`_p_admits`) and filenames are filtered by shape. Structure
projections are cleared component-wise: `Carrier.ranP` is legitimate when `Carrier` and
`ranP` both occur, even though the sources never write the two together.

What is left is a small `EXPECTED` table, each entry carrying the reason it is not a
defect — a mathlib name cited as future work, or a name a document cites *as* something
that was retired, where the retirement is the point. An
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
still listed as something `Domain.lean` defines; and `lookup_rel`, cited by the
representation audit and deleted in `e9ac3be`. The second was not a single-word citation at all — it was hidden by the
tokenizer bug described at `BACKTICKED`, which means the guard's *existing* job was also
incomplete. A guard that is loose in a way nobody has measured is a guard whose passes mean
less than they look like.

**Lean docstrings are scanned too**, and were not for most of this development's life. A
citation inside a proof's docstring is a broken pointer on exactly the same terms as one in a
document, and there are far more of them; the only reason they were not checked is that the
`CURRENT` list was written by hand from the `docs/` directory.

**Four reasons a cited name can be legitimately absent, and each has its own place.** Keeping
them apart is most of this file, because a single undifferentiated exception list would say
nothing about *why* any entry is in it:

    ~~marked~~   retired: the declaration is gone and the prose says so (`RETIRED`, §9)
    PRELUDE      the language: Lean, mathlib, Batteries — judged by root namespace
    HOST         `src/`'s names, at §8's boundary — live, just not here
    SPEC         the specification's own notation, from `docs/codec-calculus.md`
    EXPECTED     a genuine one-off, keyed to the document that makes it

When this split was first measured the four absorbed 99 of 169 hits between them, the marks
took 60, and 18 stale pointers were left — which is the number the guard exists to report.

Hits in the current-state documents — `formal/README.md`, `formal/ARCHITECTURE.md`,
`docs/codec-calculus.md`,
`docs/structural-discipline.md` —
are broken pointers and should be fixed or explicitly marked superseded.

Usage:  python3 scripts/name_drift.py            (run from formal/)
        python3 scripts/name_drift.py --all      (include the change log)
Exit code 1 if any current-state document has a hit, a stale `EXPECTED` entry, or a
`~~name~~` whose name is still in the sources.
"""
import re, sys, os, glob

CURRENT = ["README.md", "ARCHITECTURE.md", "../docs/codec-calculus.md"]
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
# of the 13 was `lookup_rel`, deleted in `e9ac3be` and dangling ever since.
# The token is now used exactly as captured; a capture with a space in it fails `LEANISH`.
BACKTICKED = re.compile(r"`([^`\n]{1,80})`")
LEANISH = re.compile(r"^[^\W\d][\w'!?⁺₀-₉]*(?:\.[^\W\d][\w'!?⁺₀-₉]*)*$", re.UNICODE)
# **A name the sources do not define is marked, not backticked** — `~~oldName~~` — and this
# guard reads only the unmarked citations. Usually the name is retired; sometimes it never
# existed (`depthP`, a companion `Value.depth`'s map row has no list to need). That convention is `ARCHITECTURE.md` §9's, and it exists because the check
# below cannot work without it: once the source set is code, a docstring that names a deleted
# declaration *on purpose* — "Was `denoteωF`", "`encPair`/`decPair` are gone with the traversal",
# "`record_e_keeps_duplicate_keys` became unstatable when `M`'s keys became a `Finset`" — is
# indistinguishable from one that names a renamed declaration by accident. Both are a backticked
# token absent from code; the difference is the tense of the sentence, and no parser reads tense.
# §9 tells a docstring to record what the forced choice cost, so those citations are the
# convention working, not drift: 49 of them, against 13 real stale pointers, when this was first
# measured. Marking them moves the judgement to where the judgement is — the person writing the
# sentence, who knows whether the thing is dead.
#
# The marker is held honest in the other direction too: `~~X~~` where `X` *does* occur in code is
# a failure (`false retirement`), so the marks cannot quietly rot into decoration as names come
# back or get reused.
RETIRED = re.compile(r"~~([^~\n]{1,80})~~")
# naming patterns and filenames, not citations
# `.match_1`, `.eq_def`, `.proof_3`: **auto-generated names, real constants, never in source.**
# `inL.match_1` is the matcher Lean derives for `inL`'s pattern match — §6 names it as the fan
# `fanOf` found — and no amount of grepping `Calculus/` will locate it, because nobody wrote it.
NOISE = re.compile(r"\.(md|py|ts|lean|json|toml|sh)$|(^|[._])X([._]|$)|^_|^f_sound$"
                   r"|\.(match|proof|eq)_\d+$|\.eq_def$")

# Cited on purpose, with the reason. Keyed by document, then name.
EXPECTED = {
    "README.md": {
        "List.Perm": "mathlib; named as the next probe, not as something proved here",
        "mono": "the ccpo/`partial_fixpoint` obligation's conventional name; `altCodec_not_monotone` is ours",
    },
    "ARCHITECTURE.md": {
        "orth_unreach_lines": "a `doc_counts.py` marker key, not a Lean name — §6 cites it to "
                              "name the count that moved in `7fff6e8`",
        "mono": "same as `README.md`'s — the ccpo obligation's conventional name, at §7's "
                "not-modelled row",
        "List.Perm": "mathlib; §9's commutativity row names it as the next probe, not as "
                     "something proved here — inherited from the deleted representation audit",
    },
    "../docs/codec-calculus.md": {
        "e_c": "the specification's own notation for a component codec, not a Lean name",
        "Encoded": "§1's own wire type, named by the specification; the model has no Lean type for it",
    },
}


# Two classes of name that are *live somewhere*, so `~~retired~~` would be a lie, and absent
# from `Calculus/` by design, so the code cannot clear them. Both are global rather than
# per-document because each recurs across many targets — `opaque` alone is cited in 17 places —
# and an `EXPECTED` entry repeated 17 times is a table nobody reads.

# The shipped TypeScript's names, at §8's boundary. The host has codecs and methods the model
# deliberately does not: §8 records what the host owes, and naming the thing that owes it is how.
HOST = {
    "opaque": "`src/`'s codec, analysed here as a well-behaved `custom` — same analysis, "
              "opposite warranty (§7). `opaqCodec` is the model's, and is not the same name",
    "admits": "`src/codec.ts`'s reader — **internal** as of the surface enumeration, with the "
              "other five definition readers. §10's question about wiring it into `union`'s "
              "resolver is closed (`ff75c6b`, write side). The model's predicate is `adm`, "
              "proved exact, which is what made that swap behaviour-preserving",
    "admitsAttribute": "`src/codec.ts`'s read-side predicate, internal, and deliberately not a "
                       "reader of the definition — it asks the codec, because the read side "
                       "validates already. §10 records why a row-by-row port was rejected",
    # The other four of the six definition readers. `writes` needs no entry: it occurs in
    # `Calculus/` on its own account. Cited together by §10's record of the surface enumeration,
    # which is the decision these four are the subject of.
    "carries": "`src/codec.ts`'s reader of which value kinds a term takes — the union's "
               "declaration filter. Internal since the surface enumeration (§10)",
    "decides": "`src/codec.ts`'s reader of whether a term pins one value; internal, and what "
               "`ident` is to the model",
    "setBase": "`src/codec.ts`'s reader of a set's element base; internal. The model indexes "
               "`set` by `SetBase` instead, which is §4a's premise-becomes-an-index",
    "deeper": "`src/codec.ts`'s one-segment path walk; internal, and the reason a path through "
              "a variant that disagrees has no single honest answer",
    "identifying": "`src/codec.ts`'s declaration-time guard: whether an option decides its own "
                   "membership. §5 cites it because `Orth` is its specification, and because "
                   "`admits` cannot replace it — a \u2200-value question is not a per-value one",
    "separatedByElements": "`src/codec.ts`'s companion to `identifying`, the exemption for a "
                           "container with no empty inhabitant. Cited by §5's bridge notes",
    "Separation": "`src/lean.ts`'s vector class carrying §5's bridge: one theorem per pair "
                  "`src/` refuses, asserting `Orth` does not certify it",
    "ReadVerdict": "`src/lean.ts`'s vector class carrying §10's read-side differential: "
                   "`AdmA t a` against whether the library's read accepted `a`. Cited because "
                   "§10 records the `AdmA` port as rejected and this as what landed instead",
    "discriminatedUnion": "`src/`'s combinator; the calculus has no such codec — it is the sum "
                          "over tag-admission, which is why `(dunion)` is a rule and not a row",
    "EveryOptionTagged": "`src/codec.ts`'s type-level check, cited by §8's arity-one row",
}

# The specification's own notation, from `docs/codec-calculus.md`. §1 names sets and §5 names
# policies in a vocabulary the model realises under other names, and a document quoting the
# specification is quoting it correctly.
SPEC = {
    "Numerals": "§1's numeral set; the model picks it out as `Numeral.WF`, so the specification's "
                "name for it is not a Lean name",
    "Numbers": "§5's policy name, realised as the `lossy`/`refuse` split — `onKind_number` is the "
               "theorem, `Numbers` is the row",
    "dom": "§2's notation for a partial function's domain, written `dom(e)`; `domE` is the Lean "
           "lemma about it",
    "p_c": "§2's notation for a component codec's read half, paired with `e_c`",
    "ground": "§9's table block, named by the convention rather than by the model — the codecs "
              "in it are `pointCodec`'s four",
    "Exact": "the `ExactV`/`ExactA` family under one name, as §5's table heads the two rows",
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
Multiset WellFounded Expr Environment NameSet ExprSet StateM Meta Core Elab IO
sizeOf casesOn recOn binductionOn brecOn noConfusion propext sorry rfl decide simp omega
deriving instance structure inductive theorem lemma abbrev mutual noncomputable partial unsafe
def example where match with fun let have show this at using
dite dif whnf native native_decide with_unfolding_all maxHeartbeats partial_function
choose iff head lookup zipWith flatMap not_forall filter_eq_nil_iff sorryAx unknown
docBlame unreachableTactic simpNF synTaut dupNamespace checkType
EXPECTED CURRENT PRELUDE LOG HEAD HOST SPEC MODULE_NAMES defaultTargets grep
""".split())
# The last four rows are the ones the stripped source set made necessary, and they are a
# different kind of entry from the first four. `Bool` was always unclearable; `dite`,
# `native_decide` and `Finset.image` used to be cleared by *a proof's own comment* mentioning
# them, which is exactly the circularity `occurring()` now refuses. A Lean tactic, a Batteries
# linter and a mathlib lemma cited in prose are citations of the language, and the language is
# not this development's to define.


def language(t):
    """Is this a citation of Lean, mathlib or Batteries rather than of `Calculus/`?

    A dotted name is judged by its root namespace: `Classical.choice`, `Finset.image` and
    `Quotient.out` are the language's whether or not any proof here appeals to them, and
    `Classical.choice` above all — the axiom base exists to keep it out, so the one thing
    certain about it is that it does *not* occur in the sources.
    """
    return t in PRELUDE or t.split(".")[0] in PRELUDE


def deliberately_absent(t):
    """Absent from `Calculus/` by design: the language, the host's names, the specification's."""
    return language(t) or t in HOST or t in SPEC


def single_word_checkable(t):
    """Is this single-word citation one the guard can hold `Calculus/` to?"""
    return not (len(t) <= 2 or HASH.match(t) or t in MODULE_NAMES or t in PRELUDE)


def strip_comments(s):
    """`s` with every Lean comment and docstring removed, string literals kept.

    Handles `--` to end of line and nested `/- … -/`, which covers `/-- … -/` docstrings and
    `/-! … -/` module docs as the block forms they are. String literals are copied through so
    that a `"--"` inside one does not open a comment, and newlines inside a stripped block are
    kept so that reported line numbers still mean something.
    """
    out, i, n, depth = [], 0, len(s), 0
    while i < n:
        if depth:
            if s.startswith("/-", i):
                depth += 1; i += 2
            elif s.startswith("-/", i):
                depth -= 1; i += 2
            else:
                if s[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        c = s[i]
        if c == '"':
            out.append(c); i += 1
            while i < n:
                if s[i] == "\\":
                    out.append(s[i:i + 2]); i += 2; continue
                out.append(s[i])
                if s[i] == '"':
                    i += 1; break
                i += 1
            continue
        if s.startswith("--", i):
            while i < n and s[i] != "\n":
                i += 1
            continue
        if s.startswith("/-", i):
            depth = 1; i += 2
            continue
        out.append(c); i += 1
    return "".join(out)


def occurring():
    """Every identifier, and every dotted sub-path of one, appearing in the sources.

    **Comments and docstrings are stripped first, and that is the whole of `6a90359`'s fix.**
    Before it the source set was raw file text, so a name appearing *only* in a docstring was
    present in its own evidence and cleared itself — `literalNRule_holds_what_it_cannot_write`
    was renamed, four citations kept the old name, and this guard passed clean until the
    archaeology sweep deleted the prose that was clearing them. Comments are 45.1% of
    `Calculus/` by character; a citation now has to be answered by code.
    """
    # `scripts/*.lean` as well as `Calculus/*.lean`: `blast_radius.lean` and `complexity.lean`
    # are Lean code in this development, and §6 cites the definitions inside them (`dagSize`,
    # `fanOf`). A citation of an instrument's own API is not drift, and leaving them out made
    # the guard fail on §6's description of the guard's siblings.
    src = "".join(strip_comments(open(f).read())
                  for f in sorted(glob.glob("Calculus/*.lean"))
                          + sorted(glob.glob("scripts/*.lean")))
    out = set()
    for tok in IDENT.findall(src):
        parts = tok.split(".")
        for i in range(len(parts)):
            for j in range(i + 1, len(parts) + 1):
                out.add(".".join(parts[i:j]))
    return out


def scan(path, present):
    expected = EXPECTED.get(path, {})
    hits, seen, stale, false_retirements = [], set(), [], []
    for lineno, line in enumerate(open(path).read().split("\n"), 1):
        # `~~X~~` claims `X` is retired. Not a citation — but the claim is checked.
        for tok in RETIRED.findall(line):
            if LEANISH.match(tok) and not NOISE.search(tok) and tok in present:
                false_retirements.append((lineno, tok))
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
            if deliberately_absent(t):
                continue
            if t in expected:
                continue
            hits.append((lineno, t))
    for name in expected:
        if name not in seen:
            stale.append(name)
    return hits, stale, false_retirements


def main():
    if not glob.glob("Calculus/*.lean"):
        sys.exit("run from formal/")
    present = occurring()
    targets = CURRENT + (LOG if "--all" in sys.argv else [])
    failed = False
    for path in targets:
        if not os.path.exists(path):
            continue
        hits, stale, false_retirements = scan(path, present)
        label = os.path.normpath(path)
        current = path in CURRENT
        if not hits and not stale and not false_retirements:
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
        if false_retirements:
            failed = True
            n = len(false_retirements)
            print(f"  {label:38s} {n} false retirement{'' if n == 1 else 's'}")
            for lineno, name in false_retirements:
                print(f"      {lineno:6d}  ~~{name}~~  (still in the sources — unmark it)")
    if LOG and "--all" not in sys.argv:
        print(f"\n  (--all also scans {', '.join(os.path.normpath(p) for p in LOG)})")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
