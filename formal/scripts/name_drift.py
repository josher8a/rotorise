#!/usr/bin/env python3
"""Find names the documents cite that `Calculus/` no longer defines.

`ratchet.py` holds four counts to the state they were in and fails when one rises.
Neither it nor any other guard here asks the question that a refactoring arc actually
breaks:

    does every Lean name a document names still exist?

Prose does not typecheck. Deleting a declaration leaves the build green and every
citation of it dangling, and the two drift findings before the residue sweep were
both caught by luck rather than by a check.

A hit is a backticked token that *looks* like a Lean name — no spaces, and either a `_`
or a `.` in it or else a single word that is not one of four categories that cannot be
`Calculus/` names (see `single_word_checkable`) — and matches no identifier occurring in
**the code** of every `.lean` file under `Calculus/`, comments and docstrings stripped (`occurring()`).
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
to a document `b163c17` deleted became unreachable the moment that file left the list, and
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

    ~~marked~~   retired: the declaration is gone and the prose says so (`RETIRED`)
    PRELUDE      the language: Lean, mathlib, Batteries — judged by root namespace
    HOST         `src/`'s names, at the host boundary — live, just not here
    SPEC         the specification's own notation, from the blueprint's `content.tex`
    EXPECTED     a genuine one-off, keyed to the document that makes it

When this split was first measured the four absorbed 99 of 169 hits between them, the marks
took 60, and 18 stale pointers were left — which is the number the guard exists to report.

Hits in the current-state documents — `formal/README.md`, `docs/architecture.md`,
`docs/roadmap.md`, `docs/defects.md`, the blueprint's `content.tex` —
are broken pointers and should be fixed or explicitly marked superseded.

**A third pass checks a backticked file path, because `NOISE` drops the whole class from the name
pass.** A path is not a Lean name, so the name pass is right to drop it, and nothing else was
reading it: `ratchet.py`'s own docstring named a deleted instrument in the present tense until
`8cc01e1` repaired it, and a docstring in `src/` named a deleted document as the record of a fact
until this pass read it. Each citation is resolved against the files the tree holds, by full path
and by basename. What the tree *produces* rather than holds is a short list of prefixes with a
producer named beside each, because a citation of `dist/Rotorise.d.ts` is honest on a machine
that has run the build and would otherwise depend on whether anyone had. The read set is wider
than the name pass's: `src/**/*.ts` is in it, because the only live defect the pass found on the
day it landed was there.

**A second pass checks `§N`, because a section number is a citation too.** The specification is
section-numbered on purpose and its `## §N` headings are the authority, so a `§N` naming a number
it does not have points at nothing. That is not hypothetical: the architecture document and the
representation audit were section-numbered as well, and `a3c1006` and `2f567c0` deleted them, so
their citations outlived the documents. The major number is what is checked, because `§5.6` is a
citation of `§5`.
The Python guards are in this pass's read set as well as the documents and the modules: a guard's
own prose is prose.

Usage:  python3 scripts/name_drift.py            (run from formal/)
        python3 scripts/name_drift.py --all      (include the change log)
Exit code 1 if any current-state document has a hit, a stale `EXPECTED` entry, a `~~name~~` whose
name is still in the sources, a `§N` the specification does not have, or a file path nothing
holds.
"""
import re, sys, os, glob, fnmatch

CURRENT = ["README.md", "docs/blueprint/src/content.tex", "docs/blueprint/src/abstract.tex",
           "docs/blueprint/src/introduction.tex",
           "../docs/architecture.md", "../docs/roadmap.md", "../docs/defects.md"]
# **The docstrings, which this guard never read.** Every module here is dense with backticked
# names and none of them was checked — 763 distinct citations, invisible. Demonstrated rather
# than assumed: writing `nullHonest_of_ownsNull_false` for `nullHonest_of_not_ownsNull` in a
# `Soundness.lean` docstring passed this guard clean. They are `CURRENT`, not a reported-only
# list, because at the time of adding them none dangled — so the bar is "keep it at zero",
# which is only meaningful if breaking it fails the build.
CURRENT += sorted(glob.glob("Calculus/**/*.lean", recursive=True))
# `LOG` held two change logs — scanned under `--all`, reported, never failing, because a name
# missing from a change log may be a deliberate record of a deletion rather than drift and no
# check can tell those apart. `b163c17` deleted both; `git log` is the change log now, and a
# commit message is not a document to scan. The list stays as the hook for any future
# reported-only target.
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
# existed (`depthP`, a companion `Value.depth`'s map row has no list to need). That convention is `docs/architecture.md`'s, and it exists because the check
# below cannot work without it: once the source set is code, a docstring that names a deleted
# declaration *on purpose* — "Was `denoteωF`", "`encPair`/`decPair` are gone with the traversal",
# "`record_e_keeps_duplicate_keys` became unstatable when `M`'s keys became a `Finset`" — is
# indistinguishable from one that names a renamed declaration by accident. Both are a backticked
# token absent from code; the difference is the tense of the sentence, and no parser reads tense.
# The docstring convention tells a docstring to record what the forced choice cost, so those
# citations are the convention working, not drift: 49 of them, against 13 real stale pointers, when this was first
# measured. Marking them moves the judgement to where the judgement is — the person writing the
# sentence, who knows whether the thing is dead.
#
# The marker is held honest in the other direction too: `~~X~~` where `X` *does* occur in code is
# a failure (`false retirement`), so the marks cannot quietly rot into decoration as names come
# back or get reused.
RETIRED = re.compile(r"~~([^~\n]{1,80})~~")
# A LaTeX document cites in `\texttt{}` and carries no backticks, so the specification
# would read as clean because nothing matched rather than because nothing was wrong.
TEXTTT = re.compile(r"\\texttt\{([^}]{1,80})\}")


def cited(line, path):
    """The citations on one line: backticks everywhere, `\\texttt{}` in a `.tex`."""
    out = BACKTICKED.findall(line)
    if path.endswith(".tex"):
        out += [t.replace("\\_", "_").replace("\\ ", " ").replace("\\%", "%")
               for t in TEXTTT.findall(line)]
    return out
# A section citation. The major number only: `§5.6` cites `§5`, and the specification numbers
# sections and not items.
SECTION = re.compile(r"§(\d+)")
# A backticked token naming a file rather than a declaration. `NOISE` keeps these out of the name
# pass, where they would be nonsense; `dangling_paths` is what checks them.
PATHISH = re.compile(r"\.(md|py|ts|lean|json|toml|sh|yml|yaml|tex)$")
# A Lean path with a line suffix. A line is what an edit moves and a declaration name is not,
# and `Calculus/` is what these guards already hold to their names, so a citation names the
# declaration. Refused as a class rather than resolved.
LINE_ANCHOR = re.compile(r"^[A-Za-z0-9_./-]+\.lean:[0-9]+$")
# What the tree produces rather than holds. One entry per producer, and no more: a prefix here
# exempts every path under it, so a fourth entry would need a fourth producer.
GENERATED = ("dist/",      # npm run build
             ".attest/")   # the attest snapshot run
# and the five vector artifacts, cited by path or by their leading-dot basename (the vector emit)
SPEC_DOC = "docs/blueprint/src/content.tex"
SECTION_HEADING = re.compile(r"^\\section\{§(\d+)", re.M)
# naming patterns and filenames, not citations
# `.match_1`, `.eq_def`, `.proof_3`: **auto-generated names, real constants, never in source.**
# `inL.match_1` is the matcher Lean derives for `inL`'s pattern match — §6 names it as the fan
# `fanOf` found — and no amount of grepping `Calculus/` will locate it, because nobody wrote it.
NOISE = re.compile(r"\.(md|py|ts|lean|json|toml|sh|tex)$|(^|[._])X([._]|$)|^_|^f_sound$"
                   r"|\.(match|proof|eq)_\d+$|\.eq_def$")

# Cited on purpose, with the reason. Keyed by document, then name.
EXPECTED = {
    "README.md": {
        "List.Perm": "mathlib; named as the next probe, not as something proved here",
        "mono": "the ccpo/`partial_fixpoint` obligation's conventional name; `altCodec_not_monotone` is ours",
    },
    "docs/blueprint/src/content.tex": {
        "e_c": "the specification's own notation for a component codec, not a Lean name",
    },
}


# Two classes of name that are *live somewhere*, so `~~retired~~` would be a lie, and absent
# from `Calculus/` by design, so the code cannot clear them. Both are global rather than
# per-document because each recurs across many targets — `opaque` alone is cited in 17 places —
# and an `EXPECTED` entry repeated 17 times is a table nobody reads.

# The shipped TypeScript's names, at the host boundary. The host has codecs and methods the
# model deliberately does not, and naming the thing that owes them is how that is recorded.
#
# AN ENTRY LEAVES WHEN ITS DECLARATION DOES. This table exempts a name from the drift check, so
# an entry outliving its declaration is an exemption for a name nothing declares: the document
# may then cite it forever and every guard stays green. That is not hypothetical — seven of the
# thirteen entries here had no declaration in `src/` when this was written, and two of them,
# `identifying` and `separatedByElements`, are exactly what the architecture was still
# naming. `separatedByElements` never had a declaration at all.
#
# The check below is an *anchored* one, and it has to be: a name can be live in `src/` as a
# local variable while the declaration it was whitelisted for is gone. `deeper` was, in
# `testing.ts`'s `firstDifference`. Asking "does this name appear in `src/`" passes it and
# reproduces the hole; asking for a declaration at the start of a line does not.
HOST = {
    "leanValueOf": "`src/codec/lean.ts`'s value emitter, which writes a `Value` for a host value. "
                   "The model has no emitter, so the name is the host's alone",
    "DynamoNumber": "`src/`'s carrier for `N`, which is what the model calls `WFNumeral`. Two "
                    "names for one carrier, on the two sides of the bridge",
    "dynamoNumber": "`src/`'s codec at the native numeric base, whose term is `Term.number`. The "
                    "codec and the term are named on their own sides",
    "sampleVectors": "`src/codec/lean/lean.spec.ts`'s differential corpus. The vectors it "
                     "generates are elaborated here; the list itself is the host's",
    "literalsOf": "`src/codec/term.ts`'s reader for the literals an object pins, at the caller's "
                  "level. The model reads `altsOfField`, which is not the same question",
    "opaque": "`src/`'s codec, analysed here as the language's one escape hatch, and warranted "
              "by the calculus rather than by its user (§7). `opaqCodec` is the model's, and is "
              "not the same name",
    "separable": "`src/codec/term.ts`'s certificate: whether two options share no value and no "
                 "attribute. The model's certificate is `certPair`; `.separations.lean` pins the "
                 "law in both directions",
    "valueKinds": "`src/codec/denote.ts`'s coarsening of `occV` to the alphabet a *value* can be "
                  "classified into — the reader `carries` became. §5 cites the value-kind filter "
                  "because a union's write side reads it; the model's `κ` is over `Kind`, which "
                  "is the same coarsening one level up",
    "Separation": "`src/codec/lean.ts`'s vector class carrying §5's bridge: one theorem per corpus "
                  "pair, `PairwiseCompat` where `src/` accepts, `certPair` false where it refuses",
    "ReadVerdict": "`src/codec/lean.ts`'s vector class carrying the read-side differential: "
                   "`AdmA t a` against whether the library's read accepted `a`. Cited because "
                   "the `AdmA` port was rejected and this is what landed instead",
    "discriminatedUnion": "`src/`'s combinator; the calculus has no such codec — it is the sum "
                          "over tag-admission, which is why `(dunion)` is a rule and not a row",
    "nullable": "`src/codec/codec.ts`'s builder, and the model has no such term. It reads whether "
                "its subterm already holds the null point and joins the null term with a union, "
                "which is what §3's sugar paragraph says it always was",
    "EveryOptionTagged": "`src/codec/codec.ts`'s type-level check, cited by the arity-one row",
    "decimal": "`src/codec/codec.ts`'s adapter: `number` under the text adapter, which the model "
               "states as `held` over `Term.number`. The model has no decimal base, so the name "
               "is the host's alone. `decimalCodec` is the model's codec for the stored numerals",
}

# The specification's own notation, from the blueprint's `content.tex`. §1 names sets and §5 names
# policies in a vocabulary the model realises under other names, and a document quoting the
# specification is quoting it correctly.
SPEC = {
    "Numerals": "§1's numeral set; the model picks it out as `Numeral.WF`, so the specification's "
                "name for it is not a Lean name",
    "Numbers": "§5's policy name. The model has no policy: `opaque` holds a number exactly, and "
               "the host states each policy as `held` over its canonical `opaque`",
    "dom": "§2's notation for a partial function's domain, written `dom(e)`; `domE` is the Lean "
           "lemma about it",
    "p_c": "§2's notation for a component codec's read half, paired with `e_c`",
    "ground": "a table block, named by the convention rather than by the model — the codecs "
              "in it are `pointCodec`'s four",
    "Exact": "the `ExactV`/`ExactA` family under one name, as §5's table heads the two rows",
}


# A single-word citation is checked against the same source set as a dotted one — any
# identifier occurring anywhere in a `.lean` file under `Calculus/`. Four categories can never occur there
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
# A module under a layer folder is named by its file and by its folder.
MODULE_NAMES = {part for f in glob.glob("Calculus/**/*.lean", recursive=True)
                for part in os.path.splitext(os.path.relpath(f, "Calculus"))[0].split(os.sep)} | {"Calculus"}
HASH = re.compile(r"^[0-9a-f]{7,}$")
PRELUDE = set("""
Bool Prop Type Sort Nat Int String Char Unit True False And Or Not Iff Eq Option Some None
List Array Finset Set Subtype Quot Quotient Decidable DecidableEq Repr BEq Inhabited Nonempty
Function Equivalence Forall₂ Perm Prod Sum Classical Exists Std Batteries Lean Mathlib
Multiset WellFounded Expr Environment NameSet ExprSet StateM Meta Core Elab IO
sizeOf casesOn recOn binductionOn brecOn noConfusion propext sorry rfl decide simp omega by_contra
deriving instance structure inductive theorem lemma abbrev mutual noncomputable partial unsafe
def example where match with fun let have show this at using
dite dif whnf native native_decide with_unfolding_all maxHeartbeats partial_function
choose iff head lookup zipWith flatMap not_forall filter_eq_nil_iff sorryAx unknown
docBlame unreachableTactic simpNF synTaut dupNamespace checkType unusedArguments
EXPECTED CURRENT PRELUDE LOG HEAD HOST SPEC MODULE_NAMES single_word_checkable defaultTargets grep
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
    # `scripts/*.lean` as well as every `.lean` file under `Calculus/`: a script written in Lean is Lean code in
    # this development, and a document citing the definitions inside one is citing real names.
    # No such script exists today — the audit instruments that were written in Lean are deleted
    # — and the glob stays so that the next one is covered without anyone remembering to add it.
    src = "".join(strip_comments(open(f).read())
                  for f in sorted(glob.glob("Calculus/**/*.lean", recursive=True))
                          + sorted(glob.glob("scripts/*.lean")))
    out = set()
    for tok in IDENT.findall(src):
        parts = tok.split(".")
        for i in range(len(parts)):
            for j in range(i + 1, len(parts) + 1):
                out.add(".".join(parts[i:j]))
    return out


def tree_files():
    """Every path the tree holds, by full path and by basename, from the repository root.

    The generated directories are skipped rather than walked, so a citation of a build output
    resolves through `GENERATED` and not through whether this machine has built.
    """
    skip = {".git", "node_modules", ".lake", "dist", ".attest", "__pycache__", ".venv"}
    full, base = set(), set()
    for root, dirs, files in os.walk("..", followlinks=True):
        dirs[:] = [d for d in dirs if d not in skip]
        for f in files:
            full.add(os.path.relpath(os.path.join(root, f), "..").replace(os.sep, "/"))
            base.add(f)
    return full, base


def path_resolves(tok, full, base):
    """Whether a cited path names a file the tree holds, or one a producer writes."""
    if any(tok.startswith(pre) for pre in GENERATED) or os.path.basename(tok).startswith("."):
        return True
    if "*" in tok:
        return any(fnmatch.fnmatch(p, tok) or fnmatch.fnmatch(p, "formal/" + tok) for p in full)
    return os.path.basename(tok) in base or any(p.endswith(tok) for p in full)


def line_anchored(paths):
    """Every backticked `<lean file>:<line>` citation, by path and line."""
    out = {}
    for path in paths:
        if not os.path.exists(path):
            continue
        for lineno, line in enumerate(open(path).read().split("\n"), 1):
            for tok in BACKTICKED.findall(line):
                if LINE_ANCHOR.match(tok.strip()):
                    out.setdefault(path, []).append((lineno, tok.strip()))
    return out


def dangling_paths(paths, full, base):
    """Every backticked file path citing a file nothing holds and no producer writes."""
    out = {}
    for path in paths:
        if not os.path.exists(path):
            continue
        for lineno, line in enumerate(open(path).read().split("\n"), 1):
            for tok in BACKTICKED.findall(line):
                tok = tok.strip()
                if " " in tok or not PATHISH.search(tok):
                    continue
                if not path_resolves(tok, full, base):
                    out.setdefault(path, []).append((lineno, tok))
    return out


def spec_sections():
    """The section numbers the specification declares, read from its own headings."""
    return {int(n) for n in SECTION_HEADING.findall(open(SPEC_DOC).read())}


def dangling_sections(paths, known):
    """Every `§N` citing a section the specification does not have, by path and line."""
    out = {}
    for path in paths:
        if not os.path.exists(path):
            continue
        for lineno, line in enumerate(open(path).read().split("\n"), 1):
            for n in sorted({int(n) for n in SECTION.findall(line)} - known):
                out.setdefault(path, []).append((lineno, n))
    return out


def scan(path, present):
    expected = EXPECTED.get(path, {})
    hits, seen, stale, false_retirements = [], set(), [], []
    for lineno, line in enumerate(open(path).read().split("\n"), 1):
        # `~~X~~` claims `X` is retired. Not a citation — but the claim is checked.
        for tok in RETIRED.findall(line):
            if LEANISH.match(tok) and not NOISE.search(tok) and tok in present:
                false_retirements.append((lineno, tok))
        for tok in cited(line, path):
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


def host_without_declarations():
    """`HOST` entries that no longer name a declaration in `src/`.

    Anchored to the start of a line, because a name can be live as a local variable while the
    declaration it was whitelisted for is gone — `deeper` was, in `testing.ts`. A `grep` for the
    bare name passes such an entry and leaves the exemption standing.
    """
    src = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "src")
    if not os.path.isdir(src):
        return []
    text = ""
    # recursive: `src/` nests its directories, and a flat listing passes over a nested file in silence
    for root, _, names in os.walk(src):
        for name in names:
            if name.endswith(".ts"):
                with open(os.path.join(root, name), encoding="utf-8") as handle:
                    text += handle.read() + "\n"
    declared = set(
        re.findall(
            r"^(?:export )?(?:declare )?(?:const|function|type|class|interface) "
            r"([A-Za-z_][A-Za-z0-9_]*)",
            text,
            re.M,
        )
    )
    return sorted(n for n in HOST if n not in declared)


def main():
    if not glob.glob("Calculus/**/*.lean", recursive=True):
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
    full, base = tree_files()
    path_targets = (CURRENT + sorted(glob.glob("scripts/*.py")) + ["scripts/gate.sh",
                    "scripts/classical.lean", "../CLAUDE.md"]
                    + sorted(glob.glob("../src/**/*.ts", recursive=True))
                    + sorted(glob.glob("../.github/workflows/*.yml")))
    broken_paths = dangling_paths(path_targets, full, base)
    if broken_paths:
        failed = True
        total = sum(len(v) for v in broken_paths.values())
        print(f"\n  {total} file citation{'' if total == 1 else 's'} naming a path the tree "
              f"does not hold and no producer writes")
        for path in sorted(broken_paths):
            for lineno, tok in broken_paths[path]:
                print(f"      {os.path.normpath(path)}:{lineno}  {tok}")
    anchored = line_anchored(path_targets)
    if anchored:
        failed = True
        total = sum(len(v) for v in anchored.values())
        print(f"\n  {total} citation{'' if total == 1 else 's'} anchored to a Lean line rather "
              f"than to a declaration name")
        for path in sorted(anchored):
            for lineno, tok in anchored[path]:
                print(f"      {os.path.normpath(path)}:{lineno}  {tok}")
    known = spec_sections()
    dangling = dangling_sections(CURRENT + sorted(glob.glob("scripts/*.py")), known)
    if dangling:
        failed = True
        total = sum(len(v) for v in dangling.values())
        print(f"\n  {total} section citation{'' if total == 1 else 's'} naming a § the "
              f"specification does not have (it has {min(known)}-{max(known)})")
        for path in sorted(dangling):
            for lineno, n in dangling[path]:
                print(f"      {os.path.normpath(path)}:{lineno}  §{n}")
    orphaned = host_without_declarations()
    if orphaned:
        failed = True
        n = len(orphaned)
        print(f"\n  {n} HOST entr{'y' if n == 1 else 'ies'} naming no declaration in src/")
        for name in orphaned:
            print(f"              {name}  (exempts a name nothing declares — drop the entry)")
    if LOG and "--all" not in sys.argv:
        print(f"\n  (--all also scans {', '.join(os.path.normpath(p) for p in LOG)})")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
