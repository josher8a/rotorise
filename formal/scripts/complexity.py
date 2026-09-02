#!/usr/bin/env python3
"""Branch count per declaration, and per file — the metric `unfolding_sites` is blind to.

`vocab_audit.py` counts hand-unfolding sites: a `replace`, a `show`, a `cases h :` — the ways a
proof takes a definition apart instead of citing a lemma. That is a **vocabulary** measure, and
`ratchet.py` holds it. It says nothing about a proof that does its work by wide case analysis,
because `cases`, `rcases` and `<;>` are not unfolding anything.

Measured per file, the two rank differently: **Spearman 0.56.** `Discharge.lean` is 8.9 branches
per unfolding site and `Orthogonality.lean` is 31.1 — the first is hand-unfolding heavy, the
second is case-analysis heavy and the older guard cannot see it. So this is a second metric and
not a restatement of the first.

WHAT IS COUNTED, AND WHY EACH ONE

Lean has no loops, so the decision points are pattern rows and case tactics:

    ^\\s*\\|                  a match/pattern row, one per alternative
    if … then                a term- or tactic-level branch
    dite / ite               the same, applied rather than written
    match … with             the head of an inline analysis
    cases / rcases / obtain / induction    a case split in tactic form
    by_cases                 a *classical* split, and §1 wants those visible anyway
    <;>                      a fan: one script, every goal
    all_goals / any_goals    the same, named
    .elim                    a disjunction consumed as a branch

Comments and docstrings are stripped first (`name_drift.py`'s stripper), so a commented-out
`cases` is not a branch. One site in `Orthogonality.lean` was a commented-out `show`, which is
the whole of `vocab_audit.py`'s 333 against this file's 332.

**`theorem` and `def` are reported apart, and that is not cosmetic.** A `def`'s branch count is
usually the *specification's* row count: `HObject` is 47 because §3's object rule has that many
cases, and `aeq` is 23 because `Attr` has ten constructors and the wire sets are three of them.
There is nothing to simplify there and a guard that says otherwise is wrong. A theorem's branch
count is the prover's choice, which is the number worth watching.

WHAT THIS IS NOT

**Not complexity per line.** The ratio is the sharper *reading* — `occV_sound` at 1.48 branches
a line is the densest proof in the tree, where `soundness_both` at 0.36 over 122 lines is a
table, one line per typing rule, exactly as §6 claims. But the ratio is **formatting-sensitive**
in the denominator: re-wrapping a signature onto two lines moves it, and this repo has already
paid for a formatting-sensitive metric once — `7fff6e8` moved `orth_unreach_lines` 168 → 169 by
splitting one signature. So the ratio is printed and never ratcheted. The *count* is
formatting-stable — rewrapping adds no `|` and no `cases` — and that is the number `ratchet.py`
holds.

**Not a measure of what the kernel checks.** A `<;>` chain is one character and can elaborate to
a large proof term, or to almost nothing: `Adm_kind` has 55 branch points in 39 lines and its
proof term is 103 nodes, while `encSet_isSome_of` looks calm at 0.38 branches a line and is
4845. That question needs the kernel, and `scripts/complexity.lean` is where it is asked.

Usage:  python3 scripts/complexity.py            (run from formal/; per file, then the leaders)
        python3 scripts/complexity.py --names    (every declaration, ranked)
Exit code is always 0 — this reports, `ratchet.py` is what fails.
"""
import re, sys, os, glob

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from name_drift import strip_comments

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*'
                  r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*'
                  r'(theorem|lemma|def|abbrev|instance)\s+([^\s({\[:]+)')

# one match per row, counted by line
ROW = re.compile(r'^\s*\|')
# these may occur more than once on a line, so they are counted by occurrence
POINTS = [re.compile(p) for p in (
    r'\bif\b.*?\bthen\b', r'\bdite\b', r'\bite\b', r'\bmatch\b.*?\bwith\b',
    r'\bcases\b', r'\brcases\b', r'\bobtain\b', r'\binduction\b',
    r'\bby_cases\b', r'<;>', r'\ball_goals\b', r'\bany_goals\b', r'\.elim\b')]


def decision_points(lines):
    """The decision points alone, with no +1 for the declaration itself.

    **The +1 is deliberately not here, and its absence is the whole of what makes the per-file
    total usable as a ratchet.** The textbook cyclomatic number is `1 + decisions` per unit, and
    summing that over a file adds one per declaration — so extracting a lemma raises the total
    by one even when it strictly reduces the work. That is backwards for this repo, where §9
    wants a proof to cite a lemma rather than inline it: the first real use of this metric was
    `AdmA_exact`'s fan, where pulling two cases into named lemmas cut the proof term from
    2754337 tree nodes to 59397 and the ratchet called it a rise. A guard that fires on the
    refactor it exists to encourage is a guard nobody keeps.

    `branches()` below adds the 1 back for a single declaration, which is the right convention
    for *ranking* one proof against another.
    """
    n = 0
    for line in lines:
        if ROW.match(line):
            n += 1
        for rx in POINTS:
            n += len(rx.findall(line))
    return n


def branches(lines):
    """`1 + decision_points`, the textbook number, for ranking one declaration."""
    return 1 + decision_points(lines)


def declarations():
    """(branches, lines, kind, name, file, line) for every declaration, comments stripped."""
    out = []
    for path in sorted(glob.glob("Calculus/*.lean")):
        code = strip_comments(open(path).read()).split("\n")
        heads = [i for i, l in enumerate(code) if DECL.match(l)]
        for idx, i in enumerate(heads):
            end = heads[idx + 1] if idx + 1 < len(heads) else len(code)
            body = code[i:end]
            while len(body) > 1 and body[-1].strip() == "":
                body.pop()
            m = DECL.match(code[i])
            out.append((branches(body), len(body), m.group(1), m.group(2),
                        os.path.basename(path), i + 1))
    return out


def main():
    if not glob.glob("Calculus/*.lean"):
        sys.exit("run from formal/")
    decls = declarations()
    per_file = {}
    for b, _, _, _, f, _ in decls:
        per_file[f] = per_file.get(f, 0) + b

    print("── branches per file ──────────────────────────────────────────")
    print(f"  {'branches':>9}  module")
    for f, b in sorted(per_file.items(), key=lambda kv: -kv[1]):
        print(f"  {b:9d}  {f}")
    print(f"  {sum(per_file.values()):9d}  TOTAL")

    thms = [d for d in decls if d[2] in ("theorem", "lemma")]
    defs = [d for d in decls if d[2] not in ("theorem", "lemma")]
    for label, grp, note in (
            ("theorems — the prover's choice", thms, ""),
            ("defs — usually the specification's row count, not a design choice", defs, "")):
        grp = sorted(grp, key=lambda d: -d[0])
        total = sum(d[0] for d in grp)
        print(f"\n── {label} ──")
        print(f"  {len(grp)} declarations, {total} branches, mean {total / len(grp):.1f}")
        print(f"  {'br':>4} {'lines':>5} {'br/ln':>6}  name")
        for b, ln, _, n, f, line in grp[:10]:
            print(f"  {b:4d} {ln:5d} {b / ln:6.2f}  {n:28s} {f}:{line}")

    if "--names" in sys.argv:
        print("\n── every declaration, by branch count ──")
        for b, ln, kind, n, f, line in sorted(decls, key=lambda d: -d[0]):
            print(f"  {b:4d} {ln:5d} {b / ln:6.2f}  {kind:8s} {n:34s} {f}:{line}")
    else:
        print("\n  (--names lists every declaration)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
