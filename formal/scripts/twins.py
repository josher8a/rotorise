#!/usr/bin/env python3
"""One-sided inversions: an `X_e…` with no `X_p…`, or the reverse.

§4c's rule is that a codec is stated once for both sides of the pair. That had been applied to
*constructions* and not to *inversions*, and the cost was a 683x proof-term fan across four
literal lemmas — `restrict_e_isSome` was `@[simp]` and `restrict_p_isSome` did not exist, so
every literal row on the read side unfolded `Codec.restrict` by hand and dragged `inL`'s
ten-row matcher in with it (§4c, §6, `423c276`).

**`vocab_audit.py`'s completeness matrix cannot see that, and the reason is worth stating.**
Its `p-inv` column asks whether *any* lemma named `restrict_p`-ish exists. One did:
`restrict_p`, an iff about `= some v`. So the matrix scored `restrict` complete on the day the
missing twin was costing 683x. Presence is the wrong question; **shape** is the question, and
the shape is the suffix. This file pairs on `(stem, suffix)` so that `_isSome` is only ever
compared with `_isSome`.

WHAT IS AND IS NOT A GAP

Three quarters of what this reports is one-sided *by construction*, and no guard should say
otherwise:

* a suffix naming a `Value` constructor — `_num`, `_str` — can only exist on the write side,
  and one naming an `Attr` constructor — `_n` — only on the read side. `numberCodec_e_num` has
  no twin because `numberCodec.p` does not take a `Value`.
* a genuinely one-sided *property*. `legacy` is a read-side hatch, so `legacy_p_outside_admA`
  has nothing to mirror; `record_p_order_irrelevant` is about reading a `Finset`'s entries in
  any order, which is not a statement about writing.

What is left is the class worth acting on: a side-agnostic suffix — `_isSome`, `_eq`, `_inv`,
`_restrict` — present on one side only. Those are ranked, and **`@[simp]` on the surviving side
is the aggravating factor**, because it means one side rewrites where the other unfolds.

MEASURED: TWO CANDIDATES, AND NEITHER IS ACTIONABLE TODAY

At `db3eb6d` the census over six files is 67 twin-shaped names, 30 paired and 37 one-sided; 22
of the 37 are side-specific suffixes, leaving 15 candidates. **Only two carry the aggravating
factor** — `numberCodec_p_isSome` and `decimalCodec_p_isSome`, whose write-side twins are both
`@[simp]`, which is exactly the `restrict` shape. Their consumer is
`admA_refine_ground_eq_admALit`, and `fanOf` says it has **no fan**: 2838 nodes at 10x, inside
the 2-19x band. So the actionable list is empty and `restrict_p_isSome` remains the only
instance of its kind that cost anything.

**Read the un-aggravated thirteen before believing them.** Suffix matching is literal, so it
reports pairs that are not pairs: the `opaq_p_*_agree` family's write-side counterpart is
`opaq_e_agree`, one lemma covering every constructor rather than one per constructor, and no
amount of string comparison sees that. `@[simp]` on the surviving side is the filter that
earned its keep; the rest of the list is a reading list, not a defect list.

This file's value is prospective: it is the guard that would have named the `restrict` gap
before a proof-term measurement found it.

Usage:  python3 scripts/twins.py            (run from formal/)
        python3 scripts/twins.py --all      (include the by-construction one-sided names)
Exit code is always 0 — this reports; nothing here is a defect on its own.
"""
import re, sys, os, glob, collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from name_drift import strip_comments

FILES = ["Calculus/Combinators.lean", "Calculus/Discharge.lean", "Calculus/Exactness.lean",
         "Calculus/LiteralArity1.lean", "Calculus/Opaque.lean", "Calculus/Equations.lean"]
DECL = re.compile(r'^(?:(?P<attr>@\[[^\]]*\])\s*)?(?:private\s+|noncomputable\s+)*'
                  r'(?:theorem|lemma)\s+(?P<name>[^\s({\[:]+)')
SIDE = re.compile(r'^(?P<stem>.+?)_(?P<side>[ep])(?P<suffix>(_.*)?)$')

# a suffix naming a constructor of `Value` (write) or `Attr` (read) cannot have a twin
VALUE_ONLY = {"_num", "_str", "_bool", "_bin", "_null", "_arr", "_map",
              "_strSet", "_numSet", "_binSet"}
ATTR_ONLY = {"_n", "_s", "_b", "_l", "_m", "_ss", "_ns", "_bs"}


def declarations():
    out = {}
    for f in FILES:
        if not os.path.exists(f):
            continue
        for i, line in enumerate(strip_comments(open(f).read()).split("\n"), 1):
            m = DECL.match(line)
            if m:
                out[m.group("name")] = (os.path.basename(f), i,
                                        "simp" in (m.group("attr") or ""))
    return out


def main():
    if not glob.glob("Calculus/*.lean"):
        sys.exit("run from formal/")
    decls = declarations()
    pairs = collections.defaultdict(dict)
    for n in decls:
        m = SIDE.match(n)
        if m:
            pairs[(m.group("stem"), m.group("suffix"))][m.group("side")] = n

    one = {k: v for k, v in pairs.items() if len(v) == 1}
    print(f"  {len(pairs)} twin-shaped names, {len(pairs) - len(one)} paired, {len(one)} one-sided\n")

    ranked, by_shape = [], []
    for (stem, suffix), v in one.items():
        side, name = next(iter(v.items()))
        want = f"{stem}_{'p' if side == 'e' else 'e'}{suffix}"
        f, i, is_simp = decls[name]
        row = (is_simp, stem, suffix, name, want, f, i)
        if (suffix in VALUE_ONLY and side == "e") or (suffix in ATTR_ONLY and side == "p"):
            by_shape.append(row)
        else:
            ranked.append(row)

    print("  CANDIDATES — a side-agnostic suffix present on one side only")
    print("  (`@[simp]` on the side that exists is the aggravating factor)\n")
    for is_simp, _, _, name, want, f, i in sorted(ranked, key=lambda r: (not r[0], r[3])):
        print(f"    {'@[simp]' if is_simp else '       '}  have {name:36s} {f}:{i}")
        print(f"             want {want}")
    if not ranked:
        print("    none\n")

    print(f"\n  ONE-SIDED BY CONSTRUCTION — {len(by_shape)}, the suffix names a constructor "
          f"of the other side's type")
    if "--all" in sys.argv:
        for _, _, suffix, name, _, f, i in sorted(by_shape, key=lambda r: r[3]):
            print(f"    {name:36s} {f}:{i}   ({suffix} is not a twin-able shape)")
    else:
        print("    (--all lists them)")
    print("\n  Rank a candidate by running `fanOf` on its consumers (scripts/complexity.lean).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
