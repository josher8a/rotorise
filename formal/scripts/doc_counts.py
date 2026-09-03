#!/usr/bin/env python3
"""Compute the counts `ARCHITECTURE.md` rests on, and hold the document to them.

Every count that drifted this month was a number typed by hand: `term_depth_wf`'s "five"
declarations when there were three, `Orthogonality.lean`'s "sixteen … about thirteen" when
neither number matched anything, §5's 23 theorems against a table naming 21, and a twin pair
count that three passes put at 82, 69 and 72. `name_drift.py` cannot catch any of them —
**a count is not a name**, as §6 says and as `7a91de8` recorded — and §9 said so in as many
words: "A count in prose is not covered; verify counts by hand". Verifying by hand is what
produced the drift.

So the counts that matter are computed here and written into the document between markers:

    the reachable total is <!-- count:orth_reachable_lines -->140<!-- /count --> lines

`--check` recomputes and exits 1 if any marked block disagrees, which is the guard. With no
argument it rewrites the blocks, which is how you fix a disagreement.

**What this cannot do**, and the reason it is a small script rather than a large one:

* It measures the *tree*, not the argument. It can say six theorems sit in the `slot` row; it
  cannot say `slot` is the right phase for them. A row moved to the wrong phase keeps the
  totals honest and the classification wrong.
* Its line counts use one convention — a declaration runs from its `theorem`/`lemma` line to
  the last non-blank line before the next declaration, docstring or section — and a number is
  only as meaningful as its convention. The convention is here rather than in prose so that
  the next person can disagree with it in one place.
* Two of the section's twenty-five discharges are named in the prose *beneath* the by-phase
  table rather than in a row (`PROSE_LIMITS`). No parser can find them, so they are listed
  here by hand, which means this script has a hand-maintained list of exactly two names in it.
  If a third limit joins them and nobody adds it, the total goes quietly wrong — that is this
  instrument's own blind spot and it is the same shape as the one it exists to close.

Deliberately not computed: the value/attribute twin pair count. §10 now records that the pair
count is an artifact of its transform and is not the dimension that decides the merge, so
generating one would re-establish exactly the false precision that section removed.

Usage:  python3 scripts/doc_counts.py            (run from formal/; rewrites the blocks)
        python3 scripts/doc_counts.py --check     (exit 1 on any disagreement)
"""
import re, sys, os, glob

DOC = "ARCHITECTURE.md"
ORTH = "Calculus/Orthogonality.lean"
FAMILY_FILES = ["Calculus/Discharge.lean", "Calculus/Exactness.lean",
                "Calculus/Refutations.lean"]

MARKER = re.compile(r"(<!-- count:(\w+) -->)(.*?)(<!-- /count -->)")

# Named in the prose under the by-phase table, not in a row — see the docstring's third caveat.
PROSE_LIMITS = ["sepJA_legacy_decimal", "sepJA_needs_member"]

WORDS = {0: "no", 1: "One", 2: "Two", 3: "Three", 4: "Four", 5: "Five", 6: "Six",
         7: "Seven", 8: "Eight", 9: "Nine", 10: "Ten", 11: "Eleven", 12: "Twelve"}

DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)?"
                  r"(?:theorem|lemma)\s+([^\W\d][\w'!?⁺₀-₉]*)")
BOUND = re.compile(r"^\s*(/--|/-!|end\b|namespace\b|section\b|mutual\b|@\[|theorem|lemma|def|"
                   r"abbrev|instance|structure|inductive|class|private|protected|noncomputable)")


def span_lines(name):
    """Lines of proof for one theorem, by the convention in the docstring. 0 if absent."""
    pat = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)?"
                     r"(?:theorem|lemma)\s+" + re.escape(name) + r"(?![\w.'])")
    for path in FAMILY_FILES + [ORTH]:
        if not os.path.exists(path):
            continue
        lines = open(path).read().split("\n")
        marks = [i for i, l in enumerate(lines) if BOUND.match(l)]
        for i, l in enumerate(lines):
            if pat.match(l):
                nxt = next((s for s in marks if s > i), len(lines))
                j = nxt - 1
                while j > i and lines[j].strip() == "":
                    j -= 1
                return j - i + 1
    return 0


def orth_table():
    """The by-phase table, as {phase: [theorem names]}. Rows are `| names | phase | reached |`."""
    rows, inside = {}, False
    for line in open(ORTH).read().split("\n"):
        if line.startswith("| theorem | phase | reached |"):
            inside = True
            continue
        if inside:
            if not line.startswith("|"):
                break
            cells = [c.strip() for c in line.strip().strip("|").split("|")]
            if len(cells) != 3 or set(cells[0]) <= set("- "):
                continue
            names = re.findall(r"`([^`]+)`", cells[0])
            phase = cells[1].split(":")[0].strip().strip("*_`")
            rows.setdefault(phase, []).extend(names)
    return rows


def counts():
    t = orth_table()
    slot = t.get("slot", [])
    alt = t.get("alternatives", [])
    unreach = [n for p, ns in t.items() if p not in ("slot", "alternatives")
               for n in ns] + PROSE_LIMITS
    fam = 0
    for path in FAMILY_FILES:
        for line in open(path).read().split("\n"):
            m = DECL.match(line)
            if m and re.match(r"^(sep|uAtCan_|uAtAct_)", m.group(1)):
                fam += 1
    slot_l = sum(span_lines(n) for n in slot)
    alt_l = sum(span_lines(n) for n in alt)
    un_l = sum(span_lines(n) for n in unreach)
    return {
        "modules": (len(glob.glob("Calculus/*.lean")), "digits"),
        "term_depth_wf_users": (sum(
            1 for f in glob.glob("Calculus/*.lean")
            for l in open(f).read().split("\n")
            if l.strip().startswith("decreasing_by term_depth_wf")), "words"),
        "sep_family": (fam, "digits"),
        "orth_file_lines": (len(open(ORTH).read().split("\n")) - 1, "digits"),
        # §4c cites `Combinators.lean`'s size against the tree's. Both drift on every commit
        # that touches either, and both were stale (3988 of a tree the sentence did not name).
        "combinators_lines": (len(open("Calculus/Combinators.lean").read().split("\n")) - 1,
                              "digits"),
        "tree_lines": (sum(len(open(f).read().split("\n")) - 1
                           for f in sorted(glob.glob("Calculus/*.lean"))), "digits"),
        "orth_slot_theorems": (len(slot), "digits"),
        "orth_slot_lines": (slot_l, "digits"),
        "orth_alt_theorems": (len(alt), "digits"),
        "orth_alt_lines": (alt_l, "digits"),
        "orth_unreach_theorems": (len(unreach), "digits"),
        "orth_unreach_lines": (un_l, "digits"),
        "orth_total_theorems": (len(slot) + len(alt) + len(unreach), "digits"),
        "orth_reachable_lines": (slot_l + alt_l, "digits"),
    }


def render(value, how):
    return WORDS.get(value, str(value)) if how == "words" else str(value)


def main():
    if not glob.glob("Calculus/*.lean"):
        sys.exit("run from formal/")
    check = "--check" in sys.argv
    c = counts()
    text = open(DOC).read()
    seen, bad = set(), []

    def repl(m):
        open_t, name, body, close_t = m.groups()
        if name not in c:
            bad.append((name, body, "no such count"))
            return m.group(0)
        seen.add(name)
        want = render(*c[name])
        if body != want:
            bad.append((name, body, want))
        return open_t + want + close_t

    out = MARKER.sub(repl, text)
    unmarked = sorted(set(c) - seen)

    for name in sorted(c):
        print(f"  {name:24s} {render(*c[name]):>6s}"
              + ("" if name in seen else "   (computed, not marked in the document)"))
    if unmarked:
        print(f"\n  {len(unmarked)} computed but unmarked: {', '.join(unmarked)}")

    if not bad:
        print(f"\n  {DOC}: every marked count agrees.")
        return 0
    print(f"\n  {DOC}: {len(bad)} disagree" + (" — rewritten." if not check else ":"))
    for name, was, want in bad:
        print(f"      {name:24s} document says {was!r}, computed {want!r}")
    if check:
        print("\n  run without --check to rewrite them.")
        return 1
    open(DOC, "w").write(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
