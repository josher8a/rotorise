#!/usr/bin/env python3
"""Hold three counts to the state they were in, per file, and fail when one rises.

`name_drift.py` asks whether a cited name exists and `doc_counts.py` asks whether a number
in prose matches the tree. Neither can ask the question §10's two guards are about:

    is this getting worse?

Three counts, none of which can be *fixed* in one arc and all of which can quietly rot:

  unfolding_sites               a `replace h : … := h`, a `show …` or a `cases h… :` — the
                                three ways a proof takes a definition apart by hand instead
                                of citing a lemma. §9's rule is that a proof reads in codec
                                vocabulary; this is the count that makes it enforceable
                                rather than aspirational. 332 today.
  retirement_marks              `~~oldName~~` citations (§9). Not a defect — the convention
                                working — but the mark is the one thing `name_drift.py`
                                takes on trust, so a session that deletes a declaration and
                                marks its citations in the same commit gets no check at all.
                                A rise in the count is where that shows. 72 today, 57 of them
                                in docstrings and 15 in the three documents.
  undocumented_public_theorems  public `theorem`/`lemma` with no docstring. §10's bar is that
                                a reader who knows the specification can tell what a theorem
                                says from its name and one line. 269 of 896 today, 30%.
  branches                      decision points — pattern rows, `if`, `cases`, `<;>` and the
                                rest of `POINTS` below. The case-analysis measure that
                                `unfolding_sites` is blind to, and the two do not track each
                                other per file, so this is a second number and not a
                                restatement.

**The branch count and not the branch *density*.** Density is the sharper reading —
`occV_sound` at 1.48 a line against `soundness_both`'s 0.36 over 122 — but its denominator
moves when a signature is re-wrapped, and this repo has paid for a formatting-sensitive metric
once already: `7fff6e8` moved `orth_unreach_lines` 168 → 169 by splitting one signature onto
two lines. A count of `|` and `cases` does not move for that. Nothing prints the density now,
and nothing ratchets it.

**A bar and a ratchet fail differently, and only one of them was available.** A coverage bar
at 269 undocumented theorems would be decoration: nobody can satisfy it, so it would be
switched off or exempted into meaninglessness. A ratchet asks nothing on the day it lands —
its bar *is* today's number — and from then on the next docstring is cheaper than the
argument for skipping it. That is why all three are ratchets and none is a bar.

WHY THE BASELINE IS A JSON FILE AND NOT A DICT IN THIS SCRIPT

Both were probed. These numbers move on nearly every commit that touches `Calculus/`, so a
baseline living here would mean the *guard's own source* is edited by every such commit — and
"did someone weaken the guard?" becomes invisible in a diff that is mostly guard edits. With
the baseline in `scripts/ratchets.json` this file stays still, which is what makes a change to
it worth reading. It is also the pattern `doc_counts.py` already established: a computed number
belongs somewhere a reviewer expects to find a number.

The cost of a separate file is the rot `EXPECTED` demonstrated — entries keyed to something
that no longer exists, unreachable and unreported. It gets the same treatment: **a baseline key
naming a file that is gone is a failure**, not a shrug.

  --accept          rewrite the baselines, printing every delta first. A *fall* is the normal
                    case and needs no ceremony.
  --accept --allow-rise
                    also write rises. Separate because accepting a rise is the one action that
                    makes this guard weaker, and it should read as a deliberate sentence in a
                    commit message rather than as a tool invocation that happened to work.

A file absent from the baseline is **new**, not a regression: it is reported and admitted at
its current count on the next `--accept`. A new module has no prior state to have got worse
than. The exposure is a module arriving with a large count already in it, which is a code
review's job and not a ratchet's.

Blind spot, and it is the same shape for all three: **a ratchet accepts the state it was born
in, so it cannot see a defect older than itself.** 269 undocumented theorems and 332 hand
unfoldings are invisible to it by construction — it guards the derivative, not the value, and
`--accept` with a *lowered* number is the only way a baseline should ever move. §6 records this
beside the other instruments.

Usage:  python3 scripts/ratchet.py                      (run from formal/; exit 1 on a rise)
        python3 scripts/ratchet.py --accept              (write falls)
        python3 scripts/ratchet.py --accept --allow-rise (write rises too)
        python3 scripts/ratchet.py --names               (list the undocumented theorems)
"""
import json, os, re, sys, glob

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# `strip_comments` is `name_drift.py`'s, deliberately shared rather than copied: two comment
# strippers that disagree would put two different numbers in front of a reader and neither
# would be wrong. Importing it also means this script inherits the string-literal and nesting
# handling that file's docstring argues for. `name_drift.py` globs `Calculus/` at import, so
# both scripts have the same "run from formal/" requirement.
from name_drift import strip_comments, LEANISH, NOISE, RETIRED, CURRENT

# ── the branch metric ────────────────────────────────────────────────────────────────────────
# The definition of a ratcheted count belongs with the guard that ratchets it. These three
# patterns and the counter are the part a guard needs; the audit instrument that used to print
# the wider reading is gone, and the commit that removed it says why.

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
    by one even when it strictly reduces the work. That is backwards for this repo, whose proof
    convention wants a proof to cite a lemma rather than inline it: the first real use of this
    metric was `AdmA_exact`'s fan, where pulling two cases into named lemmas cut the proof term
    by an order of magnitude and the ratchet called it a rise. A guard that fires on the
    refactor it exists to encourage is a guard nobody keeps.
    """
    n = 0
    for line in lines:
        if ROW.match(line):
            n += 1
        for rx in POINTS:
            n += len(rx.findall(line))
    return n

# This file owns the branch definition above and holds the number to its baseline. It did not
# own the definition until the audit instruments were deleted, and owning it is the point: a
# ratcheted count whose definition lives in a file nobody runs is a count nobody can read.

BASELINE = os.path.join("scripts", "ratchets.json")

# the hand-unfolding count, and this file is the only thing that reports it now. **Applied to
# stripped source**, so a commented-out `show` is not a site — which is why this number and the
# one the deleted vocabulary audit printed were never quite equal.
SITE = re.compile(r'\breplace \w+ :|^\s*(?:show|cases h\w* :)')

# A public theorem: `theorem` or `lemma`, attributes and the other modifiers allowed, `private`
# excluded. `example` has no name and is not a declaration anyone can cite, so it is not here.
THEOREM = re.compile(
    r'^(?P<mods>(?:@\[[^\]]*\]\s*)*'
    r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*)'
    r'(?P<kw>theorem|lemma)\s+(?P<name>[^\s({\[:]+)')


def docstring_ends(lines):
    """Line indices where a `/-- … -/` docstring closes.

    `/-! … -/` is module documentation and deliberately does not count: it explains a section,
    not a declaration, and §10's bar is about what a reader can tell from *this theorem*.
    Nesting is tracked because a docstring may contain `/- … -/`.
    """
    out, depth, is_doc = set(), 0, False
    for i, line in enumerate(lines):
        j = 0
        while j < len(line):
            if line.startswith("/--", j) and depth == 0:
                depth, is_doc = 1, True; j += 3; continue
            if line.startswith("/-", j):
                depth += 1; j += 2; continue
            if line.startswith("-/", j):
                depth -= 1
                if depth == 0 and is_doc:
                    out.add(i); is_doc = False
                j += 2; continue
            j += 1
    return out


def undocumented(path):
    """Public theorems in `path` with no docstring, as (line, name) pairs."""
    lines = open(path).read().split("\n")
    ends, out = docstring_ends(lines), []
    for i, line in enumerate(lines):
        m = THEOREM.match(line)
        if not m or "private" in m.group("mods"):
            continue
        # walk up over the declaration's own attribute lines; a blank line means no docstring
        k = i - 1
        while k >= 0 and lines[k].strip().startswith("@["):
            k -= 1
        if k not in ends:
            out.append((i + 1, m.group("name")))
    return out


def measure():
    """{metric: {path: count}} over the current tree.

    The two proof measures range over `Calculus/*.lean`. The mark count ranges over
    **`name_drift.py`'s whole `CURRENT` list**, documents included, because the hole it closes
    is not specific to docstrings: a session that deletes a declaration and marks its citations
    in a document in the same commit gets exactly as little checking as one that does it
    in a docstring.
    """
    out = {m: {} for m in ("unfolding_sites", "retirement_marks",
                           "undocumented_public_theorems", "branches")}
    for path in sorted(glob.glob("Calculus/*.lean")):
        code = strip_comments(open(path).read())
        lines = code.split("\n")
        out["unfolding_sites"][path] = sum(1 for l in lines if SITE.search(l))
        out["undocumented_public_theorems"][path] = len(undocumented(path))
        heads = [i for i, l in enumerate(lines) if DECL.match(l)]
        # decision points, not per-declaration cyclomatic numbers: summing `1 + decisions`
        # would make extracting a lemma a rise. `decision_points` above says why.
        out["branches"][path] = sum(
            decision_points(lines[i:(heads[k + 1] if k + 1 < len(heads) else len(lines))])
            for k, i in enumerate(heads))
    for path in CURRENT:
        if not os.path.exists(path):
            continue
        text = open(path).read()
        out["retirement_marks"][os.path.normpath(path)] = sum(
            1 for t in RETIRED.findall(text) if LEANISH.match(t) and not NOISE.search(t))
    return out


def load_baseline():
    if not os.path.exists(BASELINE):
        return None
    with open(BASELINE) as f:
        return json.load(f)


def write_baseline(data):
    payload = {"_comment": "Per-file ratchet baselines. See scripts/ratchet.py — a rise fails "
                           "the build; move a number only with --accept.",
               **{m: dict(sorted(counts.items())) for m, counts in sorted(data.items())}}
    with open(BASELINE, "w") as f:
        json.dump(payload, f, indent=2, sort_keys=False)
        f.write("\n")


def main():
    if not glob.glob("Calculus/*.lean"):
        sys.exit("run from formal/")
    current = measure()
    baseline = load_baseline()
    accept = "--accept" in sys.argv
    allow_rise = "--allow-rise" in sys.argv

    if baseline is None:
        print(f"  no baseline at {BASELINE}")
        for m, counts in current.items():
            print(f"  {m:30s} {sum(counts.values()):5d}")
        if accept:
            write_baseline(current); print(f"\n  written to {BASELINE}")
            return 0
        print("\n  run with --accept to create it.")
        return 1

    rises, falls, new_files, stale, new_metrics = [], [], [], [], []
    for metric, counts in current.items():
        base = baseline.get(metric, {})
        # A metric with no baseline at all is not twenty new files, it is an unaccepted
        # instrument — and "no prior" must not let a whole metric pass unmeasured.
        if not base:
            new_metrics.append((metric, sum(counts.values())))
            continue
        for path, n in counts.items():
            if path not in base:
                new_files.append((metric, path, n)); continue
            if n > base[path]:
                rises.append((metric, path, base[path], n))
            elif n < base[path]:
                falls.append((metric, path, base[path], n))
        for path in base:
            if path not in counts:
                stale.append((metric, path))

    for metric, counts in sorted(current.items()):
        base = baseline.get(metric, {})
        total = sum(counts.values())
        if not base:
            print(f"  {metric:30s} {total:5d}  (no baseline)")
            continue
        btotal = sum(base.values())
        arrow = "=" if total == btotal else ("UP" if total > btotal else "down")
        print(f"  {metric:30s} {total:5d}  (baseline {btotal}, {arrow})")

    for metric, path, was, now in falls:
        print(f"  down  {metric:30s} {os.path.basename(path):24s} {was} -> {now}")
    for metric, path, n in new_files:
        print(f"  new   {metric:30s} {os.path.basename(path):24s} {n} "
              f"(no prior — admitted on --accept)")
    for metric, path, was, now in rises:
        print(f"  RISE  {metric:30s} {os.path.basename(path):24s} {was} -> {now}")
    for metric, path in stale:
        print(f"  STALE {metric:30s} {path}  (file is gone — drop it with --accept)")
    for metric, total in new_metrics:
        print(f"  NEW   {metric:30s} {'':24s} {total} across the tree, no baseline "
              f"— --accept to adopt it")

    if "--names" in sys.argv:
        print()
        for path in sorted(glob.glob("Calculus/*.lean")):
            hits = undocumented(path)
            if hits:
                print(f"  {os.path.normpath(path)}  {len(hits)} undocumented")
                for line, name in hits:
                    print(f"      {line:6d}  {name}")

    if accept:
        if rises and not allow_rise:
            print("\n  refusing to write a rise. Fix the tree, or say --allow-rise and say why "
                  "in the commit message.")
            return 1
        write_baseline(current)
        print(f"\n  {BASELINE} rewritten.")
        return 0

    if rises or stale or new_metrics:
        print("\n  a ratcheted count rose, a baseline names a file that is gone, or a metric "
              "has no baseline.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
