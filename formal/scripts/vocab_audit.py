#!/usr/bin/env python3
"""Audit the codec vocabulary in Calculus/.

Three measurements, all name- and pattern-based, all re-runnable:

  1. the completeness matrix  — which of the five slots each construction fills;
  2. unfolding sites by kind  — what the remaining hand-unfolding is actually about;
  3. unfolding density by block — sites per 100 lines, against inversion completeness.

An "unfolding site" is a `replace h : … := h`, a `show …`, or a `cases h… :` — the
three ways a proof takes a definition apart by hand instead of citing a lemma. It is a
proxy, not a verdict: some are irreducible. The count is useful as a *trend*.

Usage:  python3 scripts/vocab_audit.py            (run from formal/)
        python3 scripts/vocab_audit.py --sites    (also list the sites, for triage)
"""
import re, sys, glob, os, collections

SRC = sorted(glob.glob(os.path.join("Calculus", "*.lean")))
if not SRC:
    sys.exit("no Calculus/*.lean found — run from formal/")

DECL = re.compile(r'^(?:private )?(?:theorem|lemma|def|abbrev|instance)\s+([^\s({\[:]+)')
SITE = re.compile(r'\breplace \w+ :|^\s*(?:show|cases h\w* :)')

# ── every Codec-producing construction, and the stem its lemmas are named after ──
CONSTRUCTIONS = [
    ("pointCodec", "pointCodec"), ("stringCodec", "stringCodec"),
    ("numberCodec", "numberCodec"), ("decimalCodec", "decimalCodec"),
    ("booleanCodec", "booleanCodec"),
    ("binaryCodec", "binaryCodec"), ("nullCodec", "nullCodec"),
    # `literalSCodec`/`literalNCodec` stood here and neither exists: `GroundKind` replaced
    # both with one `literalCodec`. They scored as empty rows, so every denominator was 23
    # where it should be 22 and every ✓ count was measured against two constructions that
    # could not have lemmas. `literalNCodec` even scored a p-inversion, off
    # `literalNCodec_p_n` — a lemma about `literalCodec .number` still carrying the old
    # stem, which is a naming defect no guard can see and is logged in the handoff.
    ("literalCodec", "literalCodec"),
    ("through", "through"), ("restrict", "restrict"),
    ("extendRead", "extendRead"), ("orNull", "orNull"),
    ("carriedCodec", "carried"), ("entrywise", "entrywise"),
    ("setCodec", "setCodec"), ("arrayCodec", "arrayCodec"),
    ("recordCodec", "recordCodec"), ("tupleCodec", "tupleCodec"),
    ("objectCodecCore", "objWrite"), ("altCodec", "altCodec"),
    ("dunionCodec", "dunionCodec"), ("opaqCodec", "opaqCodec"),
]
# constructions whose slot is deliberately empty, with the reason
EXEMPT = {("extendRead", "lawful"): "(MP) is the sanctioned breach — §5's first residue"}

# ── how a site is classified: what is being taken apart ──
NAMED = [c for c, _ in CONSTRUCTIONS] + ["objectCodec", "encPair", "decPair",
                                         "encEntry", "decEntry"]
def kind_of(blob):
    if re.search(r'\b(Obligations|MPOk|UAtCan)\b', blob):            return "judgement premises (Obligations/MPOk)"
    if re.search(r'filter \(·\.admit|admitV|admitA|altCodec', blob): return "union resolution (altCodec's filter)"
    if re.search(r'some \[\] = some|traverse\b', blob):              return "traverse / list base cases"
    if re.search(r'\blookup\b', blob):                               return "association-list lookup"
    if any(re.search(r'\b' + re.escape(c) + r'\b', blob) for c in NAMED): return "a named codec's e/p"
    if re.search(r'\.bind|\.map|if .* then .* else none|match ', blob):   return "raw Option algebra"
    return "raw Option algebra"          # `some x = some y := h` lands here

# ── blocks, for the density table: patterns, and whether inversion is complete ──
BLOCKS = [
    ("array + record", ["arrayCodec", "recordCodec", "encPair", "decPair",
                        "entrywise", "carried"], "complete"),
    ("tuple",  ["tupleCodec", "align", "slots", "zip_", "tuple_"], "complete"),
    ("set",    ["setCodec", "asWireSet", "Payloads", "set_", "agree_of_member"], "complete"),
    ("object", ["objectCodec", "entryCodec", "encEntry", "decEntry", "objWrite",
                "objRead", "object_", "fbDefaults", "valPresent", "reqPresent",
                "keepB", "rcOf", "mem_decoded", "objEntryT", "objStep", "entry_"], "complete"),
    ("opaque", ["opaqCodec", "opaq_", "onKind", "opaqKinds"], "none"),
    ("union",  ["altCodec", "OptionSem", "uniqueAdmission", "unanimous",
                "optionSemOf", "dunion", "tag_filter"], "complete"),
    ("wrappers", ["through", "restrict", "extendRead", "orNull"], "complete"),
    ("ground", ["stringCodec", "numberCodec", "decimalCodec",
                "booleanCodec", "binaryCodec", "nullCodec", "literalS", "literalN",
                "pointCodec", "decimal_", "numeral"], "none"),
]

def load():
    files, names = {}, set()
    for f in SRC:
        L = open(f).read().split("\n")
        files[f] = L
        names |= {m.group(1) for m in (DECL.match(l) for l in L) if m}
    return files, names

def declarations(lines):
    """(name, start, end) for every top-level declaration."""
    starts = [i for i, l in enumerate(lines) if DECL.match(l)] + [len(lines)]
    for a, b in zip(starts, starts[1:]):
        yield DECL.match(lines[a]).group(1), a, b

def matrix(names):
    has = lambda *c: any(x in names for x in c)
    # some constructions carry inversion as a *family* of per-constructor unfoldings
    # rather than one iff; count the family
    fam = lambda s, side: any(n.startswith(f"{s}_{side}_") for n in names)
    print("── 1. completeness matrix ─────────────────────────────────────────────\n")
    print(f"{'construction':18s} {'e-inv':>6s}{'p-inv':>7s}{'_eq':>6s}{'core':>7s}{'lawful':>8s}{'carrier':>9s}")
    print("─" * 62)
    filled = collections.Counter(); total = collections.Counter()
    for d, s in CONSTRUCTIONS:
        slots = {
            "e-inv":   has(f"{s}_e", f"{s}_e_eq", f"{s}_e_inv", f"{s}_e_iff", f"{s}_eq") or fam(s, "e"),
            "p-inv":   (has(f"{s}_p", f"{s}_p_eq", f"{s}_p_inv", f"{s}_p_iff",
                             "objRead_eq" if s == "objWrite" else f"{s}_p") or fam(s, "p")),
            "_eq":     has(f"{s}_eq", f"{d}_eq"),
            "core":    has(f"lawfulCore_{d}", f"lawfulCore_{s}", f"LawfulCore.{s}"),
            "lawful":  has(f"lawful_{d}", f"lawful_{s}", f"Lawful.{s}"),
            "carrier": has(f"carrier_{d}", f"carrier_{s}"),
        }
        cells = ""
        for k, v in slots.items():
            total[k] += 1
            if v: filled[k] += 1
            mark = "✓" if v else ("–" if (d, k) in EXEMPT else "·")
            cells += f"{mark:>{7 if k != 'e-inv' else 6}s}"
        print(f"{d:18s} {cells}")
    print("─" * 62)
    print(f"{'filled':18s} " + "".join(
        f"{f'{filled[k]}/{total[k]}':>{7 if k != 'e-inv' else 6}s}" for k in total))
    for (d, k), why in EXEMPT.items():
        print(f"\n  – {d}/{k}: {why}")
    print("\n  Name-based: a lemma proved under a different name reads as missing —")
    print("  which is the point. The scheme of ARCHITECTURE.md §9 is what makes the")
    print("  matrix meaningful, so a violation must show as a gap, not be absorbed.")
    dot = sorted(n for n in names
                 if re.match(r'(Lawful|LawfulCore|Carrier)\.(through|restrict|extendRead|orNull)$', n))
    if dot:
        print(f"\n  in dot form ({len(dot)}) — sanctioned by §2 for the namespaced wrappers,")
        print("  listed so the split stays visible rather than absorbed:")
        print("      " + ", ".join(dot))

def sites(files, show=False):
    by_kind = collections.Counter(); by_file = collections.defaultdict(collections.Counter)
    listing = collections.defaultdict(list)
    for f, L in files.items():
        for i, l in enumerate(L):
            if SITE.search(l):
                blob = " ".join(x.strip() for x in L[i:i + 3])
                k = kind_of(blob)
                by_kind[k] += 1; by_file[k][os.path.basename(f)] += 1
                listing[k].append(f"{f}:{i+1}  {l.strip()[:96]}")
    print("\n\n── 2. unfolding sites, by what is being taken apart ───────────────────\n")
    for k, v in by_kind.most_common():
        top = ", ".join(f"{n.replace('.lean','')} {c}" for n, c in by_file[k].most_common(3))
        print(f"{v:5d}  {k:42s} [{top}]")
    print(f"\n{sum(by_kind.values()):5d}  total")
    if show:
        for k, _ in by_kind.most_common():
            print(f"\n── {k} ──")
            for s in listing[k]: print("  " + s)
    return sum(by_kind.values())

def density(files):
    def block_of(name):
        for b, pats, _ in BLOCKS:
            if any(p.lower() in name.lower() for p in pats): return b
        return None
    lines, hits = collections.Counter(), collections.Counter()
    for f, L in files.items():
        for name, a, b in declarations(L):
            blk = block_of(name)
            if not blk: continue
            lines[blk] += b - a
            hits[blk] += sum(1 for i in range(a, b) if SITE.search(L[i]))
    print("\n\n── 3. unfolding density, against inversion completeness ───────────────\n")
    print(f"{'block':16s}{'inversion':11s}{'lines':>7s}{'sites':>7s}{'per 100 lines':>15s}")
    print("─" * 58)
    for b, _, inv in BLOCKS:
        n, s = lines[b], hits[b]
        print(f"{b:16s}{inv:11s}{n:7d}{s:7d}{(100*s/n if n else 0):15.1f}")

if __name__ == "__main__":
    files, names = load()
    matrix(names)
    sites(files, show="--sites" in sys.argv)
    density(files)
    print()
