#!/usr/bin/env python3
"""Measure the *review surface* of the mechanization in Calculus/.

The vocabulary audit (`vocab_audit.py`) asks whether a proof reads in codec
vocabulary. This one asks a different question, and the one that matters for an
artifact meant to be checked rather than trusted:

    could a competent reviewer who knows the specification, but not this
    codebase, verify a single theorem in isolation?

Four measurements, all re-runnable:

  1. the guard's coverage  — theorem names the documents cite as results, against
     the names `Calculus/Axioms.lean` actually puts through `#assert_axioms`;
  2. §-tag coverage        — declarations whose own docstring names a spec section,
     per module: the only in-source link from a rule to its theorem;
  3. docstring coverage    — theorems and defs carrying any docstring at all;
  4. statement opacity     — theorem statements that mention a definition with no
     docstring anywhere, i.e. whose *statement* (not proof) needs a detour.

Usage:  python3 scripts/fidelity_audit.py           (run from formal/)
        python3 scripts/fidelity_audit.py --names   (list the offenders)
"""
import re, sys, os, glob, collections

SRC = sorted(glob.glob(os.path.join("Calculus", "*.lean")))
DOCS = ["README.md", "VOCABULARY.md", "FIDELITY.md",
        os.path.join("..", "docs", "codec-formalization.md")]
if not SRC:
    sys.exit("no Calculus/*.lean found — run from formal/")

DECL = re.compile(r'^(?:private )?(?:theorem|lemma|def|abbrev|structure|inductive)\s+([^\s({\[:]+)')
KIND = re.compile(r'^(?:private )?(theorem|lemma|def|abbrev|structure|inductive)\s')

def declarations():
    """(name, kind, file, line, docstring, statement) for every top-level declaration."""
    out = []
    for f in SRC:
        L = open(f).read().split("\n")
        starts = [i for i, l in enumerate(L) if DECL.match(l)] + [len(L)]
        for a, b in zip(starts, starts[1:]):
            name = DECL.match(L[a]).group(1)
            kind = KIND.match(L[a]).group(1)
            # the docstring immediately above, if any
            doc, j = [], a - 1
            if j >= 0 and L[j].rstrip().endswith('-/'):
                while j >= 0 and not L[j].lstrip().startswith('/--'):
                    j -= 1
                doc = L[j:a]
            # the statement: up to the first `:=` or `where` or `by`
            stmt = []
            for i in range(a, b):
                stmt.append(L[i])
                if re.search(r':=|\bwhere\b|\bby\b', L[i]): break
            out.append((name, kind, f, a + 1, "\n".join(doc), "\n".join(stmt)))
    return out

def cited_names(decls):
    """Theorem names the documents name as results (backticked, and a real theorem)."""
    known = {n for n, k, *_ in decls if k in ("theorem", "lemma")}
    cited = set()
    for d in DOCS:
        if not os.path.exists(d): continue
        for m in re.finditer(r'`([A-Za-zκμω_][A-Za-z0-9κμω_.\']*)`', open(d).read()):
            if m.group(1) in known: cited.add(m.group(1))
    return cited

def guarded():
    p = os.path.join("Calculus", "Axioms.lean")
    if not os.path.exists(p): return set()
    body = open(p).read()
    return set(re.findall(r'#assert_axioms\s+([^\s]+)', body))

def main(show=False):
    decls = declarations()
    thms = [d for d in decls if d[1] in ("theorem", "lemma")]
    defs = [d for d in decls if d[1] in ("def", "abbrev", "structure", "inductive")]
    undocumented_defs = {d[0] for d in defs if not d[4].strip()}

    print("── 1. the guard's coverage ────────────────────────────────────────────\n")
    cited, g = cited_names(decls), guarded()
    missing = sorted(cited - g)
    print(f"  cited as a result by the documents : {len(cited)}")
    print(f"  put through #assert_axioms         : {len(g)}")
    print(f"  cited but unguarded                : {len(missing)}")
    if show and missing:
        for n in missing: print(f"      {n}")
    print("\n  Unguarded is not unsound — it means the advertised axiom base is a")
    print("  claim for that theorem rather than a build error. Check with")
    print("  `#print axioms` before trusting one.")

    print("\n\n── 2. §-tag coverage, per module ──────────────────────────────────────\n")
    tag = collections.Counter(); tot = collections.Counter()
    for n, k, f, ln, doc, st in decls:
        b = os.path.basename(f); tot[b] += 1
        if '§' in doc: tag[b] += 1
    print(f"{'module':22s}{'tagged':>8s}{'decls':>8s}{'%':>7s}")
    print("─" * 45)
    for b in sorted(tot, key=lambda b: (tag[b] / tot[b] if tot[b] else 0)):
        print(f"{b:22s}{tag[b]:8d}{tot[b]:8d}{100*tag[b]/tot[b]:6.0f}%")
    print("─" * 45)
    print(f"{'TOTAL':22s}{sum(tag.values()):8d}{sum(tot.values()):8d}"
          f"{100*sum(tag.values())/sum(tot.values()):6.0f}%")

    print("\n\n── 3. docstring coverage ──────────────────────────────────────────────\n")
    for label, group in (("theorems", thms), ("definitions", defs)):
        have = sum(1 for d in group if d[4].strip())
        print(f"  {label:14s}{have:4d} / {len(group):4d}  ({100*have/len(group):.0f}%)")

    print("\n\n── 4. statement opacity ───────────────────────────────────────────────\n")
    opaque = []
    for n, k, f, ln, doc, st in thms:
        hit = sorted({d for d in undocumented_defs if re.search(r'\b'+re.escape(d)+r'\b', st)})
        if hit: opaque.append((n, f, ln, doc.strip() != "", hit))
    both = [o for o in opaque if not o[3]]
    print(f"  statements naming an undocumented definition : {len(opaque)} / {len(thms)}"
          f"  ({100*len(opaque)/len(thms):.0f}%)")
    print(f"  …and themselves undocumented                 : {len(both)}")
    print(f"  undocumented definitions in total            : {len(undocumented_defs)}")
    if show:
        print("\n  undocumented definitions named in a statement:")
        named = collections.Counter()
        for *_, hit in opaque:
            for h in hit: named[h] += 1
        for d, c in named.most_common(25): print(f"      {c:4d}  {d}")
    print("\n  A statement naming an undocumented definition cannot be read against")
    print("  the specification without a detour. This counts the *statement*, never")
    print("  the proof — a reviewer is entitled to skip the proof.")

if __name__ == "__main__":
    main(show="--names" in sys.argv)
    print()
