#!/usr/bin/env python3
"""Check that the axiom guard can *see* every module in `Calculus/`.

`Calculus/Axioms.lean` runs `#assert_axioms_all`, which walks the environment and
fails the build if any declaration in the `Calculus` namespace depends on an axiom
outside the sanctioned base. Its docstring argues, at length and correctly, that a
guard must not be opt-in: the enumerated form it replaced named 125 theorems out of
1199, and one of the 1074 it did not name had already acquired `Classical.choice`.

But `#assert_axioms_all` walks *the environment*, and the environment is what
`Axioms.lean` imports — a hand-maintained list of nine lines. So the guard is
universal over the modules someone remembered to import and silent about the rest.
The opt-in list did not go away; it moved from theorem names to module names, where
it is shorter and therefore easier to believe is complete.

That gap has been real twice:

  * `Calculus/Dynamo/Witness/Nesting.lean` used `omega`, a known `Classical.choice` route, and sat
    outside the guard until the import was added by hand.
  * `Calculus/Bridge/Vectors.lean` pulled `Classical.choice` through mathlib's
    `DecidableEq (Finset α)` — and it entered through a `def`, so no amount of proof
    review would have found it. `Axioms.lean`'s own last section says so: "This
    import is the reason the guard saw it."

Both were caught by someone adding an import. This script is the check that makes
the next one fail the build instead.

    every `.lean` file under `Calculus/` on disk is transitively imported by `Calculus/Axioms.lean`

The method is textual: read `import Calculus.X` out of every module, take the
transitive closure from `Axioms.lean`'s own imports, diff against the files on disk.
Non-`Calculus.*` imports (mathlib, `Lean`) are ignored — they are not what the guard
walks. `Axioms.lean` is trivially reachable from itself.

**What this does not prove.** Reachability is a necessary condition, not a sufficient
one. It says the declarations exist in the environment `#assert_axioms_all` walks; it
says nothing about whether that elaborator is correct, whether `sanctionedAxioms` is
the base the documentation claims, or whether the walk's own filters
(`ci.isTheorem`, `!n.isInternal`) let something through — a `def` that acquires an
axiom is *not* checked by `#assert_axioms_all` at all, which is exactly how the
`Vectors.lean` defect entered. Only the Lean build proves anything about axioms. This
proves that the build is looking.

It also runs on source text, not on Lean's module resolution: a module Lake excludes,
or an import inside a comment or a conditional, is read the same as any other.

Usage:  python3 scripts/guard_reach.py          (run from formal/)
        python3 scripts/guard_reach.py --graph  (also print the import graph)
Exit code 1 if any module is unreachable from the guard.
"""
import os, re, sys, glob, collections

GUARD = os.path.join("Calculus", "Axioms.lean")
# Lean puts one import per line, at the top, unindented.
IMPORT = re.compile(r"^import\s+(Calculus(?:\.[^\s]+)?)\s*$")


def module_of(path):
    """`Calculus/Dynamo/Lang/HeldSet.lean` -> `Calculus.Dynamo.Lang.HeldSet`; `Calculus.lean` -> `Calculus`."""
    return os.path.splitext(path)[0].replace(os.sep, ".")


def imports(path):
    """The `Calculus.*` modules this file imports, in source order."""
    out = []
    for line in open(path).read().split("\n"):
        m = IMPORT.match(line)
        if m and m.group(1) not in out:
            out.append(m.group(1))
    return out


def reachable(graph, roots):
    """Transitive closure of `roots` under `graph`, roots included."""
    seen, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(graph.get(m, []))
    return seen


def main():
    src = sorted(glob.glob(os.path.join("Calculus", "**", "*.lean"), recursive=True))
    if not src or not os.path.exists(GUARD):
        sys.exit("no Calculus/Axioms.lean found — run from formal/")

    graph = {module_of(f): imports(f) for f in src}
    if os.path.exists("Calculus.lean"):
        graph["Calculus"] = imports("Calculus.lean")
    modules = set(graph) - {"Calculus"}

    guard = module_of(GUARD)
    seen = reachable(graph, [guard]) & modules
    missing = sorted(modules - seen)

    print(f"  guard        {guard}")
    print(f"  modules      {len(modules)} under Calculus/")
    print(f"  reachable    {len(seen)} transitively from the guard's imports")

    # A module nothing imports is a different defect — not what this check fails on,
    # but worth seeing while the graph is in hand. The guard itself is expected here:
    # only the `Calculus` aggregator imports it.
    imported = {m for deps in graph.values() for m in deps}
    orphans = sorted(m for m in modules - imported if m != guard)
    if orphans:
        print(f"  imported by nothing: {len(orphans)}  (not a failure — see the docstring)")
        for m in orphans:
            print(f"      {m}")

    if "--graph" in sys.argv:
        print()
        for m in sorted(graph):
            mark = " " if m in seen or m == "Calculus" else "!"
            print(f"  {mark} {m:28s} -> {', '.join(graph[m]) or '(no Calculus imports)'}")

    print()
    if missing:
        print(f"  UNREACHABLE: {len(missing)} module(s) the axiom guard never loads,")
        print("  so #assert_axioms_all does not walk their declarations:")
        for m in missing:
            print(f"      {m}")
        print(f"\n  Fix: add `import {missing[0]}` (and the rest) to {GUARD},")
        print("  or import them from a module that is already reachable.")
        return 1

    print("  every module is in the environment the guard walks.")
    print("  (reachability only — it does not prove the guard is configured correctly)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
