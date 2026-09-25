#!/usr/bin/env python3
"""Check that each import under `Calculus/` follows the order of the layers.

THE RULE

Each folder under `Calculus/` is a layer. An import against the order of the layers is a
coupling: the lower layer then depends on a fact of the higher layer. The build does not
see a coupling, because the build only needs a graph without a cycle. This check refuses
the import that goes against the order:

  * `Alg/` and `Lang/` are generic. A generic module imports no module of `Dynamo/`,
    `JSON/` or `Bridge/`.
  * `Alg/` is below `Lang/`. A module of `Alg/` imports no module of `Lang/`.
  * `JSON/` and `Dynamo/` are two universes. A universe imports no module of the other.
  * Inside `Dynamo/`, the order is the root, then `Alg/`, then `Lang/`, then `Analysis/`,
    then `Witness/`. A module imports no module of a higher folder.
  * `Bridge/` is the host bridge. Only `Bridge/` and `Axioms.lean` import a module of
    `Bridge/`.

A module in a folder that this check does not know fails. Give a new folder its place in
the order here before the folder holds a module.

WHAT THIS CHECKS, AND WHAT IT CANNOT

The check reads the import header of each `.lean` file under `Calculus/`. The root
`Calculus.lean` imports every module and is no layer, so the check does not read it. An
import of a module outside `Calculus` (Mathlib, Batteries) is not a layer, and passes.

The check sees the direct import only. A declaration that a module cites through a
transitive import is invisible here. Remove the direct import and build to find that
citation.

USAGE

    layer_order.py [FORMAL_DIR]

`FORMAL_DIR` holds the folder `Calculus/`. The default is the parent of this script's folder.
The exit code is 1 when an import goes against the order, and 0 otherwise.
"""

import os
import re
import sys

DYNAMO_ORDER = ["", "Alg", "Lang", "Analysis", "Witness"]


def layer(rel):
    """The layer of a module path relative to `Calculus/`, or None for an unknown folder."""
    parts = rel.split("/")
    if len(parts) == 1:
        return ("axioms",) if parts[0] == "Axioms" else None
    top = parts[0]
    if top in ("Alg", "Lang", "JSON", "Bridge"):
        return (top,)
    if top == "Dynamo":
        sub = parts[1] if len(parts) > 2 else ""
        return ("Dynamo", DYNAMO_ORDER.index(sub)) if sub in DYNAMO_ORDER else None
    return None


def violation(src, dst):
    """The rule that the import of the layer `dst` by the layer `src` breaks, or None."""
    if dst == ("Bridge",) and src not in (("Bridge",), ("axioms",)):
        return "only Bridge/ and Axioms.lean import Bridge/"
    if src in (("Alg",), ("Lang",)) and dst[0] in ("Dynamo", "JSON", "Bridge"):
        return "a generic module imports no universe and no bridge"
    if src == ("Alg",) and dst == ("Lang",):
        return "Alg/ is below Lang/"
    if {src[0], dst[0]} == {"JSON", "Dynamo"}:
        return "JSON/ and Dynamo/ are two universes"
    if src[0] == "Dynamo" and dst[0] == "Dynamo" and dst[1] > src[1]:
        return "inside Dynamo/, the order is root < Alg < Lang < Analysis < Witness"
    return None


def imports(path):
    """The modules that the header of a Lean file imports."""
    found = []
    in_comment = False
    with open(path, encoding="utf-8") as f:
        for line in f:
            text = line.strip()
            if in_comment:
                in_comment = "-/" not in text
                continue
            if not text or text.startswith("--") or text in ("prelude", "module"):
                continue
            if text.startswith("/-"):
                in_comment = "-/" not in text[2:]
                continue
            m = re.match(r"(?:public\s+)?import\s+(.*)", text)
            if not m:
                break
            found.extend(m.group(1).split("--")[0].split())
    return found


def main(argv):
    formal = argv[1] if len(argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
    root = os.path.join(formal, "Calculus")
    if not os.path.isdir(root):
        print(f"layer_order.py: no folder {root}", file=sys.stderr)
        return 2
    failures = []
    for dirpath, _, files in os.walk(root):
        for name in sorted(files):
            if not name.endswith(".lean"):
                continue
            path = os.path.join(dirpath, name)
            rel = os.path.relpath(path, root)[: -len(".lean")].replace(os.sep, "/")
            src = layer(rel)
            if src is None:
                failures.append(f"Calculus/{rel}.lean: the folder has no place in the order")
                continue
            for mod in imports(path):
                if not mod.startswith("Calculus."):
                    continue
                dst = layer(mod[len("Calculus.") :].replace(".", "/"))
                if dst is None:
                    failures.append(f"Calculus/{rel}.lean: imports {mod}, whose folder has no place in the order")
                    continue
                rule = violation(src, dst)
                if rule:
                    failures.append(f"Calculus/{rel}.lean: imports {mod}: {rule}")
    for line in sorted(failures):
        print(line)
    if failures:
        print(f"layer_order.py: {len(failures)} import(s) against the order of the layers")
        return 1
    print("layer_order.py: every import follows the order of the layers")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
