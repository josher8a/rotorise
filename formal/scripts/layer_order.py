#!/usr/bin/env python3
"""Check that each import follows the order of the layers, on both sides of the bridge.

The check reads two trees. The Lean side is `Calculus/`. The host side is `src/`, without the
spec files and the test files. Each side has its own rule, and each rule is below.

THE RULE FOR THE LEAN SIDE

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

THE RULE FOR THE HOST SIDE

`HOST_ORDER` lists the files of `src/` from the lowest to the highest. A file imports no file
that is higher in the list. An `import type` counts, because a type that a lower file takes from
a higher file is a coupling that the erased import hides. The list also names the layer of the
model that each file projects, so a reader sees which fact each file owns. The order is the
order of the run-time imports, which have no cycle. A file of `src/` that the list does not
name fails. Give a new file its place in the list before the file holds code.

WHAT THIS CHECKS, AND WHAT IT CANNOT

The check reads the import header of each `.lean` file under `Calculus/`. The root
`Calculus.lean` imports every module and is no layer, so the check does not read it. An
import of a module outside `Calculus` (Mathlib, Batteries) is not a layer, and passes.

The check sees the direct import only. A declaration that a module cites through a
transitive import is invisible here. Remove the direct import and build to find that
citation.

On the host side the check reads the `import` and `export ... from` statements of each file,
after it removes the comments. It sees a relative specifier only. It does not read the
spec files, and it does not read a type that a file names through `import('...')`.

USAGE

    layer_order.py [FORMAL_DIR]

`FORMAL_DIR` holds the folder `Calculus/`. The default is the parent of this script's folder.
The folder `src/` is the sibling of `FORMAL_DIR`.
The exit code is 1 when an import goes against the order, and 0 otherwise.
"""

import glob
import os
import re
import sys

# The files of `src/`, from the lowest to the highest, each with the layer of the model that it
# projects. "none" names a file that no layer of the model states.
HOST_ORDER = [
    ("utils.d.ts", "none: general type utilities"),
    ("codec/result.ts", "none: the failure value that both directions of a codec are written in"),
    ("codec/standard.ts", "none: the types of the Standard Schema"),
    ("codec/attribute.ts", "Dynamo/Domain.lean and Dynamo/Lang/Store.lean: the carrier and the store"),
    ("codec/value.ts", "Dynamo/Domain.lean and Dynamo/AttrEq.lean: the value side, under the pair"),
    ("codec/term.ts", "Dynamo/Lang/Term.lean and Dynamo/Lang/Scope.lean: the term language"),
    ("codec/pathModel.ts", "none: the type-level read of a term, for `at`"),
    ("codec/scoped.ts", "Dynamo/Analysis/Scope*.lean: the decisions over the graph of a closed codec"),
    ("codec/build.ts", "none: the one place that constructs a codec"),
    ("codec/denote.ts", "Dynamo/Alg/*.lean and Dynamo/Lang/Equations.lean: the pair of each constructor"),
    ("codec/clause.ts", "Lang/ScopePath.lean: the clause `φ` of `narrowC`, a closed codec, and the opening of a pattern"),
    ("codec/frontier.ts", "Lang/CodecPath.lean and Lang/ScopePath.lean: the segment of a path, and the frontier along a path"),
    ("codec/codec.ts", "Dynamo/Alg/Codec.lean: a codec and its laws, with the constructors"),
    ("codec/pin.ts", "none: the key paths of a type"),
    ("codec/native.ts", "none: the marshaller of the SDK, a migration aid outside the model"),
    ("codec/lean.ts", "Bridge/*.lean: the emitter of the vectors"),
    ("codec/testing.ts", "Dynamo/Alg/Codec.lean: the laws, run as checks"),
    ("codec/typeVectors.ts", "Bridge/*.lean: the type bridge, through `type_bridge.py`"),
    ("Rotorise.ts", "Dynamo/Alg/Key*.lean and Bridge/KeyRows.lean: the key layer, over the codecs"),
]

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


def host_files(src):
    """The files of `src/` that the host order covers, as paths relative to `src/`."""
    found = []
    for path in glob.glob(os.path.join(src, "**", "*.ts"), recursive=True):
        if re.search(r"\.(spec|test)\.ts$", path):
            continue
        found.append(os.path.relpath(path, src).replace(os.sep, "/"))
    return found


EDGE = re.compile(
    r"(?:^|\n)[ \t]*(import|export)[ \t]+(type[ \t]+)?(?:\{[^}]*\}|\*[^;\n]*?|[\w$]+)[ \t\n]+from[ \t]+'(\.[^']*)'"
)


def host_imports(path):
    """The relative modules that a TypeScript file imports or re-exports, with `import type` marked."""
    with open(path, encoding="utf-8") as f:
        text = f.read()
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    text = re.sub(r"(?m)^[ \t]*//.*$", "", text)
    return [(m.group(3), bool(m.group(2))) for m in EDGE.finditer(text)]


def host_failures(src):
    """The imports of `src/` that go against `HOST_ORDER`, and the files that the order omits."""
    rank = {name: i for i, (name, _) in enumerate(HOST_ORDER)}
    failures = []
    for rel in sorted(host_files(src)):
        if rel not in rank:
            failures.append(f"src/{rel}: the file has no place in the host order")
            continue
        for spec, is_type in host_imports(os.path.join(src, rel)):
            base = os.path.normpath(os.path.join(os.path.dirname(rel), spec)).replace(os.sep, "/")
            target = base + (".d.ts" if os.path.exists(os.path.join(src, base + ".d.ts")) else ".ts")
            if target not in rank:
                failures.append(f"src/{rel}: imports {spec}, a file with no place in the host order")
            elif rank[target] > rank[rel]:
                kind = "import type" if is_type else "import"
                failures.append(f"src/{rel}: {kind} {spec}: src/{target} is higher in the host order")
    for name in rank:
        if not os.path.exists(os.path.join(src, name)):
            failures.append(f"src/{name}: the host order names a file that does not exist")
    return failures


def main(argv):
    formal = argv[1] if len(argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
    root = os.path.join(formal, "Calculus")
    src = os.path.join(formal, "..", "src")
    if not os.path.isdir(root):
        print(f"layer_order.py: no folder {root}", file=sys.stderr)
        return 2
    if not os.path.isdir(src):
        print(f"layer_order.py: no folder {src}", file=sys.stderr)
        return 2
    failures = host_failures(src)
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
