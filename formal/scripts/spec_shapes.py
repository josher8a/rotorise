#!/usr/bin/env python3
"""What shape is each `src/*.spec.ts`, and where does a test pin *wording*?

Written for §8's question about the harness failing correct code. A refusal that the
algebra requires is a fact about the calculus; the *words* the refusal is phrased in are
not, so a `toThrow(/text/)` at an algebra-required refusal fails a correct rewrite for a
reason the specification does not have. This counts those sites and classifies the files,
so the argument rests on a number that can be recomputed rather than on a reading.

**The classification is mechanical, and that is the point of it being here.** A file is

  algebra-law     it imports a law checker from `./testing` — `checkRoundTrip`,
                  `checkEquivalent`, `checkDecodesAreWritable`, `checkStable`, `checkIso`,
                  `checkUniqueAdmission`, `checkAgainst`, `checkMembersStable`,
                  `checkEncodePaths`. These are the harness's statements of §2 and §6, so a
                  file that calls one is asserting the algebra whatever else it does.
  bridge          it names `lean` — the emitter and its vectors.
  implementation  everything else: the key layer, paths, native, types.

That is a proxy and it is stated as one. It cannot see a file that asserts an equation by
hand without the harness, and it will call a file algebra-law for one incidental
`checkRoundTrip`. What it can do is be rerun.

**Its one known false positive, measured rather than supposed.** `opaque.types.spec.ts`
imports a law checker and is not algebra-law: it is type reflection, and the refusals it
pins are about what the *type* rejects. Tier (i) excluded it by hand for that reason. The
whole of `src/` was read against this classification while doing so, and it is the only
file the proxy gets wrong — which is a better rate than the docstring above implies, and
the reason to leave the proxy alone rather than special-case it. A caller that wants the
tier's scope should exclude that one file, not adjust the counts.

`toThrow` sites are counted by argument shape after joining the file into one line, so a
call split across lines is not missed — the shapes are BARE, REGEX, CODECERROR, STRING and
OTHER, and only REGEX pins wording.

Usage:  python3 scripts/spec_shapes.py            (run from formal/)
        python3 scripts/spec_shapes.py --files    (per-file table)
"""
import re, sys, glob, os, collections

SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "src")

LAW_CHECKERS = ("checkRoundTrip", "checkEquivalent", "checkDecodesAreWritable",
                "checkStable", "checkIso", "checkUniqueAdmission", "checkAgainst",
                "checkMembersStable", "checkEncodePaths")

def shape(arg: str) -> str:
    a = arg.strip()
    if a == "":            return "BARE"
    if a.startswith("/"):  return "REGEX"
    if a.startswith("CodecError"): return "CODECERROR"
    if a[0] in "\"'`":     return "STRING"
    return "OTHER"

def classify(path: str, text: str) -> str:
    if "lean" in os.path.basename(path):
        return "bridge"
    if any(c in text for c in LAW_CHECKERS):
        return "algebra-law"
    return "implementation"

def main() -> int:
    # recursive: `src/` nests its directories, and a flat glob passes over a nested file in silence
    files = sorted(glob.glob(os.path.join(SRC, "**", "*.spec.ts"), recursive=True) +
                   glob.glob(os.path.join(SRC, "**", "*.test.ts"), recursive=True))
    kinds = collections.Counter()
    shapes = collections.Counter()
    per_file = []
    regex_files = 0
    for path in files:
        text = open(path, encoding="utf-8").read()
        kind = classify(path, text)
        kinds[kind] += 1
        # join to one line so a split call is still one match
        flat = re.sub(r"\s+", " ", text)
        counts = collections.Counter()
        for m in re.finditer(r"\.toThrow\(", flat):
            i, depth = m.end(), 1
            while i < len(flat) and depth:
                if flat[i] == "(": depth += 1
                elif flat[i] == ")": depth -= 1
                i += 1
            counts[shape(flat[m.end():i - 1])] += 1
        shapes.update(counts)
        if counts["REGEX"]:
            regex_files += 1
        per_file.append((os.path.basename(path), kind, counts))

    print(f"  spec files                  {len(files)}")
    for k in ("algebra-law", "bridge", "implementation"):
        print(f"  {k:26s}{kinds[k]:4d}")
    print()
    for k in ("BARE", "REGEX", "CODECERROR", "STRING", "OTHER"):
        print(f"  toThrow {k:18s}{shapes[k]:4d}")
    print(f"\n  files with a REGEX site     {regex_files}")
    print(f"  REGEX sites in algebra-law  "
          f"{sum(c['REGEX'] for _, k, c in per_file if k == 'algebra-law')}")

    if "--files" in sys.argv:
        print()
        for name, kind, c in per_file:
            if c["REGEX"]:
                print(f"  {name:34s} {kind:15s} regex={c['REGEX']:3d} "
                      f"bare={c['BARE']:3d} codecError={c['CODECERROR']:3d}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
