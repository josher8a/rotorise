#!/usr/bin/env python3
"""Hold the disagreements of the type checker with the run time to a list, and fail on a new one.

The pool spec emits `formal/.pool.types/`: the codecs of the pool as library calls, one check per
decision of the run time, and a rows file, which names the row of each check. The entry spec emits
`formal/.entry.types/` in the same form: the methods of an entry, one program for the pool of the
entries. Each directory has its own rows, its own programs and one owner spec. A check where the
run time accepts is a plain line. A check where the run time refuses is a line under
`@ts-expect-error`. This script compiles the slice program beside the path programs, and the path
programs one after another, so the peak memory holds one path program. Each program holds the
codecs file. The script maps each error to its row:

  an `accept` row with an error         the type refuses what the run time accepts
  a `refuse` row whose directive is     the type accepts what the run time refuses
  unused (TS2578)

A row with `after` reads the result of other rows: `after` is an id or a list of ids. Where one of
those rows disagrees, the type of the result is not the type of the run time, and the script reads
no verdict at the row. The script follows no chain, so a row names each row that it reads.

An error at no row is a hard failure, and the script prints the error. The codecs file has a row
for each declaration, so an error at a declaration is the row of that declaration. An error at a
`typing` row is a hard failure: the row puts an item of a draw to the type of its entity, so an
error is a defect of the generator and not a disagreement.

The set of disagreements is compared with `scripts/type_bridge_baseline.txt`. An id that is not in
the baseline fails, and the script prints the id. An id of the baseline that no longer fails is a
fall: the script counts it, and the check passes.

Usage:  python3 scripts/type_bridge.py            (exit 1 on a new id or a hard failure)
        python3 scripts/type_bridge.py --accept   (rewrite the baseline to the current set)
"""
import glob, json, os, re, subprocess, sys
from collections import Counter

FORMAL = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(FORMAL)
POOL = os.path.join(FORMAL, ".pool.types")
ENTRY = os.path.join(FORMAL, ".entry.types")
TYPE_DIRS = (POOL, ENTRY)
BASELINE = os.path.join(FORMAL, "scripts", "type_bridge_baseline.txt")
SLICES = "tsconfig.slices0.json"

ERROR = re.compile(r"^(.*?)\((\d+),(\d+)\): error (TS\d+): (.*)$")


def tsc(directory, program):
    """The compiler is TypeScript 7, the compiler of `npm run check`. The `typescript` package is
    TypeScript 6 for the compiler API, and the bridge reads only the diagnostics."""
    compiler = os.path.join(REPO, "node_modules", "typescript-7", "bin", "tsc")
    return subprocess.Popen(
        ["node", compiler, "-p", os.path.join(directory, program), "--pretty", "false"],
        cwd=REPO, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
    )


def programs(directory, *kinds):
    """The programs of a type directory, by name."""
    return sorted(
        os.path.basename(p)
        for kind in kinds
        for p in glob.glob(os.path.join(directory, f"tsconfig.{kind}[0-9]*.json"))
        if os.path.basename(p) != SLICES
    )


def compile_all():
    """Run the slice program beside the path programs, and the path programs one after another.
    The entry programs run in the sequence of the path programs. Return the directory, the program,
    the output and the exit code of each program."""
    sequence = [(POOL, p) for p in programs(POOL, "slices", "meets", "paths")]
    sequence += [(ENTRY, p) for p in programs(ENTRY, "entries")]
    slices = tsc(POOL, SLICES)
    results = []
    for directory, p in sequence:
        proc = tsc(directory, p)
        results.append((directory, p, proc.communicate()[0], proc.returncode))
    return [(POOL, SLICES, slices.communicate()[0], slices.returncode), *results]


def parse(directory, program, output, hard):
    """The errors of one program, as (file, line, column, code, message). The file is the name of the
    directory and the name of the file. Each other line is hard."""
    errors = []
    for line in output.splitlines():
        if not line.strip():
            continue
        m = ERROR.match(line)
        if m is None:
            if line.startswith(" ") and errors:
                continue  # the continuation of the message above
            hard.append(f"{program}: {line}")
            continue
        path = os.path.normpath(os.path.join(REPO, m[1]))
        if os.path.dirname(path) != directory:
            hard.append(f"{program}: an error outside the generated files: {line}")
            continue
        errors.append((os.path.join(os.path.basename(directory), os.path.basename(path)), int(m[2]), int(m[3]), m[4], m[5]))
    return errors


def disagreements(rows, errors, hard):
    """The ids of the rows where the type checker and the run time disagree."""
    at = {(r["file"], r["line"]): r for r in rows}
    directive = {(r["file"], r["line"] - 1): r for r in rows if r["expect"] == "refuse"}
    failing = set()
    for file, line, col, code, message in errors:
        if code == "TS2578" and (file, line) in directive:
            failing.add(directive[(file, line)]["id"])
            continue
        row = at.get((file, line))
        if row is not None and row["group"] == "typing":
            hard.append(f"{file}({line},{col}): {code}: an error at the typing row {row['id']}: {message}")
            continue
        if row is not None and row["expect"] == "accept":
            failing.add(row["id"])
            continue
        hard.append(f"{file}({line},{col}): {code}: an error at no row: {message}")
    unread = {r["id"] for r in rows if any(a in failing for a in as_list(r.get("after")))}
    return failing - unread


def as_list(after):
    """`after` of a row: an id, a list of ids, or nothing."""
    return [] if after is None else [after] if isinstance(after, str) else list(after)


def load_baseline():
    if not os.path.exists(BASELINE):
        return [], set()
    header, ids = [], set()
    for line in open(BASELINE, encoding="utf-8").read().splitlines():
        if line.startswith("#"):
            header.append(line)
        elif line:
            ids.add(line)
    return header, ids


def summary(ids):
    """The count of each group and expected verdict."""
    by = Counter("|".join(i.split("|", 2)[:2]) for i in ids)
    return ", ".join(f"{k} {n}" for k, n in sorted(by.items())) or "none"


def main():
    rows = []
    for directory in TYPE_DIRS:
        rows_path = os.path.join(directory, "rows.json")
        if not os.path.exists(rows_path):
            print(f"no {rows_path}: run the vector emit first (EMIT_LEAN_REFUSALS=1 vitest)")
            return 1
        for r in json.load(open(rows_path, encoding="utf-8")):
            r["file"] = os.path.join(os.path.basename(directory), r["file"])
            rows.append(r)
    for directory, kind in ((POOL, "paths"), (ENTRY, "entries")):
        if not glob.glob(os.path.join(directory, f"tsconfig.{kind}[0-9]*.json")):
            print(f"no {kind} program in {directory}: run the vector emit first (EMIT_LEAN_REFUSALS=1 vitest)")
            return 1
    hard = []
    errors = set()
    for directory, program, output, code in compile_all():
        if code not in (0, 1, 2):
            hard.append(f"{program}: tsc exit {code}")
        errors.update(parse(directory, program, output, hard))
    failing = disagreements(rows, sorted(errors), hard)
    header, baseline = load_baseline()
    new = sorted(failing - baseline)
    fallen = baseline - failing
    print(f"rows {len(rows)}, disagreements {len(failing)}: {summary(failing)}")
    for line in hard:
        print(f"HARD  {line}")
    if hard:
        return 1
    if "--accept" in sys.argv:
        with open(BASELINE, "w", encoding="utf-8") as out:
            out.write("".join(f"{h}\n" for h in header))
            out.write("".join(f"{i}\n" for i in sorted(failing)))
        print(f"baseline rewritten: {len(new)} new, {len(fallen)} fallen")
        return 0
    for i in new:
        print(f"NEW   {i}")
    if fallen:
        print(f"{len(fallen)} id(s) of the baseline no longer fail: run --accept to drop them")
    if new:
        print(f"{len(new)} new disagreement(s): {summary(new)}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
