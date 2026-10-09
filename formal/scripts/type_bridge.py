#!/usr/bin/env python3
"""Hold the disagreements of the type checker with the run time to a list, and fail on a new one.

The pool spec emits `formal/.pool.types/`: the codecs of the pool as library calls, one check per
decision of the run time, and a rows file, which names the row of each check. A check where the
run time accepts is a plain line. A check where the run time refuses is a line under
`@ts-expect-error`. This script compiles two programs in parallel, the slice checks and the path
checks, each with the codecs file, and maps each error to its row:

  an `accept` row with an error         the type refuses what the run time accepts
  a `refuse` row whose directive is     the type accepts what the run time refuses
  unused (TS2578)

A row with `after` reads the result of another row. Where that row disagrees, the type of the
result is not the type of the run time, and the script reads no verdict at the row.

An error at no row is a hard failure, and the script prints the error. The codecs file has a row
for each declaration, so an error at a declaration is the row of that declaration.

The set of disagreements is compared with `scripts/type_bridge_baseline.txt`. An id that is not in
the baseline fails, and the script prints the id. An id of the baseline that no longer fails is a
fall: the script counts it, and the check passes.

Usage:  python3 scripts/type_bridge.py            (exit 1 on a new id or a hard failure)
        python3 scripts/type_bridge.py --accept   (rewrite the baseline to the current set)
"""
import json, os, re, subprocess, sys
from collections import Counter

FORMAL = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(FORMAL)
TYPES = os.path.join(FORMAL, ".pool.types")
BASELINE = os.path.join(FORMAL, "scripts", "type_bridge_baseline.txt")
PROGRAMS = ("tsconfig.slices.json", "tsconfig.paths.json")

ERROR = re.compile(r"^(.*?)\((\d+),(\d+)\): error (TS\d+): (.*)$")


def compile_all():
    """Run the two programs at one time, and return the output and the exit code of each."""
    procs = [
        subprocess.Popen(
            ["npx", "--no-install", "tsc", "-p", os.path.join(TYPES, p), "--pretty", "false"],
            cwd=REPO, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        for p in PROGRAMS
    ]
    return [(p, *proc.communicate()[:1], proc.returncode) for p, proc in zip(PROGRAMS, procs)]


def parse(program, output, hard):
    """The errors of one program, as (file, line, column, code, message). Each other line is hard."""
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
        if os.path.dirname(path) != TYPES:
            hard.append(f"{program}: an error outside the generated files: {line}")
            continue
        errors.append((os.path.basename(path), int(m[2]), int(m[3]), m[4], m[5]))
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
        if row is not None and row["expect"] == "accept":
            failing.add(row["id"])
            continue
        hard.append(f"{file}({line},{col}): {code}: an error at no row: {message}")
    unread = {r["id"] for r in rows if r.get("after") in failing}
    return failing - unread


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
    rows_path = os.path.join(TYPES, "rows.json")
    if not os.path.exists(rows_path):
        print(f"no {rows_path}: run the vector emit first (EMIT_LEAN_REFUSALS=1 vitest)")
        return 1
    rows = json.load(open(rows_path, encoding="utf-8"))
    hard = []
    errors = set()
    for program, output, code in compile_all():
        if code not in (0, 1, 2):
            hard.append(f"{program}: tsc exit {code}")
        errors.update(parse(program, output, hard))
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
