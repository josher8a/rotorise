#!/usr/bin/env python3
"""Hold the disagreements of the type checker with the run time to a list, and fail on a new one.

The pool spec emits `formal/.pool.types/`: the codecs of the pool as library calls, one check per
decision of the run time, and a rows file, which names the row of each check. The entry spec emits
`formal/.entry.types/` in the same form: the methods of an entry, one program for the pool of the
entries. Each directory has its own rows, its own programs and one owner spec. A check where the
run time accepts is a plain line. A check where the run time refuses is a line under
`@ts-expect-error`, and a refused path row is a bare line (the row has `bare`). This script compiles the slice program beside the path programs, and the path
programs one after another, so the peak memory holds one path program. Each program holds the
codecs file. The script maps each error to its row:

  an `accept` row with an error         the type refuses what the run time accepts
  a `refuse` row whose directive is     the type accepts what the run time refuses
  unused (TS2578), or a bare `refuse`
  row with no error on its line

A row with `after` reads the result of other rows: `after` is an id or a list of ids. Where one of
those rows disagrees, the type of the result is not the type of the run time, and the script reads
no verdict at the row. The script follows no chain, so a row names each row that it reads.

A bare `refuse` row of a path program states the column where its first error starts (`hop`). The
site is the first prefix where the walk of `at` gives none: the element of the tuple or the object
of the clause at the last step of the prefix. A path that refuses on use (the frontier holds a
`never` codec, or two codecs) has the whole tuple as the site. The one compile of the program gives
the verdict and the site. An error that starts elsewhere is the id `site|<id of the row>`.

A `refuse` row of the entry pool can state where its error starts (`at`, a text of the line) and the
rule that the message of the library holds (`rule`). The directive hides the error, so the script
compiles a copy of the entry program without the directive of those rows. An error that starts
elsewhere is the id `site|<id of the row>`. A message that holds a rule text of the library, and
lacks `rule`, is the id `text|<id of the row>`. A plain compiler message is no fact, because
TypeScript 6 and 7 give another code for one refusal.

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
import glob, json, os, re, shutil, subprocess, sys, tempfile
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
        ["node", compiler, "-p", os.path.join(directory, program), "--pretty", "false", "--noErrorTruncation"],
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
                errors[-1][4] += " / " + line.strip()  # the continuation of the message above
                continue
            hard.append(f"{program}: {line}")
            continue
        path = os.path.normpath(os.path.join(REPO, m[1]))
        if os.path.dirname(path) != directory:
            hard.append(f"{program}: an error outside the generated files: {line}")
            continue
        errors.append([os.path.join(os.path.basename(directory), os.path.basename(path)), int(m[2]), int(m[3]), m[4], m[5]])
    return [tuple(e) for e in errors]


def disagreements(rows, errors, hard):
    """The ids of the rows where the type checker and the run time disagree."""
    at = {(r["file"], r["line"]): r for r in rows}
    directive = {(r["file"], r["line"] - 1): r for r in rows if r["expect"] == "refuse" and not r.get("bare")}
    bare = {(r["file"], r["line"]): r for r in rows if r.get("bare")}
    first = {}
    failing = set()
    for file, line, col, code, message in errors:
        if (file, line) in bare:
            first[(file, line)] = min(col, first.get((file, line), col))
            continue
        if code == "TS2578" and (file, line) in directive:
            failing.add(directive[(file, line)]["id"])
            continue
        row = at.get((file, line))
        if row is not None and row["id"].startswith("typing|"):
            hard.append(f"{file}({line},{col}): {code}: an error at the typing row {row['id']}: {message}")
            continue
        if row is not None and row["expect"] == "accept":
            failing.add(row["id"])
            continue
        hard.append(f"{file}({line},{col}): {code}: an error at no row: {message}")
    failing |= {r["id"] for key, r in bare.items() if key not in first}
    unread = {r["id"] for r in rows if any(a in failing for a in as_list(r.get("after")))}
    return failing - unread, first


def bare_sites(rows, failing, first):
    """The ids `site|<id>` of the bare rows whose first error starts at another column than `hop`.
    A row whose `after` row disagrees has no verdict."""
    return {
        "site|" + r["id"]
        for r in rows
        if r.get("bare")
        and (r["file"], r["line"]) in first
        and first[(r["file"], r["line"])] != r["hop"]
        and not any(a in failing for a in as_list(r.get("after")))
    }


def site_ids(rows, failing, hard):
    """The ids of the `refuse` rows that state a site (`at`) or a rule (`rule`), where the error of the
    row starts elsewhere (`site|<id>`), or where a library rule message lacks the rule (`text|<id>`).
    The directive of a row hides its error, so a copy of each entry program, with the directive of each
    such row removed, compiles beside the original. The copy lives in a scratch directory of the same
    depth as the type directory, so the imports resolve, and the script deletes the directory. A row
    whose `after` row disagrees has no verdict. A plain compiler message is no fact: TypeScript 6 and 7
    give another code for one refusal."""
    wanted = [r for r in rows if r["expect"] == "refuse" and (r.get("at") or r.get("rule"))]
    if not wanted:
        return set()
    scratch = tempfile.mkdtemp(prefix=".site", dir=FORMAL)
    try:
        lines, names = {}, set()
        for r in wanted:
            names.add(os.path.basename(r["file"]))
        for name in names:
            text = open(os.path.join(ENTRY, name), encoding="utf-8").read().split("\n")
            for r in wanted:
                if os.path.basename(r["file"]) != name:
                    continue
                if text[r["line"] - 2].strip() != "// @ts-expect-error":
                    hard.append(f"{r['id']}: no directive above the line {r['line']}")
                    continue
                text[r["line"] - 2] = "//"
            lines[name] = text
            with open(os.path.join(scratch, name), "w", encoding="utf-8") as out:
                out.write("\n".join(text))
            config = "tsconfig." + os.path.splitext(name)[0] + ".json"
            shutil.copy(os.path.join(ENTRY, config), os.path.join(scratch, config))
        found = {}
        for name in names:
            config = "tsconfig." + os.path.splitext(name)[0] + ".json"
            proc = tsc(scratch, config)
            output, code = proc.communicate()[0], proc.returncode
            if code not in (0, 1, 2):
                hard.append(f"{config}: tsc exit {code}")
            for file, line, col, _code, message in parse(scratch, config, output, hard):
                found.setdefault((os.path.basename(file), line), []).append((col, message))
    finally:
        shutil.rmtree(scratch, ignore_errors=True)
    ids = set()
    for r in wanted:
        if any(a in failing for a in as_list(r.get("after"))):
            continue
        name = os.path.basename(r["file"])
        errors = found.get((name, r["line"]))
        if not errors:
            continue  # the type accepts the row: the verdict of the row is the disagreement
        first = min(col for col, _ in errors)
        line = lines[name][r["line"] - 1]
        if r.get("at"):
            starts = [m.start() + 1 for m in re.finditer(re.escape(r["at"]), line)]
            if not starts:
                hard.append(f"{r['id']}: the text {r['at']} is not in the line")
            elif first not in starts:
                ids.add("site|" + r["id"])
        message = " / ".join(m for _, m in errors)
        if r.get("rule") and "ErrorMessage<" in message and r["rule"] not in message:
            ids.add("text|" + r["id"])
    return ids


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
    failing, first = disagreements(rows, sorted(errors), hard)
    failing |= site_ids(rows, failing, hard)
    failing |= bare_sites(rows, failing, first)
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
