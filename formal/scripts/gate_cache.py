#!/usr/bin/env python3
"""Reuse the result of a gate step whose inputs did not change since the step passed.

The key of a step is the hash of each file that the step reads, of the environment variables that
the step reads, and of the command. A step that passes stores its key, and the files that it
writes. A later run with the same key restores those files and runs nothing. A key over every
input gives the answer of a run, so a reuse is honest only while the key holds every input.

The compiler lists the modules that an emit spec loads, so no list of modules is kept by hand.
The compiler cannot see a file that a module reads or writes at run time, so `SPECS` declares
those files. The script fails when a module of a closure reads a file and `SPECS` declares no
read for the module, and when an emit writes a generated file that `SPECS` does not declare.

A kernel job reads its generated file and the oleans. The oleans equal the sources of the model
only where `lake build` passed on those sources. The model is each `.lean` source of this package,
the lake files and the toolchain. So `build` hashes the model before `lake build`, and writes that
hash to the seal only when the build passed and the model did not change during the build. A
kernel job takes the model hash from the seal, and stores an entry only under a seal. A run with
no seal reads an entry and stores none. The type bridge reads `.pool.types/`, the modules that
its programs load, its baseline and its script.

GATE_CACHE names the directory, and the default is `formal/.gate-cache`. GATE_CACHE_OFF=1 runs
every step and stores nothing. GATE_REUSE_LOG names a file where each reuse adds one line.
GATE_SEAL names the file of the seal for the run.

Usage:  gate_cache.py emit                the emit specs whose key has no entry
        gate_cache.py types               the type bridge, unless its key has an entry
        gate_cache.py build               `lake build`, and the seal of the run when it passed
        gate_cache.py kernel <file> <out> the kernel job of <file>, unless its key has an entry.
                                          The output of the job goes to <out>
        gate_cache.py kernel-files        the file of each kernel job, one for each line
"""
import hashlib, os, re, shutil, subprocess, sys, tempfile, time

FORMAL = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(FORMAL)
CACHE = os.environ.get("GATE_CACHE") or os.path.join(FORMAL, ".gate-cache")
OFF = os.environ.get("GATE_CACHE_OFF") == "1"
TYPES = ".pool.types"
TSC = os.path.join(REPO, "node_modules", "typescript-7", "bin", "tsc")
KEEP_DAYS = 14

# The files that each emit spec writes into `formal/`, and the files that the spec reads at run time.
SPECS = {
    "src/codec/lean/lean.spec.ts": {
        "writes": [".resolutions.lean", ".legacyreads.lean", ".readverdicts.lean",
                   ".separations.lean", ".disjoints.lean", ".vectors.full.lean",
                   ".readvectors.lean"],
        "reads": ["formal/lean.sample.lean", "formal/lean.sample.check.lean"],
    },
    "src/codec/lean/lean.pool.spec.ts": {
        "writes": [".pool.disjoints.lean", ".pool.separations.lean", ".pool.slices.lean",
                   ".pool.paths0.lean", ".pool.paths1.lean", ".pool.paths2.lean",
                   ".pool.paths3.lean", ".pool.guards.lean", ".pool.fits.lean",
                   ".pool.meets.lean", TYPES],
        "reads": [],
    },
    "src/codec/lean/lean.key.spec.ts": {"writes": [".keys.lean"], "reads": []},
    "src/codec/lean/lean.update.spec.ts": {"writes": [".updates.lean"], "reads": []},
}
EMIT = ["npx", "--no-install", "vitest", "run", "--reporter=dot"]
# Each step of vitest reads these files beside the closure of its specs.
VITEST = ["package-lock.json", "tsconfig.json", "vitest.config.ts", "setupVitest.ts"]
READ = re.compile(r"\b(readFileSync|readFile|readdirSync|readdir|createReadStream|opendirSync)\b")
ENV = re.compile(r"process\.env\.([A-Za-z_][A-Za-z0-9_]*)")


def digest(paths):
    """The hash of each path, as a path relative to the repository and the hash of its content."""
    h = hashlib.sha256()
    for path in sorted(set(paths)):
        h.update(os.path.relpath(path, REPO).encode() + b"\0")
        with open(path, "rb") as f:
            h.update(hashlib.sha256(f.read()).digest())
    return h


def closure(roots):
    """The modules of the repository that the compiler loads from `roots`."""
    out = subprocess.run(
        ["node", TSC, "--ignoreConfig", "--listFilesOnly", "--noEmit", "--module", "preserve",
         "--moduleResolution", "bundler", "--allowJs", "--resolveJsonModule",
         "--target", "es2022", "--lib", "es2022", "--types", "node", *roots],
        cwd=REPO, capture_output=True, text=True,
    )
    files = [os.path.normpath(os.path.join(REPO, line.strip()))
             for line in out.stdout.splitlines() if line.strip()]
    if out.returncode not in (0, 1, 2) or not files or not all(map(os.path.isfile, files)):
        sys.exit(f"gate_cache: the compiler listed no closure for {roots}: {out.stdout}{out.stderr}")
    return [f for f in files
            if f.startswith(REPO + os.sep) and f"{os.sep}node_modules{os.sep}" not in f]


def key(kind, paths, command, env_from=(), extra=()):
    """The key of a step: its files, the environment variables that its modules read, its command,
    the strings of `extra`, and this script."""
    h = digest([*paths, os.path.abspath(__file__)])
    names = set()
    for path in env_from:
        with open(path, encoding="utf-8", errors="replace") as f:
            names.update(ENV.findall(f.read()))
    for name in sorted(names):
        h.update(f"{name}={os.environ.get(name, '')}\0".encode())
    h.update("\0".join(command).encode())
    for text in extra:
        h.update(b"\0" + text.encode())
    return os.path.join(CACHE, kind, h.hexdigest())


def reused(line):
    log = os.environ.get("GATE_REUSE_LOG")
    if log:
        with open(log, "a", encoding="utf-8") as f:
            f.write(line + "\n")


def prune(kind):
    """Delete the entries that no run read or wrote for `KEEP_DAYS` days."""
    root = os.path.join(CACHE, kind)
    limit = time.time() - KEEP_DAYS * 86400
    for name in os.listdir(root):
        path = os.path.join(root, name)
        if os.path.getmtime(path) < limit:
            shutil.rmtree(path) if os.path.isdir(path) else os.remove(path)


def hit(entry):
    if OFF or not os.path.exists(entry):
        return False
    os.utime(entry)
    return True


def store(kind, entry, fill=None):
    """Write an entry through a temporary path, so a reader sees a whole entry or none."""
    if OFF:
        return
    os.makedirs(os.path.dirname(entry), exist_ok=True)
    tmp = tempfile.mkdtemp(dir=os.path.dirname(entry))
    if fill:
        fill(tmp)
    try:
        os.rename(tmp, entry)
    except OSError:  # another run stored the same key
        shutil.rmtree(tmp)
    prune(kind)


def spec_key(spec, files):
    readers = [f for f in files if READ.search(open(f, encoding="utf-8", errors="replace").read())]
    undeclared = [f for f in readers if os.path.relpath(f, REPO) not in SPECS
                  or not SPECS[os.path.relpath(f, REPO)]["reads"]]
    if undeclared:
        sys.exit("gate_cache: a module reads a file at run time, and SPECS declares no read for "
                 f"it: {[os.path.relpath(f, REPO) for f in undeclared]}")
    inputs = [*files, *(os.path.join(REPO, p) for p in VITEST),
              *(os.path.join(REPO, p) for p in SPECS[spec]["reads"])]
    return key("emit", inputs, [*EMIT, spec, "EMIT_LEAN_REFUSALS=1"], env_from=files)


def generated():
    """Each generated file in `formal/`, with the time of its last write."""
    found = {f: os.path.getmtime(os.path.join(FORMAL, f))
             for f in os.listdir(FORMAL) if f.startswith(".") and f.endswith(".lean")}
    types = os.path.join(FORMAL, TYPES)
    if os.path.isdir(types):
        found[TYPES] = max((os.path.getmtime(os.path.join(types, f)) for f in os.listdir(types)),
                           default=0)
    return found


def restore(entry, spec):
    for name in SPECS[spec]["writes"]:
        target = os.path.join(FORMAL, name)
        if name == TYPES:
            shutil.rmtree(target, ignore_errors=True)
            shutil.copytree(os.path.join(entry, name), target)
        else:
            shutil.copy2(os.path.join(entry, name), target)


def emit():
    keys = {spec: spec_key(spec, closure([spec])) for spec in SPECS}
    misses = []
    for spec, entry in keys.items():
        if hit(entry):
            restore(entry, spec)
            reused(f"vector emit: {os.path.basename(spec)} {os.path.basename(entry)[:12]}")
        else:
            misses.append(spec)
    if not misses:
        return 0
    marker = time.time()
    env = dict(os.environ, EMIT_LEAN_REFUSALS="1")
    rc = subprocess.run([*EMIT, *misses], cwd=REPO, env=env).returncode
    if rc != 0:
        return rc
    written = {f for f, at in generated().items() if at >= marker}
    declared = {name for spec in misses for name in SPECS[spec]["writes"]}
    if written != declared:
        print("gate_cache: the emit wrote files that SPECS does not declare, or did not write "
              f"files that it declares: written {sorted(written)}, declared {sorted(declared)}")
        return 1
    for spec in misses:
        def fill(tmp, spec=spec):
            for name in SPECS[spec]["writes"]:
                source = os.path.join(FORMAL, name)
                if name == TYPES:  # the files of this run only, not a file that an older emit left
                    os.makedirs(os.path.join(tmp, name))
                    for f in os.listdir(source):
                        if os.path.getmtime(os.path.join(source, f)) >= marker:
                            shutil.copy2(os.path.join(source, f), os.path.join(tmp, name, f))
                else:
                    shutil.copy2(source, os.path.join(tmp, name))
        store("emit", keys[spec], fill)
    return 0


def model():
    """The sources of the model, the lake files and the toolchain."""
    found = [os.path.join(FORMAL, f) for f in ("lakefile.toml", "lake-manifest.json", "lean-toolchain")]
    for root, dirs, files in os.walk(FORMAL):
        dirs[:] = [d for d in dirs if not d.startswith(".")]
        found += [os.path.join(root, f) for f in files
                  if f.endswith(".lean") and not f.startswith(".") and f != "Scratch.lean"]
    return found


def model_digest():
    """The hash of the model."""
    return digest(model()).hexdigest()


def sealed():
    """The model hash that `build` sealed for this run, or an empty string."""
    seal = os.environ.get("GATE_SEAL")
    if not seal or not os.path.isfile(seal):
        return ""
    with open(seal, encoding="utf-8") as f:
        return f.read().strip()


def kernel_entry(file, model_hash):
    return key("kernel", [os.path.join(FORMAL, file)], ["lake", "env", "lean", file,
                                                         "#assert_axioms_module"],
               extra=[model_hash])


def build():
    """Run `lake build`. Seal the model hash from before the build when the build passed on a model
    that did not change during the build."""
    seal = os.environ.get("GATE_SEAL")
    if seal:
        open(seal, "w", encoding="utf-8").close()
    before = model_digest()
    rc = subprocess.run(["lake", "build"], cwd=FORMAL).returncode
    if rc == 0 and seal and model_digest() == before:
        with open(seal, "w", encoding="utf-8") as f:
            f.write(before)
    return rc


def kernel(file, out):
    """Run the kernel job of `file`, unless its key has an entry. The key comes from before the
    job. The job stores an entry when it passes with no output, the file did not change during
    the job, and the run has a seal."""
    seal = sealed()
    entry = kernel_entry(file, seal or model_digest())
    if hit(entry):
        reused(f"vector bridge: {file} {os.path.basename(entry)[:12]}")
        open(out, "w", encoding="utf-8").close()
        return 0
    with open(out, "w", encoding="utf-8") as f:
        rc = subprocess.run(["lake", "env", "lean", file], cwd=FORMAL, stdout=f,
                            stderr=subprocess.STDOUT).returncode
    if rc == 0 and os.path.getsize(out) == 0 and seal and kernel_entry(file, seal) == entry:
        store("kernel", entry)
    return rc


def kernel_files():
    """The file of each kernel job: each `.lean` file that a spec writes, then each `.lean` file
    that a spec reads. Each is a file of `formal/`."""
    return [os.path.basename(name) for kind in ("writes", "reads") for files in SPECS.values()
            for name in files[kind] if name.endswith(".lean")]


def types():
    script = os.path.join(FORMAL, "scripts", "type_bridge.py")
    if not os.path.isdir(os.path.join(FORMAL, TYPES)):  # the script names the missing emit
        return subprocess.run([sys.executable, script], cwd=FORMAL).returncode
    roots = [os.path.join(FORMAL, TYPES, f) for f in os.listdir(os.path.join(FORMAL, TYPES))]
    programs = [f for f in roots if f.endswith(".ts")]
    files = closure(programs)
    baseline = os.path.join(FORMAL, "scripts", "type_bridge_baseline.txt")
    entry = key("types", [*roots, *files, script, baseline,
                          *(os.path.join(REPO, p) for p in VITEST[:2])],
                ["python3", "scripts/type_bridge.py"])
    if hit(entry):
        reused(f"type bridge {os.path.basename(entry)[:12]}")
        return 0
    rc = subprocess.run([sys.executable, script], cwd=FORMAL).returncode
    if rc == 0:
        store("types", entry)
    return rc


def main(argv):
    if argv[:1] == ["emit"]:
        return emit()
    if argv[:1] == ["types"]:
        return types()
    if argv[:1] == ["build"]:
        return build()
    if argv == ["kernel-files"]:
        print("\n".join(kernel_files()))
        return 0
    if len(argv) == 3 and argv[0] == "kernel":
        return kernel(argv[1], argv[2])
    print(__doc__.split("Usage:")[1], file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
