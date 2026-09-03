# Handoff

**Branch `wip/map-types`. `lake build` green and warning-free, `#assert_axioms_all` and
`#lint_calculus` over 21 modules, and all four Python guards — `guard_reach.py`,
`name_drift.py`, `doc_counts.py --check`, `ratchet.py` — exit 0.** Verify with
`formal/scripts/gate.sh`, which runs all seven and exits nonzero on any failure — by exit code
and not by eye. `complexity.py`, `complexity.lean`, `twins.py` and `vocab_audit.py` report and
never fail; they are not in the gate. Nor is `fidelity_audit.py`, which reports but **does**
exit 1 — if `#assert_axioms_all` is absent, which is its one guard rather than its measurement.

Delete this file once read. The commit messages are the record; `git log` is now the only
change log there is.

---

## The one idea

**Probe the fix you were handed, and it will tell you where the defect actually is.** Three
times in eleven commits a brief named a repair that could not have worked, and writing it out
far enough to fail is what located the cause:

- "one inversion lemma for `inL` at a general `GroundKind`" — the statement respelled `HLit`,
  which exists, and a `Prop` existential says nothing about the nine rows answering `false`.
  Writing it found the real gap: `restrict_e_isSome` was `@[simp]` and `restrict_p_isSome` did
  not exist, so every literal row on the read side unfolded `Codec.restrict` by hand.
- "the per-constructor rows go through one `List.all` argument" — they are `Term` constructors,
  not `Slot` cases, and the per-row work differs. What was there instead: sixteen rows whose
  proofs were byte identical.
- "cheap, because `vocab_audit.py` already computes the pair table" — it computes one that asks
  *presence* where the gap was *shape*, and it scored `restrict` complete on the day the missing
  twin was costing 683×.

The corollary, which is the arc's other half: **a number is a claim about the tree and has to
be measured, including the numbers a new instrument produces.** Every metric tried here was
wrong in a way only measurement caught.

---

## What landed

Eleven commits since `93f44d2`. Four instruments, two wins, three negative results.

| commit | why |
| --- | --- |
| `2d57420` | `name_drift.py`'s docstring check cleared citations with themselves; §9 gained the `~~retired~~` marker at JH's call, 18 stale pointers fixed |
| `09d0654` | `ratchet.py` — §10's two guards, built as ratchets because a docstring bar at 269 is decoration |
| `9f1be62` | HANDOFF item 2 named the wrong file and a count that does not reproduce |
| `7fff6e8` | `sepV_refine_disjoint` general in the base — the value side of a claim `codec-calculus.md` already made |
| `7fc0c4f` | two mechanisms `7fff6e8` exposed: a signature span moves a count in a file you did not edit, and the ratchet steers a proof |
| `cdf766c` | that commit's own docstring said what the code says — 13 lines to 4 |
| `2c62f6b` | `complexity.py`/`complexity.lean`, the `branches` ratchet, and two measured dead ends |
| `bd80576` | `AdmA_exact`'s fan named by `fanOf` — 380× to 12×, and the ratchet's own +1-per-declaration defect |
| `423c276` | the fan was a missing read-side inversion, not a missing `inL` lemma |
| `db3eb6d` | the two densest proofs were sixteen copies of two simp sets |
| `cc8477b` | `twins.py`, and the pair table could not have found the gap that motivated it |

**The instruments, all recorded in `ARCHITECTURE.md` §6 with their blind spots.**

- **`ratchet.py`** — four per-file counts, failing on a *rise*: `unfolding_sites`,
  `retirement_marks`, `undocumented_public_theorems` and `branches`. **The values are in
  `scripts/ratchets.json` and are not repeated here**, because three places typed `branches` by
  hand and gave 3972, 4042 and 5260. Baselines live in that file, never in the script, so the guard's source stays still and a
  changed number is worth reading. `--accept` writes falls; a rise additionally needs
  `--allow-rise`, so weakening the guard has to be a sentence in a commit message. A metric
  with no baseline fails rather than passing as twenty new files.
- **`complexity.py`** — decision points per declaration and file. Not a restatement of
  `unfolding_sites`: Spearman 0.56, and `Orthogonality.lean` is 31 branches per unfolding site
  where `Discharge.lean` is 9. The *count* is ratcheted and the *density* only printed, because
  a density has lines in its denominator.
- **`complexity.lean`** — proof-term DAG size, sharing ratio, direct deps, and `fanOf`.
  **Count the DAG, not the tree**: `Expr` is a DAG and the naive size read `AdmA_exact` as
  2754337 when the kernel holds 7239. `dagSize` reports a number and never a location, which is
  why `fanOf` exists.
- **`twins.py`** — one-sided inversions paired on `(stem, suffix)`. `@[simp]` on the surviving
  side is the filter that works: it picks 2 real candidates out of 15.

---

## Pick up here

**Nothing is queued.** Every decision is answered and every item is struck below with its commit
and its result — because **each brief was wrong about something load-bearing, and the correction
is the part worth inheriting**. Two of the five ended as refusals rather than changes, and those
two are the ones to read first.

1. ~~**The 13 citations**~~ — **ten landed, three refused on principle.** Eight names in
   `ARCHITECTURE.md`, two in `README.md`, each the theorem's name added to the sentence that
   already made its claim, so `name_drift.py` guards the correspondence from now on.

   **The three normative ones are refused, not deferred**, and `docs/codec-calculus.md`'s own
   second paragraph is why: *"it names no implementation of one… nothing here is true because
   something elsewhere checks it."* It cites **zero** `Calculus/` names, deliberately. The two §2
   corollaries the proposal wanted anchored — (Q — stability) and (read-side W) — are already
   cited **in the other direction**, by `Lawful.stable`'s and `Lawful.reads`'s docstrings naming
   the section they mechanize, which costs the document nothing. Where that document makes a
   claim and cites nothing, **that is the policy working, not a gap.** Do not re-open it without
   deciding to amend that paragraph first.

   **And the count still does not reproduce — three readings, none of them 172.** HANDOFF and
   `9f1be62` both say "the five deleted documents"; **three** were deleted, in `b163c17`, whose
   own message names them: the audit, the change log and the `src/` discipline. A code-only
   reading against those three gives **273** orphaned citations, `9f1be62`'s table gives 172 gross
   and 90 net, and the item before it said 78. The reading was never pinned, which is the defect
   `9f1be62` was written to fix, recurring inside the commit that fixed it. The ten below were
   therefore chosen by **anchor** — an orphaned theorem whose claim a surviving non-normative
   document already makes in a specific sentence — and not by filling a quota. **A number here is
   worth nothing without its reading; if you need one, compute it and say which reading.**
2. ~~**`src/`'s arity-one check**~~ — **`999b877`.** `EveryOptionTagged` and the runtime both
   refuse a discriminator literal admitting several values. It cost **four deliberate tests**,
   one of them labelled "the feature the refusal must not take with it" and written to prevent
   exactly this; the two that went unstatable are `HOpaque set []`'s shape again. `src/lean.ts`'s
   dedup-by-identity went with them, so `Typed.dunion`'s `hdisj` is answered at the declaration
   rather than in two places.
3. ~~**`admits`' violation list**~~ — **`7b376f9`** and **`c37e5cf`.** `admits(c,v) ↔
   !isError(c.encode(v))` is an **iff** at all thirty-two codecs in `codec.laws.spec.ts`'s table.
   This item said four codecs were loose; the repo's own pinned test said **twenty-three**, and
   had said so since it was written. Eleven gates closed all of them, because twelve were loose
   only through their elements. Every gate runs the predicate `admits` already ran — one test per
   kind, two callers — and `opaque`/`custom` are carved out because `admits` reaches them *by*
   calling `encode`, so consulting it there would not terminate.
4. ~~**Wiring `admits` into `union`'s resolver**~~ — **`ff75c6b`**, and half of it was
   impossible. The write side decides through `admits` (`onlyAdmitting`) and the swap changed no
   test, which is the evidence (3) had to land first. **`identifying` cannot be retired**, and
   not for want of trying: its one consumer is the *declaration-time* pairwise guard, which asks
   whether **any** value can tell two options apart, and `admits` answers a question about a
   value there is none of at import time. Its docstring says so now. The declaration guard was
   also narrowed — `set` separates where `array` and `record` do not, because an empty `Set` is
   admitted by neither and `[]` is admitted by both.

5. ~~**The `AdmA` port**~~ — **rejected on measurement (`a41f874`), and its guard landed
   instead.** This was a recorded question and became a task; the answer is no. `AdmA t a` and
   whether the library's read accepts `a` agree at **861 of 861 checkable pairs** of 864, and
   disagree at none. **The read side validates because it parses data somebody else wrote**;
   the write side trusted its argument's *type*, which is the whole of why wiring gained there
   and gains nothing here. Three pairs are stuck rather than divergent — `AdmA .number`'s `.n`
   row goes through `Double.ofDec`, an axiom with no computation rule, so *both* assertions
   fail, which is how it was told apart from a disagreement. §10 has it, with the instruction:
   **do not re-open as a port without first showing a pair where the two disagree.**

   **The twin landed after all, internal, because a different question was the right one.**
   Declined as *API* first; JH's reading then moved it — *"`admits` should not be a public api in
   the first place. Those and the proposed one are internal utils."* So the **six definition
   readers** left the published surface (`a1effb5`), which is what made the twin expressible:
   `codec.ts` can export freely once `Rotorise.ts` enumerates instead of starring. Two places had
   already written the function — `testing.ts` as `reads`, `lean.ts`'s read-verdict generator
   inlined — so `admitsAttribute` is those two, once. It **asks the codec** and is not a
   def-reader; the read side validates already, and §10 says why the next proposal here should
   not reach for twenty-one rows.

**The bridge is three artifacts now, all generated at gate time and none committed:** the refusal
cross product (599), the declaration-guard verdicts (17), and the read-side differential (861).
`scripts/gate.sh` elaborates all three beside the two committed vector samples, and treats a
*warning* as a failure, machine-written files having no judgement calls to make. Seven checks,
about twenty seconds.

**The `src/` numbers, measured at `a41f874` in
`mcr.microsoft.com/devcontainers/typescript-node:0-20` against the host `node_modules`:**
`tsc --noEmit` clean, `biome ci src` **6**, `vitest run` **876 passed, 9 skipped**. HANDOFF said
biome was at 8 and a session note said 9; it was 7 before this arc and neither number had been
run. **Re-measure; do not quote this paragraph either.**

**Closed this arc, do not re-open:** unifying `κ` with `occV`/`occA` (§4a — the computability
gate passes and the ⊤ encodings are incompatible; the cost shape kills it); collapsing the four
per-base `AdmALit_*_exact` into one parametric lemma (`423c276` — dag −8%, tree +1%, two premises
at every call site); the twin census as a backlog (`cc8477b` — the ranked list is empty);
elaboration heartbeats and transitive dependency count as metrics (§6 — measured, both wrong);
a docstring-coverage *bar* (§10 — 269 of 896 makes it decoration). And from the previous arc:
`select` over `List.attach` (`daa211e`); `adm (.literal .number ls)` not exact (`152ab6b`);
`admA`'s `legacy` `⊤` row (`90794bd`); the value/attribute twin merge (§10); bundling `Lawful`
into `custom` (§4a); keying `(dunion)` by tag (§4a).

---

## Landmines

**Three Claude sessions share this working tree, and there is one index.** A peer's
`git commit -a` commits your staged *and* unstaged edits under its message, and your own commit
then reports "nothing to commit, working tree clean". `2e13324` carries an edit I wrote under
another session's commit message. **Check `git log -1` as well as `git status`.** Do not rewrite
a peer-authored commit to reclaim authorship. For parallel work, use a separate `git worktree`.

**Gate on exit codes, not on printed output.** I shipped two commits claiming all guards pass
over a red tree (`eed1b58`, `e3bd71f`) because I ran them as `…; echo "$g=$?"; done && git
commit` — `echo` always succeeds, so the chain gated on nothing. The gate is
`formal/scripts/gate.sh` now, for the reason that block was easy to run wrong: it lived in the
file you are told to delete once you have read it.

```sh
formal/scripts/gate.sh              # the four guards and the Docker build
formal/scripts/gate.sh --no-build   # guards only — see its header for when that is honest
```

It runs **seven** checks — the four Python guards, `lake build`, then *vector emit* (generating
the four bridge artifacts) and *vector bridge* (elaborating them beside the two committed vector
samples) — prints one line each, and exits nonzero if any failed, so `gate.sh && git commit`
gates on something. Every check runs even after one fails, so one invocation reports the whole
state of the tree rather than its first symptom. (This said "the five checks in the order below"
and listed nothing: the order moved into the script when the paste block did.)

Editing *any* `Calculus/*.lean` can move a `doc_counts` count, because §4c and §5 cite file
lengths — a comments-only edit is not exempt. **And a count can move in a file you did not
edit.** §5's `orth_unreach_lines` sums the *spans* of the unreachable declarations, and a span
runs from the `theorem` line to the last non-blank line before the next declaration — so
re-wrapping one signature onto two lines moves a number the document attributes to
`Orthogonality.lean`. `7fff6e8` moved it 168 → 169 that way. When a count moves and you cannot
see why, recompute the spans against `HEAD` rather than guessing which edit did it.

**`lake env lean` reads the *existing* olean of a dependency.** Edit `Domain.lean`, check
`Combinators.lean`, and the new constructor is unknown until you build.

**Host writes take ~1 s to reach the container mount.** `sleep 2` after editing.

**One `lake build` at a time**, and *your* build rewrites oleans under someone else's
`lake env lean`. Editing a late module and checking it with `lake env lean` writes nothing.

**Python is on the host, not in `rotorise-lean-dev`.** There is no Python in that container at
all — `which python3` there exits non-zero. The Python scripts run from `formal/` on the Mac.

**The TS toolchain is not on PATH and neither is `node`.** Run it in
`mcr.microsoft.com/devcontainers/typescript-node:0-20` mounted on the repo, against the host
`node_modules`: `npx --no-install tsc --noEmit`, `npx --no-install biome ci src`,
`npx --no-install vitest run --reporter=dot`.

**And baseline all three before touching anything, because this file has been wrong about one of
them twice.** It said biome was at 8, a session note said 9, and it was **7** — nobody had run it.
`biome ci` exits non-zero at HEAD, so exit code alone says nothing; read the count. `vitest` exit
0 alone is not proof either — a run that collects nothing exits 0, so require the
`Tests N passed` line. And `biome format --write` on a file that is already dirty produces a
diff nobody asked for mixed into the commit, so format only the files your own change touched.

**Do not touch `CHANGELOG.md` on this branch.** JH writes it at release time from `git log`, so
it carries only what is in `main` — six commits had added 85 lines of `Unreleased` entries and
they were all reverted at his call (*"delete change log changes of this branch and keep only what
is in main. i will fill it when we were ready"*). The commit message **is** the record; an entry
here is a second copy of it that nobody asked for and that goes stale between arcs. If a change
feels like it needs one, that is a sign the commit message is not carrying its weight.

**`tuple` is variadic.** `tuple([x])` passes an array as one element and every reader of
`def.elements[0].def` then sees `undefined`.

**`by_cases` and `by_contra` reach `Classical.em`**; `simp` reaches `Classical.choice` more
often than you expect. Use `cases h : decide P` and `Decidable.byContradiction`.
`Finset.card_pos`, `mem_insert` and `mem_filter` are clean; `Finset.toList` is `Quotient.out`
and is not. Extracting an element from a `Finset` is where it turns — `Finset.card_eq_one` is an
existential, so getting the witness inside a `def` is choice.

**`grep` has three blind spots.** A pattern anchored on a qualified name misses an
anonymous-constructor pattern — changing `Typed.held`'s arity missed a consumer written
`| _, _, _, .held h' _ =>`, and only the build found it. And **a grep piped into `head` is not
a measurement**: a truncated pipe twice produced a false reading here.

And **a declaration pattern anchored at column 0 misses everything inside a `mutual` block**,
because those are indented. `adm`, `admA` and `κ` are all in one, so a census of
`Discharge.lean` read 114 declarations where there are 125, and reported the three functions
the census was *about* as referenced from nowhere — a false negative that reads exactly like
a retirement being cheap. Anchor on `^\s*`, and sanity-check the count against the names you
already know are in the file.

---

## The thing to keep

**A test that compares a generator against what it produced cannot see the generator being
wrong.** The differential bridge — the one artifact checking `src/` against the model — **had not
compiled for a day and ten commits**, and every guard was green. `db444e3` changed
`Term.object`'s arity; the emitter kept the old spelling; `src/lean.spec.ts` compared the
emitter's bytes against files *that emitter generates*, so a stale generator agreed with its own
stale output. Its docstring said "a sample that is not regenerated is a sample that lies"; the
sharper statement is that **a regenerated sample lies just as well, because regeneration is not
verification**. Nothing ran a generated file through Lean — the build is `Calculus/` and the
samples live in `src/`. Ask of any generated artifact: *what would fail if the generator were
wrong?* If the answer is a comparison against the generator's own output, nothing would.

The corollary is `ARCHITECTURE.md` §2's ninth companion. A stratum owed eight; `Body` proved it
owes an **emitter clause** too, and that debt is a row in the table now rather than a sentence in
a commit message, because the eight were what `db444e3` was written against.

**The read side validates because it parses data somebody else wrote; the write side trusted its
argument's type.** That one asymmetry explains the whole `admits` arc. On the write side it made
twenty-three of thirty-two rows loose, made a union report an ambiguity that was never real, and
made wiring the resolver worth doing. On the read side it makes all of that unnecessary — 861 of
861 checkable pairs already agree with the model — so the port was rejected and its guard landed
instead. **Before porting a predicate to the other side of a pair, ask whether that side ever had
the licence the first side abused.**

**An ambiguity a resolver reports may be its own looseness wearing an ambiguity's clothes.**
`codec.uniqueadmission.spec.ts` recorded a union this library builds, decodes from, and cannot
encode into — `union([held(decimal, dateAdapter), string])`, throwing on *every* `Date` — and
left the repair as a choice between refusing the declaration and giving `held` a write-side `κ`,
"both the specification's call". **Neither was needed.** The cause was in the defect's own prose:
with no `κ` the resolver falls back to attempting, and `string.encode(new Date())` succeeded. Gate
`string` and the `held` option answers alone. The option that had no `κ` still has none; what it
no longer has is a rival that admitted everything. A resolver that decides by *trying* inherits
every looseness of everything it tries, and then reports the result as a property of the
declaration — so before costing a repair for an ambiguity, check whether both options really
admit the value or whether one of them merely failed to refuse it.

**Twenty-three loose rows closed with eleven gates, because twelve were loose only through their
elements.** The measurement was the deliverable of `admits`' violation list, and the useful part
was not the total but its *shape*: five ground gates closed seventeen, since a `tuple` took a
`Uint8Array` of the right length only because its positions did, and `attributes`, the four
wrappers, `legacy`, `held`, `lazy` and both unions inherited the same way. Only the six that were
loose in their **own** row needed their own gate. **Measure a container's defect at its leaves
before costing it per container** — and re-measure after each layer, because the second
measurement is what said six and not eighteen.

**A guard that fires on the refactor it exists to encourage is a guard nobody keeps.**
`branches` summed `1 + decision_points` per declaration, so the per-file total counted one per
declaration — and extracting a lemma *raised* it. Found the first time the metric was used in
anger: pulling two cases out of `AdmA_exact` cut its proof term 46× and the ratchet called it a
rise. The per-file total is decision points alone now. Any new metric wants this question asked
of it before it is ratcheted.

**Text measures and term measures are blind to each other, and neither subsumes the other.**
`Adm_kind` is worst-tier on branch density (1.41 a line) and trivial in the kernel (103 nodes) —
its branches live in a `<;>` chain that elaborates to nothing. `encSet_isSome_of` reads calm at
0.38 and is 4845 nodes. `soundness_both` is 122 lines, 0.36 a line, 79 kernel nodes and 2×
sharing: a table, not a tangle, which §5 and §6 claimed in prose and four numbers now agree
with. **Do not shorten it, and do not pick a refactor target from one column.**

**The sharing ratio is the only thing that saw the one real fan, and it is a ratio of two
numbers neither of which is a size.** 2–19× is the band. `AdmA_exact` was at 380×, from three
literal bases with `inL` in a `simp` set, each unfolding a ten-row matcher on every rewrite —
and the proof read calm at 0.58 branches a line over unremarkable source. The fix was §4c's
rule applied to an *inversion*: `restrict_p_isSome`, the twin of an `@[simp]` lemma that had
none, plus row equations for `inL` at the four ungated bases. Family proof term 3.9M tree nodes
to 134k. **When something is slow to check and reads fine, measure the term.**

**Four metrics were tried and are wrong; §6 records them so nobody rebuilds them.** A long
docstring is not a smell — 91 of the 118 declarations whose docstring outruns their code have
three lines or fewer of code, because §9 makes a forced choice most interesting exactly where
the proof is one line. Naive `Expr` size is a sharing measurement in disguise. **Elaboration
heartbeats are not deterministic** — three identical `Meta.check` runs in one process spread
1.2% to 13.7%, run 1 always highest from cold caches. Transitive dependency closure measures
which layer of §1 you are in: its largest values are the two simplest proofs in every other
column.

The lesson all four share, and the previous arc's four as well: **the sentence saying the brief
was wrong is the most valuable thing in any report.** Every brief in this arc was wrong about
something load-bearing, three of them about the repair itself, and in each case the correction
was worth more than the change it arrived with. The previous arc's four results are in the
documents now — §3's `(literal)` premise, the `(dunion)` measurement, §1's cancelling
widenings at §10, and `codec-calculus.md`'s algebra-under-a-label.
