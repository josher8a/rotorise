# Handoff

**Branch `wip/map-types`. `lake build` green and warning-free, `#assert_axioms_all` and
`#lint_calculus` over 21 modules, and all four Python guards — `guard_reach.py`,
`name_drift.py`, `doc_counts.py --check`, `ratchet.py` — exit 0.** Verify with
`formal/scripts/gate.sh`, which runs all five and exits nonzero on any failure — by exit code
and not by eye. `complexity.py`, `complexity.lean`, `twins.py`, `vocab_audit.py` and
`fidelity_audit.py` report and never fail; they are not in the gate.

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

- **`ratchet.py`** — four per-file counts, failing on a *rise*: `unfolding_sites` 332,
  `retirement_marks` 72, `undocumented_public_theorems` 269 of 896, `branches` 3972. Baselines
  in `scripts/ratchets.json`, never in the script, so the guard's source stays still and a
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

**Nothing is queued.** The instruments line is exhausted; every probe it suggested has been run
and the three that did not pay are recorded as rejections rather than as backlog. What remains
is four decisions, and all four are JH's.

1. **Item 2's citations — with JH, unanswered.** 172 declarations are named by a document this
   arc deleted and by no surviving one, in three bins: 12 §2 laws, **10 where a surviving
   document already makes the claim and cites nothing**, 150 plumbing. The proposal is 13
   citations — six non-normative bin (ii) anchors, three of the four normative ones, four of the
   twelve §2 laws, nothing from bin (iii). Reproduce with the five deleted documents against
   `README.md`, `ARCHITECTURE.md` and `docs/codec-calculus.md`; the four alternative readings and
   their counts are in `9f1be62`.
2. **`src/`'s arity-one check — JH's call.** `(dunion)`'s discriminator is arity one in the
   calculus. `EveryOptionTagged` (`src/codec.ts`) refuses only options naming no literal and
   pairs sharing a tag, so `string('A','B')` at a discriminator is legal, and `codec.ts:4415`
   records that as deliberate — *"an option may answer to several tags"*. One type-level check
   plus that comment, which becomes false. Keying `discriminatedUnion` by tag was **declined**.
3. **`admits`' violation list — JH's call.** `admits(c,v) ↔ !isError(c.encode(v))` is false in
   one direction, because `string`/`boolean`/`binary`/`array(string)` do not validate on
   `encode`. Making `encode` use `admits` closes it at the root and is a behaviour change.
4. **Wiring `admits` into `union`'s resolver — JH's call**, and deliberately not done. It
   replaces try-and-see with a decision and retires `identifying` (45 lines, one consumer).
   Depends on (3).

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

It runs the five checks in the order below, prints one line each, and exits nonzero if any
failed, so `gate.sh && git commit` gates on something. Every check runs even after one fails,
so one invocation reports the whole state of the tree rather than its first symptom.

Editing *any* `Calculus/*.lean` can move a `doc_counts` count, because §5 and §8 cite file
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
all — `which python3` there exits non-zero. The six scripts run from `formal/` on the Mac.

**The TS toolchain is not on PATH and neither is `node`.** Run it in a container against the
host `node_modules`; `tsc --noEmit` is clean there, biome is at 8.

**`tuple` is variadic.** `tuple([x])` passes an array as one element and every reader of
`def.elements[0].def` then sees `undefined`.

**`by_cases` and `by_contra` reach `Classical.em`**; `simp` reaches `Classical.choice` more
often than you expect. Use `cases h : decide P` and `Decidable.byContradiction`.
`Finset.card_pos`, `mem_insert` and `mem_filter` are clean; `Finset.toList` is `Quotient.out`
and is not. Extracting an element from a `Finset` is where it turns — `Finset.card_eq_one` is an
existential, so getting the witness inside a `def` is choice.

**`grep` has two blind spots.** A pattern anchored on a qualified name misses an
anonymous-constructor pattern — changing `Typed.held`'s arity missed a consumer written
`| _, _, _, .held h' _ =>`, and only the build found it. And **a grep piped into `head` is not
a measurement**: a truncated pipe twice produced a false reading here.

---

## The thing to keep

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
