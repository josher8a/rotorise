# Handoff

**Branch `wip/map-types`. `lake build` green and warning-free, `#assert_axioms_all` and
`#lint_calculus` over 21 modules, `guard_reach.py` and `name_drift.py` exit 0.**

Delete this file once read — it is a handoff, not a document. The previous one is in
`git show 6b208fc:HANDOFF.md`… it was never committed; read this one and the commit messages.

---

## The one idea, because most of the arc is an instance of it

**A row that asks its codec is exact for free**, and the corollary that keeps paying: *a
description must be kept in agreement with what it describes; a question cannot drift.*

That was the previous arc's finding, at seven rows. This arc found five more instances and
one boundary:

- `nullable` — the excuse said `ownsNull` is a disjunction over both halves of the pair, so a
  row could not account for it. `Codec.ownsNull` is a computable `Bool`; the row asks it.
- `union` — the excuse said a count is anti-monotone, so sharpening breaks soundness. True
  while any *other* row was loose, which was a fact about the state of the table recorded as a
  fact about the row.
- `SetBase.setMember_elemMember` was `@[simp]` with a left-hand side that cannot occur in
  simp-normal form. An attribute is a description of behaviour, and nothing was keeping it
  honest. Batteries' `simpNF` found it in a first-ever lint run.
- `src/`'s `identifying` describes which codecs validate on `encode`, and had **drifted in
  both directions** — too narrow at `number`/`decimal`/`nullValue`, too generous at `array`
  (where `[]` never runs the element check).
- And the boundary: `union`'s (U) is **not a property of an option**. It is a property of a set
  of options at an input the set as a whole resolves. Indices make per-thing properties
  structural; this is not one. That is why the `set`/`literal`/`dunion` moves worked and
  `union` resists.

---

## What landed

**The model is at 21/21 on both sides.** `Adm_exact : ∀ t, ExactV t` and
`AdmA_exact : ∀ t, ExactA t`, no hypothesis, no escape hatch. `Analysable`, `Excuse`, `covers`,
`childrenAnalysable`, `analysable_excused`, `excuse_shapes`, `excuse_witnessed` and their
attribute twins are **deleted** — an excuse with no user is an excuse with no content, and
`Adm_exact` exhaustive over `Term` forces a proof per constructor where the hatch offered a
`false` row. `Adm_sound`/`AdmA_sound` became one-line corollaries, which orphaned 328 lines of
scaffolding, swept.

**`Orth`** (`Orthogonality.lean`, 947 lines) — a decidable syntactic certificate for a fragment
of (U), phases *slot* and *names*, with `Separates` covering *alternatives* as a `Prop` because
`DecidableEq Double` is noncomputable. **Measured against what it replaces it does not pay:**
947 lines against 45 lines of hand proof, 8 of 13 discharges reachable, and none of the hand
proofs deleted. Its value turned out to be elsewhere — see recursion below.

**Confluent admission** (`Continuity.lean`) — `selectF` is first-match plus an obligation, and
`Continuity.lean`'s refutation is specific to **counting**. Its own witness has both options
writing `⟨S,"A"⟩`, so it does not reach the weaker rule. Monotone given the obligation,
continuous, and `docs/codec-calculus.md` §5 records it as a proved alternative **not adopted**,
because order-independence stops being unconditional and that is a real loss for a spec.

**`docs/codec-calculus.md` caught up** — `(set)`'s premise became an index; three `⊤` rows in
the `adm`/`admA` table were not forced and are now `dom(p)`; one parting into `⊤` survives
(`legacy`, read side). The original argument is kept below each correction: it is a good
argument reaching a wrong conclusion, and that is worth reading.

**`#lint_calculus`** — fifteen Batteries environment linters, never run here before, now a build
guard with two sanctioned hits (`qTop`, `occTop`, both `fun _ => true`). `docBlame` is excluded,
not sanctioned; its 90 hits are helper defs and whether the docstring convention reaches them is
JH's call.

**`src/` finally moved** — four commits from a dispatched agent: `decimal('1')` (and `binary`)
emittable, `.set()` propagating with `set(...)`/`literal(...)` gone, `admits` as a reader of
`def` with the half of its law that is true, and `union` refusing two options that store the same
member. Read those four commit messages; they are the record.

---

## Pick up here

1. **`select` over `List.attach`** — queued since `Codec μ`'s spike, described as a standalone
   strict improvement removing the only structural obstruction in the union proofs. Touches
   `Combinators.lean`, deep in the graph, so it needs a clean build window.
2. ~~**`adm (.literal .number ls)` is not exact**~~ — **done**, by the carrier route, at JH's
   call. `GroundKind.number.Carrier` is the gated subtype, `LiteralD` is gone, and the older
   generation's literal row is exact for free because it is now the *same function* as the
   joint row. The witness moved to `literalNRule`, an ungated transcription that is not a
   `Term`. And the premise that made this a fidelity call was misdescribed: §3's rule already
   carries `ℓ ⊆ D` as `ℓᵢ ∈ T`, so the witness shows that premise is load-bearing rather than
   showing a defect in the rule. See ARCHITECTURE §8 and the commit message.
3. **One-line `src/` follow-up, JH's call.** `(dunion)`'s discriminator is arity one in the
   calculus as of this arc. `src/` is not aligned: `EveryOptionTagged` (`src/codec.ts`) refuses
   only options naming no literal and pairs sharing a tag, so `string('A','B')` at a
   discriminator is legal, and `codec.ts:4415` records that as deliberate — *"the whole
   admissible set, not one value: an option may answer to several tags"*. The change is one
   type-level check that the discriminator's literal has exactly one value, plus that comment,
   which becomes false. `discriminatedUnion` also takes a list rather than a tag-keyed table
   (`codec.ts:4394`); keying it was **declined**, so the list stays.
4. **`admits`' violation list** — `admits(c,v) ↔ !isError(c.encode(v))` is false in one
   direction, because `string`/`boolean`/`binary`/`array(string)` do not validate on `encode`.
   Making `encode` use `admits` closes it at the root and is a behaviour change.
5. **Wiring `admits` into `union`'s resolver** — deliberately not done. It replaces try-and-see
   with a decision and retires `identifying` (45 lines, one consumer), and it depends on (3).
6. **The change log's 70 dangling names** (`codec-formalization.md` §4) — a judgement about
   whether a change log carries names of deleted things, not an edit.
7. **`fa9ce05`'s commit message** cites a regex pass as a reachability measurement. Needs a
   rebase; `scripts/unreferenced.lean` is the honest instrument for next time.

---

## Landmines

**`lake env lean` reads the *existing* olean of a dependency.** Edit `Domain.lean`, check
`Combinators.lean`, and the new constructor is an unknown identifier until you build.

**Host writes take ~1 s to reach the container mount.** `sleep 2` after editing, before building.

**One `lake build` at a time**, and note the corollary a parallel session needs: *your* build
rewrites oleans under someone else's `lake env lean`. Editing a late module and checking it with
`lake env lean` writes nothing and is the safe way to work alongside an agent.

**The TS toolchain is not on PATH and neither is `node`.** Run it in a container against the host
`node_modules`; `mcr.microsoft.com/devcontainers/typescript-node:0-20` works, `tsc --noEmit` is
**clean** there (the "one pre-existing aws-sdk error" is a host artefact), biome is at **8**.

**`tuple` is variadic.** `tuple([x])` passes an array as one element and every reader of
`def.elements[0].def` then sees `undefined`. It cost me a false bug report.

**`by_cases` and `by_contra` reach `Classical.em`**; `simp` reaches `Classical.choice` more often
than you expect — `not_forall` and a `decide` over a `Finset` subtype both do it, and one of
those was in a one-line proof I handed an agent. `#assert_axioms_all` is what catches it.

**A `mutual` block's members reference each other in no constant's value.** Different projections
of one induction principle, so reachability analysis reports them as orphans. See
`scripts/unreferenced.lean`.

---

## The thing to keep

**Roughly one reading-derived verdict in three is wrong, and this arc is more evidence, mostly
against me.** Eight documented "impossible"s turned out to be "did not". But the sharper lesson
is the shape of my *own* errors, because they were all the same:

- **F1** — "the library refuses what the calculus permits" for `union(set(string), set(number))`.
  I conflated *legal term* with *resolvable union*. The doc said the write direction cannot be
  resolved, and I read past it.
- **The certificate is bundlable** — I told JH his reasoning defeated my objection. It did not:
  the obligation ranges over `Term` itself, and a mutual inductive's *signature* cannot mention
  the type being defined. A stronger obstruction than the one I first gave.
- **The `⋁` deletion** — promised, retracted twice.
- **"13 hand proofs collapse into one function"** — the whole value case for a 947-line dispatch.
  8 of 13, totalling **45 lines**. I counted declarations and never opened one.
- **"Continuity needs no confluence"** — true of the two-option growth-first case only, and I
  wrote it into a commit message and the normative doc before generalising it.

Every one is a *reading* treated as a measurement. The repo's instruments — `#assert_axioms_all`,
`name_drift.py`, `#lint_calculus`, and now `scripts/unreferenced.lean` — exist because prose does
not typecheck. **Measure the thing you are about to claim, and measure the right dimension:**
count is not size, legal is not resolvable, and a special case is not the general one.

**And the most valuable line in any dispatch report is the one saying the brief was wrong.** It
happened in all three dispatches this arc. Twice the brief was mine.
