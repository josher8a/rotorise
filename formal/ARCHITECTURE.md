# Architecture of the Lean development

Read this once, in full, before changing anything under `Calculus/`. It is not a tour of the
files — `README.md` has the module table, and the files themselves are better at saying what
they contain. This says **why the shape is the shape**, which invariants are load-bearing,
and **where each guard is blind**, because the blind spots are what a contributor actually
trips over.

Where something is already written down, this cites it instead of restating it:

| For | Read |
| --- | --- |
| The rules, normatively (§1–§7) | `docs/codec-calculus.md` |
| What changed and why, historically | `git log` — see §6 |
| Module table, modelling decisions, how to build | `README.md` |

Two standing rules govern this file too: **record why, not what**,
and **a documented verdict is a hypothesis**. Everything below was re-checked against the
sources rather than inherited; where a recorded claim did not survive, the correction is
stated inline.

---

## 1. The layering, and the one thing the build enforces about it

<!-- count:modules -->21<!-- /count --> modules, and the import graph is an almost-linear spine — `Domain` → `Codec` →
{`Combinators`, `Term`} → `Denote` → `Typing` → `Soundness` → the analyses (`Discharge`,
`HeldSet`, `Nesting`, `Equations`) → `Exactness` → `Orthogonality`, with
`Axioms` as the sink — `Malleability` is the one analysis off the spine, importing
`Combinators` alone. `python3 scripts/guard_reach.py --graph` prints it; nothing else is
worth writing down about it, because **the layering is a convenience and only one property
of it is checked.**

That property: `Axioms.lean` runs `#assert_axioms_all`, which walks *the environment*, and
the environment is what `Axioms.lean` imports — a hand-maintained list. A module nothing on
that list reaches is silently unguarded. `scripts/guard_reach.py` fails if any module under
`Calculus/` is outside the transitive closure of the guard's imports.

It exists because the gap was real twice: `Nesting.lean` used `omega` (a known
`Classical.choice` route) outside the guard, and `Vectors.lean` acquired `Classical.choice`
through mathlib's `DecidableEq (Finset α)` — through a `def`, where no proof review would
have found it. Both were caught by someone remembering an import.

**Consequence for a contributor: a new module under `Calculus/` must be reachable from
`Axioms.lean`, or the build fails at the script.** `Axioms.lean` cannot `import Calculus`
instead — the aggregator imports the guard, so that is a cycle, and inverting it would let
`defaultTargets` build the tree with no guard running at all.

Nothing else about the graph is enforced. There is no layering lint; a cycle would be caught
by Lean and a bad-taste upward dependency would not be caught at all.

> `README.md`'s module table predates five of the <!-- count:modules -->21<!-- /count --> modules — `Exactness.lean`,
> `Orthogonality.lean`, `Malleability.lean`, `LiteralArity1.lean`, `Vectors.lean` have no row.
> Each opens with a module docstring that says what it is for; read those.

---

## 2. The stratification, and the pattern a new stratum must follow

`Term`, `Body`, `Field`, `Rest` are four inductives in **one** `mutual` block. The point of
the split is negative and it is the whole reason for it: **no `Term` position accepts a
`Field`.** §4's field policies (`req`/`optional`/`fallback`) are not terms, and making them a
separate sort means a nonsensical term is a type error rather than a rule someone has to
remember to refuse.

`Body` is the newest stratum (`db444e3`) and is the worked example. It bundles §4's object
payload — the declared key set, the field at each key, and the rest policy — into one thing:

```lean
inductive Body where
  | mk (fields : Finset Name) (f : {k // k ∈ fields} → Field) (rest : Rest)
```

Two things follow, and both are the reason to do it again:

- **Every table over terms gets a one-argument `.object` row** that delegates to a `Body`
  companion. Threading three arguments by hand through twenty tables was the only reason those
  three had to agree *by convention* rather than *by type*.
- **`Finset Name` plus a function off the membership subtype** is what makes §4's `Nodup`
  premise disappear. A `List (Name × Field)` admitted two orderings of one object and a
  repeated name; the typing rule carried `Nodup` to make the first harmless and rule out the
  second. Both are now properties of the type. `Field` sits in the function's *codomain*,
  which is strictly positive — the same factoring `Attr.m` and `Value.map` use one level down.

**The pattern, so a fifth stratum is written correctly.** A stratum owes **nine** companions —
seven kinds with the admission row counted on both sides, and the emitter clause the ninth —
and `db444e3`'s own table was the list of the first eight. `Term` and `Body` have all nine;
`Field` has no spec projection (`Body.spec` matches on the field inline) and `Rest` has neither
spec nor tags, because a policy answers to no name and carries no tag. So the two name-reading
projections are owed only by a stratum that holds names; the other **six** rows are owed
unconditionally, which is seven companions with the admission row counted on both sides:

| Companion | For `Body` | Why it is owed |
| --- | --- | --- |
| a depth clause | `Body.depth` | §3's termination measure must see through it (§3 below) |
| a denotation clause | `bodySem` | `denote` must dispatch without a case split at the use site |
| a spec projection | `Body.spec` | `select` counts an object option by its names, not its contents |
| a member/tag projection | `Body.tags` | the union residues read this, not the payload |
| an admission row, per side | `AdmBody`/`AdmABody` | exactness is per-row; a stratum with no row cannot be exact |
| a premise carrier | `ObligationsBody` | semantic side conditions are structural, not global |
| a law exemption | `MPOkBody` | `legacy`'s (MP) exemption propagates through the stratum |
| an emitter clause | the term emitter's object row (`src/lean.ts`) | the vector bridge writes terms in this language; a constructor it cannot spell breaks it |

Miss one of the first eight and the failure is not a build error but a silent `⊤`: the analysis
will still be *sound* and will have stopped saying anything. That asymmetry is the subject of §5.

**The ninth is `db444e3`'s own debt, and it went unpaid for a day with every guard green.**
Making the payload a stratum changed `Term.object` from three arguments to one, and `src/lean.ts`
kept emitting three — so `src/lean.sample.lean` and its `check` twin, the committed output of the
bridge, typechecked against no `Calculus/` for ten commits. **Nothing could have reported it.**
`src/lean.spec.ts` compares the emitter's bytes against those files, and the files are generated
*by that emitter*, so a stale generator agrees with its own stale output; a test that compares a
generator against what it produced cannot see the generator being wrong. And no gate ran a
generated file through Lean: this repository's build is `Calculus/` and the samples live in
`src/`, which the build does not reach. `scripts/gate.sh` now has a check that elaborates
both, which is the only thing that closes it — and the reason a stratum's debt to the emitter is
a row in this table rather than a sentence in a commit message.

`Body`'s projections (`Body.fields`, `Body.at`, `Body.rest`) are written by hand — a `mutual`
block admits no `structure`. Rows needing all three still pattern-match on `.mk`, which keeps
the equation compiler's iota reductions available.

### Where a side condition goes, and why there are three places

The first thing to settle when adding a rule, and `Typing.lean`'s module header states it —
`Typed` keeps only the "*syntactic and fuel-free*" premises:

| A premise that is… | goes in | consumed by |
| --- | --- | --- |
| decidable from the term | `Typed` (`Typing.lean`) — `(union)`'s is `hD : DIncomp Ts` | the judgement itself |
| about what a codec *does* — `e`, `p`, an iso, a resolution | `Obligations` (`Soundness.lean`) — `UAtAct opts` (reached from the canonical form by `uAtAct_of_uAtCan`), `IsoCancels`, `ReadsCoherently` | both soundness theorems |
| §2's `(MP)`, which `legacy` is exempt from | `MPOk` (`Soundness.lean`) — `.legacy _ _ => False`, structural elsewhere | `soundness` alone |

`MPOk` is not a rule premise at all: it is a predicate on the *term* saying the derivation is
legacy-free, and it is the single hypothesis separating `soundness_core` (`LawfulCore` — (R),
(C), (W)) from `soundness` (`Lawful`, adding (MP)). Choosing wrong is not a build error: a
semantic premise in `Typed` makes the judgement undecidable, a syntactic one in `Obligations`
becomes a burden every caller carries. All three recur structurally, which is what the
companion table's last two rows owe. (That header carried two stale spots of exactly this
kind, invisible to the guards because no name was dangling: the semantic premises were called
"fuel-indexed" where `Obligations` says "**Structural, and no longer fuel-indexed**", and
~~literalS~~/~~literalN~~ were named as live constructors though `GroundKind` had retired them.
Both are **corrected inline** as of `0aec076`, along with two more the same pass found — "set
member" in the premise list and `boolean`/`binary`/`null` described as spelled `refine`. Kept
here as the worked example, because four defects in one header is the strongest evidence in
the repo that prose does not typecheck.)
---

## 3. Termination: why there is a hand-rolled depth at all

`Term.depth` exists for one reason, and it is not aesthetic. `Typed` is a `Prop`-valued mutual
family with no `.brecOn`, so proofs cannot recurse on the derivation and must recurse on the
term instead — and **`sizeOf` cannot serve, because `Term.object`'s field table is a function
and `sizeOf` is blind to functions (`sizeOf f = 0`).** `Term.depth` is the measure that sees
through it: `attach.sup` over the key set where a list would fold, exactly the shape
`Value.depth` in `Opaque.lean` has always used.

What matters is that it is **derived from the term**, so it appears in no statement, no
`Obligations`, and no rule. That is the whole difference between it and the `fuel` parameter it
replaced.

`term_depth_wf` is the shared `decreasing_by` tactic. **<!-- count:term_depth_wf_users -->Four<!-- /count -->** declarations use it:
`soundness_both`, `typed_TSub` and `carrier_denote` in `Soundness.lean`, and `typed_T_eq` in
`HeldSet.lean` — which is not where it belongs by shape. It is `typed_TSub`'s mirror and wants
to sit beside it; its `opaque` case is `opaq_T_identity`, and that module imports
`Soundness.lean`. Its four list and table helpers did stay beside their converses.

Their goal sets differ, so some alternatives in the block are dead at each site — that is what
`unreachableTactic` reports there, and it is why the option is disabled at those declarations
rather than the block being specialised per site.

**Its docstring said *five* until `7a91de8`**, naming `Adm_sound` and `AdmA_sound`. Those do not
recurse: `Adm_exact`/`AdmA_exact` are structural mutual recursions with no `termination_by`, and
the two `_sound` results are one-line corollaries. The claim was true before the exactness
rewrite and nothing was keeping it honest — see §6 on why `scripts/name_drift.py` could not
catch it.

Anything new recursing on a term takes `term_depth_wf`, and if it needs an inequality the block
does not offer, the inequality goes in `Term.lean` beside `Term.depth_lt_object_req` and
friends — not inline.

---

## 4. The four recurring design moves

These are the architecture, more than the module list is.

### 4a. A premise becomes an index

Repeatedly, a typing-rule side condition turned out to be expressible in the *type* of the
constructor, at which point violating it stops being possible rather than being refused.

- **`SetBase`.** §3 `(set)`'s premise was `⊢ c : T ⇝ μ` with `setMember μ = some μS`, and
  `setMember` is partial — so the constructor accepted element terms the rule then refused
  (`set(union(string, boolean))` was the standing witness). `SetBase` is the four bases that
  survive the premise; `SetBase.member` is now a total function of the index, and the refusal
  is a type error.
- **`GroundKind`.** Three literal constructors — arity-one, ~~literalS~~, ~~literalN~~ — became
  `literal (k : GroundKind) (ls : NEFinset k.Carrier)`. The index makes the carrier concrete,
  hence membership decidable; `NEFinset` makes nonemptiness, pairwise distinctness *and*
  homogeneity the type's rather than three premises. `GroundKind.Carrier` is `@[reducible]`
  deliberately, so `Carrier .string` elaborates as `String` and resolves through ordinary
  instances — an indexed `DecidableEq` instance would work and would be *noncomputable*,
  which then spreads to every `def` naming a literal.
- **`object`'s field table** — `Finset Name` plus a function off the subtype, retiring `Nodup`
  (§2).
- **`Body`** — not an index but the same instinct: bundle so that agreement is by type.

**The criterion, stated honestly.** The spine I was handed said an index is available "exactly
when the separator is a function of the input into a finite key set". That is right for
`SetBase` and `GroundKind` and does not describe the other two — `Nodup` is not a function into
a key set, and `Body` is not an index at all. What the four cases actually share is:

> A premise becomes structural when its satisfying set is **finitely enumerable at declaration
> time** (an index), or when it is a property of **one argument** expressible in that argument's
> own type (a subtype, a `Finset`, a quotient carrier). It does **not** when the premise relates
> one argument to *other* arguments' behaviour at a shared input.

That last clause is the boundary, and `union`'s (U) is on the wrong side of it: (U) is not a
property of an option, it is a property of a *set* of options at an input the set as a whole
resolves. Indices make per-thing properties structural; this is not one, which is why the
`set`/`literal`/`object` moves worked and `union` resists. Do not spend another arc looking for
a `union` index.

**And the case where the criterion cuts a premise in half: `(dunion)`'s tags.** The rule carried
two premises, tag nonemptiness and pairwise tag disjointness. Arity one at the discriminator (JH's
call) sharpens the first and leaves the second exactly where it was, and the criterion says why:
arity is a property of **one** option against its own field, so it is a premise — and could in
principle be a carrier; distinctness relates one option to *others* at a shared key, which is the
clause on the wrong side of the boundary, the same side as `union`'s (U). Two options with one tag
stays a premise's business.

The structural version was probed and declined, and the *shape* of the failure is worth having:
keying the union by tag and injecting the discriminator would have made all of it structural, but
`{b : Body // d ∉ b.fields}` cannot be written — `Body.fields` is defined after the mutual block,
so it does not exist where the constructor is declared. The exclusion *is* expressible if the
variant's three components are inlined instead of taking a `Body` (`{s : Finset Name // d ∉ s}`
needs only `Finset` and `d`, both in scope), and **that is rejected on the same criterion in the
same direction as the `custom` bundling below**: it re-threads the three components `Body` exists
to bundle, at one constructor, and every table over terms grows a three-argument row — to buy one
decidable premise. §2's rule about a new stratum costing all nine companions is the same
observation from the other end.

**One move that passes the criterion and still does not pay: bundling `Lawful` into `custom`.**
`Obligations (.custom ce cp)` is `Lawful ⟨dom(ce), none, ce, cp⟩` and `ce`/`cp` never travel
apart, so the law is a property of one argument-group and the criterion admits it. It also
elaborates — a scratch mutual block carrying
`Lawful { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp }` in a `Term`-shaped
inductive compiles with no positivity complaint, proof irrelevance makes two laws on the same
pair `rfl`-equal, and table rows still match `.custom ce _ _`. **It was measured and dropped
anyway.** The bundle cannot take a whole `Codec`: `Carrier.domE` is not derivable from `Lawful`,
so `T` must stay `dom(ce)` or a `Carrier` field must ride along too, and `μSyn`/`denote` both
fix `μ := none`. What it buys is the `Obligations` row (2 lines) joining the `True` list and one
3-line accessor — **five lines, against ~33 pattern and statement sites in 8 files**. Only one of
the four `Soundness` custom cases actually shrinks; `carrier_denote`'s still builds `Carrier` by
hand. And it would strip the arbitrary pair out of the `custom` rows, whose content *is* the
arbitrariness: not a bound on the pair but the pair itself. Last, it is the one instance of this move that
crosses a stated decision rather than realizing one: `Term.lean:11` says `custom` "carries its
pair as data; its *laws* are premises of the typing rule (§3), exactly as in the doc", and
`Typing.lean`'s header puts the *syntactic* premises in `Typed` and the *semantic* ones —
naming `(custom)`'s laws — in `Obligations`, "stated where they can mention the denotation".
`(held)`'s premise-to-index move (`c66d493`) was the syntactic kind and landed; this is the
semantic kind. **The criterion is necessary, not sufficient — measure the site count too.**

**Unifying `κ` with `occV`/`occA` — probed and rejected, and the cost *shape* is the reason.**
`Kind` is a coarsening of `Slot` by design: `Value.kind` and `Value.slot` are both functions of
the constructor, and the first collapses `strSet`/`numSet`/`binSet` to `.set`. So `occV` really
is `κ`'s question at a finer grain, and a Slot-granular `κ` stays computable — `Slot` never
inspects a payload, where `adm`'s noncomputability comes from comparing `Double`s inside the
literal row. The gate passes and the merge still does not pay. The two tables have **no code
contact**: `κ` is 32 code lines across `Discharge`, `Exactness` and `Refutations`, `occV`/`occA`
and their list companions are 85 references entirely inside `Orthogonality.lean`, and `κ`
appears in that file only in prose. And their ⊤ encodings are incompatible where it is
load-bearing — `κ` is `Option (List Kind)` with `none` as *no information*, consumed by six
`κ t = some ks` hypotheses and by `Adm_kind` killing the `held`/`custom`/`opaq` rows with
`nomatch`, against a total predicate whose ⊤ is `occTop`, which cannot distinguish "occupies
everything" from "unknown" and is one of §6's two sanctioned lint hits for exactly that reason.
So a merge is not widening a codomain, it is choosing one of two ⊤ encodings and rewriting the
other's consumers — pushing the coarse/fine distinction into three files to shrink one. What
killed it is the shape of that cost, not its size.

### 4b. A row asks its codec instead of describing it

A row can either *describe* the set it stands for or **call the codec and ask**. The pattern is
this section's subject, and the table below is every row that converted. Four of the rows named
in it were rows of the per-aspect tables that `Discharge.lean` carried; those tables are gone,
and the rows that survive are `Adm`'s and `AdmA`'s. The pattern is what survives them, and it
is the reason the exact generation could be written at all. A row can either *describe* the set or *call the codec and ask*. `custom`
always asked (`(cp a).isSome`, because `p := cp`). Over two arcs **seven** more converted —
`admA .legacy` is the newest and the last of that shape — and one row below,
`admALit .decimal`, was written that way from the start:

| Row | What it asks | The excuse it retired |
| --- | --- | --- |
| `opaq` | `((opaqCodecω lossy).p a).isSome` | "`opaque` needs a rule of its own" |
| `admA .number` | `(numberCodec.p a).isSome` | "`Double.ofDec` is an axiom, so no syntactic set bounds it" |
| `admALit .number` | `((literalCodec .number ls).p a).isSome` | the same, at a literal |
| `admALit .decimal` | `((literalCodec .decimal ls).p a).isSome` | none — a new row (`5b6a0c1`), and it could be spelled out; asking keeps *one* definition |
| `refine` (read side) | `refineReads t q a` | "`q` tests the value a read produces" |
| `nullable` | `Codec.ownsNull` | "`ownsNull` is a disjunction over both halves of the pair" |
| `union` | the count, given the options' exactness | "a count is anti-monotone" — true of the *table*, recorded as a fact about the row |
| `AdmA .legacy` | `AdmA t a \|\| (r a).isSome` — the subterm's row, or `r` | "`extendRead` widens `p` past the subterm's admissible set, which is the direction the read row bounds" |

**The last row is the odd one and the difference matters.** It does not ask its codec; it names
both of `r`'s and the subterm's channels and takes the union, keeping the subterm's
*over-approximation* rather than reaching past it. Asking was probed — the row
`((denote (.legacy t r)).p a).isSome` is exact and compiles at a one-line cost — and **refused**,
because it sees through `admA (.object _) = ⊤`, which §5 records as load-bearing slack rather
than looseness. Two objects cannot be separated by a disjointness test on the read-side row of
the retired table (both were `⊤`); wrapped in a `legacy` they could be, while `select` still attempts both options, which is
`not_uAtCan_of_sepJ`'s failure one wrapper out. So this row is as sharp as it can be *without* becoming unsound, and
the excuse it retired was still a correct observation reaching a wrong conclusion: what
`extendRead` widens *by* is `r`, data the term carries. `Exactness.lean`'s "why `legacy` was in
the wrong family" reached this first, for the joint predicate.

Every excuse in that column was a correct observation reaching a wrong conclusion, and the
pattern is identical: *no syntactic set names it* is a reason to stop being syntactic, not a
reason to give up. `denote (.literal .number ls)` **is** `literalCodec .number ls` by `rfl`, so
the row that asks is `dom(p)` on the nose.

**The corollary is the load-bearing part, and it generalises past this repo:** a description
must be kept in agreement with what it describes; a question cannot drift. When you are about
to add a row, prefer asking. The price is only that the row becomes `noncomputable` when the
codec is, which costs nothing here — `Double`'s equality is a field of an axiomatized interface
already.

### 4c. One codec, stated once for both sides of the pair

`Combinators.lean` is <!-- count:combinators_lines -->4147<!-- /count --> lines of the tree's
<!-- count:tree_lines -->16522<!-- /count -->, and this is its organizing idea; without it
the file reads as the inventory `README.md` already has. A constructor is a **prism** —
`Ctor α β`, with `into`/`out` and the laws `out_into` (matching what was built returns it) and
`into_out` (anything that matches was built) — and those two *are* §2's (R) and (C) at a
constructor, so the prism half of every lawfulness proof is discharged once, here.

Thirteen prisms: six value-side (`strV`, `boolV`, `binV`, `nullV`, `arrV`, `mapV`), seven
attribute-side (`sC`, `nC`, `bC`, `boolA`, `nullA`, `lA`, `mA`). The inventory is **partial on
both sides on purpose** — the gaps are the constructions that are not one payload between one
pair: `.num`, where §1's numeral gate stops `out` being onto the image, and the three wire sets.
Two shapes sit over them, and the second is the load-bearing one:

- `pointCodec V A μ₀` — the degenerate case, one payload type on both sides; `string`,
  `boolean`, `binary` and `null` share **one** lawfulness proof through it
  (`lawful_pointCodec`, via `Lawful.congr`).
- `carriedCodec (V : Ctor γ Value) (A : Ctor δ Attr)` — a payload *pair* between two prisms,
  the shape underneath every product (`entrywise`, hence `arrayCodec`/`recordCodec`;
  `tupleCodec`; `objectCodec`). **The model states a codec once for both sides**, which is why
  §10's twin question is askable at all: the doubling is in the analyses, not the algebra. Its
  two inversions, `carried_e` and `carried_p`, are what every product's proof goes through.
- `set` is the one deliberate non-instance: its attribute side is a choice among three wire
  constructors rather than one prism (`setCodec`, `Combinators.lean`), so its inversion names all
  three families (`setCodec_p_eq`).

**The read side of an inversion is not optional, and its absence cost a 683× fan.**
`restrict_e_isSome` was `@[simp]` and there was no `restrict_p_isSome`, so every literal row on
the *read* side unfolded `Codec.restrict` and `inL` by hand instead of rewriting. Unfolding
`inL` means unfolding `inL.match_1`, the matcher Lean derives for the whole ten-row table, and
paying for all ten rows at every rewrite — which is what `fanOf` found behind `AdmA_exact`'s
duplication (§6). Adding the missing twin, plus `@[simp]` row equations for `inL` at the four
ungated bases, took the four per-base exactness lemmas from 683–797× sharing to 11–39× and
their combined proof term from 3.9M tree nodes to 134k. **§4c's rule is that a codec is stated
once for both sides of the pair; this is that rule applied to an inversion rather than to a
construction, and the cost of the exception was invisible until something measured the term.**
Collapsing the four into one parametric lemma over `GroundKind` was probed and does not pay:
8% off the DAG, 1% on the tree, two `k ≠ …` premises at every call site, and it puts
`NEFinset k.Carrier` back in a statement — the expression whose re-derivation started this.

### 4d. The guards exist because prose does not typecheck

Every instrument in §6 was built after a description drifted from what it described: an axiom
claim in prose (`#assert_axioms_all`), a `@[simp]` attribute asserting a behaviour that had
stopped being true (`#lint_calculus`), a citation of a deleted name (`scripts/name_drift.py`), a
regex passed off as a reachability measurement (`scripts/unreferenced.lean`), a grep passed off
as a refactor estimate (`scripts/blast_radius.lean`). None of them was added speculatively.

---

## 5. Generations of analysis: two that stay, one that does not pay

`Discharge.lean` used to hold four per-aspect approximations — a kind table, a
decides-its-own-membership table, and one admissible-set table per side — with the separation
predicates ~~SepV~~ and ~~SepA~~ running on them, each a **two-disjunct** disjunction (labels
disjoint, *or* admissible sets disjoint). The predicates went at `f5fc4a6` and the four tables
went with the pass that retired them from the model. The fifth aspect, `μSyn`, is
`Denote.lean`'s, because `denote` needs the member index itself, and it stays.

Every discharger in this section is one appeal to `uniqueAdmission_of_disjoint`
(`Combinators.lean`), which takes two families of allowed values, one per side, and asks only
that each be pairwise disjoint. Kinds, members, tags and admissible sets are *ways of building*
those families rather than four conditions.

`Exactness.lean` holds the joint predicate `Adm`/`AdmA`, exact at **all twenty-one**
constructors: `Adm_exact : ∀ t, ExactV t` and `AdmA_exact : ∀ t, ExactA t`, no hypothesis, no
escape hatch. Its separation predicate `SepJV` is one clause — `∀ v, Adm x v = true → Adm y v =
false` — because the joint predicate absorbs what `κ` used to carry. (`SepJA` keeps the member
disjunct: `AdmA` does not bound `μSyn`.)

The obvious cleanup is to retire the older generation. **It is refused, by theorem** —
`not_uAtCan_of_sepJ` (`0467587`). The reason is worth stating precisely, because it is
counter-intuitive:

- `select` counts an `object` option by `keysOk` — **which names a map carries, never what they
  hold.**
- So at an object, `Adm` is *not* an over-approximation of `OptionSem.admitV`. It is strictly
  **tighter**, and disjointness of a tighter predicate does not imply disjointness of admission.
- Therefore **`adm (.object _) = ⊤` is load-bearing, not slack.** It is exactly the
  over-approximation that turns `adm`-disjointness into admission-disjointness. Two objects can
  never be separated by a per-aspect test (both `κ`s are `[map]`, both `adm`s are `⊤`, so neither
  disjunct is available) — and that is the point.
- Restate the discharger on `SepJV` and the pair *does* separate, while `select` still attempts
  both options, so (U) genuinely fails. **The premise gets stronger and the theorem becomes
  false.** The witness is two objects with the same names and different field terms
  (`objReqStr`, `objReqNum`), both derivable, both closed, both lawful — so no other premise is
  what declines them.

**The boundary on the value side, and there it is sharp:** the `object` row is the whole of
*that* obstruction. `admitV_Adm_nonObject` and `admitA_AdmA_nonObject` are the containments the
discharger needs, and they hold from exactness alone for every term whose `specOf` is `none` —
which is every term but an `object`.

**The read side carries a second obstruction, independent of the first, and this section used to
claim the `object` row was the only one.** `SepJA` keeps its member disjunct because `AdmA` does
not bound `μSyn`, and `sepJA_needs_member` is the witness: `legacy` over `string` with a read
channel firing at `N` stores `S` while the channel reads an `.n`, widening `p` past the member
the term claims, and `decimal` admits that same attribute. The pair is separated by `μSyn` and
not by `AdmA`. So a discharger that repaired the `object` row would still be missing something
the exact rows do not carry, and the two obstructions sit at different constructors — neither
subsumes the other, and a migration has to answer both.

**And the repair the `object` row invites — ask what the resolver consults, not what the row
says — is already made, in `Orthogonality.lean` rather than here.** `OrthSV` and `OrthSA` are
occupancy conjoined with `admitOptV`/`admitOptA`, and `admitOptV_eq` is the identification of
that second conjunct with option admission itself, so `uAtCan_of_separates` is already the
discharger stated on what `select` actually decides by. Restating it on option admission
*alone*, dropping the occupancy conjunct, is measurably weaker rather than new: it is
`uAtCan_of_separates` with one conjunct deleted from each family and factors back through it in
one line; it loses `sepJA_needs_member`'s pair on the read side, exactly as `SepJA` predicts;
and at an `object` it reduces to `keysOk` disjointness, which `OrthM`'s `reqNotDeclared`
disjunct already delivers through `orthSV_disjoint`. Kernel-checked, not argued — the four
results and the negative are in this paragraph's commit. **The move that looks open here was
made in the next file, and what is left to take from it is a conjunct.**

**And the per-aspect separation layer is gone, which is what the measurement was for.**
`scripts/blast_radius.lean` rooted on the four definitions that layer was built from partitions
as 28 old-only, 0 both, and every dependent inside `Discharge.lean` or `Refutations.lean` —
nothing in `Soundness`, `Denote`, or `Exactness`'s positive results, and nothing in
`Orthogonality`. Those 28 plus their four roots were deleted: the two separation predicates and
their footprint definitions, the discharger stated on them and its kind/member half, the hand
discharges phrased in that vocabulary, the eight refutations of those separations, and the two
bridges into the joint predicate. JH's call.

Nothing was lost that anything else can state. What the layer proved by hand in phases *slot*
and *alternatives*, `Orthogonality.lean` reaches by `decide`, and its by-phase table now lists
what only exists by hand rather than what is duplicated. The discharges no phase reaches —
an arbitrary `q` inside a `refine`, and `uAtAct_array_literals` where `UAtCan` is outright
false — were never phrased in the retired vocabulary and stay where they were. **The four
tables are gone**, with the containments that related them to
the exact generation. §5 stopped specifying them, and a transcription of an analysis nothing
states and nothing consumes is a description with nothing keeping it honest.

Two citations the walk overturned on the way, both the shape its own header warns about. The
combined discharger appeared in `Exactness.lean` five times and its kind/member half in
`Soundness.lean` once, and **every one of those was prose or a docstring** — no proof outside
`Discharge.lean` used either, so a grep for them was counting sentences.

**Three things the walk got right and one it got wrong.** It costs a *declaration*, never a
change to a row's body: measured on the `admA .legacy` sharpening (§4b), the partition was
identical before and after, name for name, because the walk measures dependence on a **name**.
It reported no positive result in `Soundness` or `Exactness` naming the retired tables in a
statement, and the deletion bore that out. And where it did report a dependent, the dependent
was real.

What it got wrong is that its own root list is a declaration too. The list named two
declarations that `f5fc4a6` had deleted and omitted four that it had not, which understated
the older generation by ten. Worse, `name_drift.py` reads `scripts/*.lean`: the two dead
entries were *clearing* every prose citation of those two names across the tree, so the guard
that exists to catch dangling names was answering with a dangling name of its own. Correcting
the list surfaced 21 citations at once. **An instrument's inputs go stale exactly as prose
does, and nothing was checking these.** The file now says so where the lists are, and the
lists are an example question rather than a standing one: the two-generation question they
were written for is answered and gone.

### And a third machine, `Orth`, which does not pay — measured

`Orthogonality.lean` is the fourth-largest file at <!-- count:orth_file_lines -->1070<!-- /count --> lines — `Soundness.lean` is 1033 —: a decidable certificate for a
fragment of (U), over-approximating each term's occupancy per side (`occV`/`occA`) and
certifying a pair whose occupancies are disjoint, `by decide`. **Measured against what it
replaces it does not pay**, and its own by-phase table is the measurement — the <!-- count:orth_total_theorems -->10<!-- /count --> hand
discharges it names, eight as rows and two in the prose beneath them, out of a
<!-- count:sep_family -->13<!-- /count -->-theorem `sep*`/`uAtCan_*`/`uAtAct_*` family:

| | theorems | lines of proof |
| --- | --- | --- |
| reachable by `Orth` itself — phase *slot* | <!-- count:orth_slot_theorems -->0<!-- /count --> | <!-- count:orth_slot_lines -->0<!-- /count --> |
| reachable only through `Separates`, the `Prop` interface — phase *alternatives*, where `DecidableEq Double` makes a `Bool` test noncomputable | <!-- count:orth_alt_theorems -->1<!-- /count --> | <!-- count:orth_alt_lines -->25<!-- /count --> |
| unreachable on principle — an arbitrary `q` or `f`, a different constructor, `SepJA`'s member disjunct, or `UAtCan` itself failing (`uAtAct_array_literals`) | <!-- count:orth_unreach_theorems -->9<!-- /count --> | <!-- count:orth_unreach_lines -->145<!-- /count --> |

*This table counted the hand proofs against what `Orth` reaches, and the layer it was
counting is gone.* Every theorem it found **reachable** was phrased in the retired per-aspect
vocabulary and was deleted with it, `Orth` being what certifies those pairs now — which is why
the reachable total is <!-- count:orth_reachable_lines -->25<!-- /count --> lines rather than the
145 measured before the deletion. What is left in the unreachable column is the answer the
table was built to produce: the discharges that exist by hand because no phase of the
classifier can reach them, and `uAtAct_array_literals`, which holds where `UAtCan` is outright
false and so has nothing to certify.

When this was written **nothing had been deleted**, and the sentence was the finding: 983
lines stood *beside* the <!-- count:orth_reachable_lines -->25<!-- /count --> they could
replace. Two passes have deleted since, and neither deleted for this reason — the per-aspect
layer went because nothing consumed it, and the four tables went because §5 stopped stating
them. `Orth` still does not pay for itself as a replacement. It stays anyway, because its
value moved — **twice**, and the second is the one that pays.

**`Orth` is the specification of `src/`'s only declaration-time guard, and now a checked one.**
`src/`'s `union` refuses a pair of options no *value* can choose between — `separable`, which reads
`identifies` and the two occupancies beside it — which is the ∀-value question
`Orth` answers by `decide`. The bridge is `src/lean.ts`'s `Separation`: one theorem per pair
`src/` refuses, asserting `Orth x y = false`, generated and elaborated by `scripts/gate.sh`.

Measured over the emittable pairs of the vector corpus — 351 of them — the two agree everywhere
they can both speak: **268** where `Orth` certifies and `src/` accepts, **17** where both decline,
and **0** where `src/` refuses a pair the model certifies. That last number is the law, and it is
the only direction the bridge runs: `Orth` is *sufficient* and not necessary, so the remaining
**66** — where `src/` accepts and `Orth` declines — are not disagreements. Every one lands in a
documented exemption: a literal, which identifies its own values; an object option, chosen by
names; or an option whose kind is unknown (`opaque`, `lazy`, an adapter). Asserting the converse
would produce 66 false findings.

**And the law caught a real over-refusal before it was found another way.**
`Orth (.set .string) (.set .number)` is `true` — the model *proves* those two separable, because
their occupancies are `strSet`/`numSet` and `SS`/`NS`, disjoint on both sides. `src/` refused that
declaration until `ff75c6b`, on the ground that "neither checks what it is given", which stopped
being true when its rows started validating. The pair is not in the corpus (a numeric wire set is
`NEFinset Double`, so no vector can name one) — so it is written out by hand in §5's own bridge
notes rather than generated, which is the shape of every gap this classifier has: decidable, and
bounded by what has closed terms. The classifier framing did not pay; but confluent admission —
the weaker rule proved monotone and continuous and **not adopted** (§7) — needs its obligation
to be an *invariant of the unrolling* (`string_decimal_not_confluent`), which is vacuous exactly
where the options are pairwise disjoint. So a syntactic disjointness test is what would license
recursion under `union`, and `Orth` is that test — delete it and that is the question you
delete.

---

## 6. The instruments, and what each is blind to

The blind spot is the part that matters; the check is the part you can read off the script.

**`#assert_axioms_all`** (`Axioms.lean`) — the advertised base is
`[propext, Quot.sound, Calculus.Double, Calculus.numericHost]`, four names where there were
seven, because the `Double` facts now project out of one `NumericHost` interface rather than
being five independent assertions — `Double.roundtrip` is the one every numeric row leans on. It is a *build error*, not an assertion in prose; that is the
whole design. Two blind spots:
- It walks **imported** modules only — hence `scripts/guard_reach.py` (§1).
- Its filter is `ci.isTheorem`, so **a `def` that acquires an axiom is not checked at all.**
  That is exactly how the `Vectors.lean` defect entered. Run `#print axioms` on definitions, not
  only on theorems.

**`#lint_calculus`** (`Axioms.lean`) — Batteries' fifteen environment linters over the
`Calculus` namespace, which this development had **never run**. Two sanctioned hits, named
individually in `sanctionedLintHits`: `qTop` and `occTop`, both `fun _ => true`, where the unused
argument *is* the content. `docBlame` is **excluded, not sanctioned** — its 90 hits are helper
defs and whether the docstring convention reaches them is a judgement, not a defect; excluding
it is visible in `unrunLinters`, sanctioning 90 hits would not be. The first run over 1674
declarations found one substantive defect, invisible by reading: `SetBase.setMember_elemMember`
was `@[simp]` with a left-hand side that cannot occur in simp-normal form.

**`scripts/guard_reach.py`** — reachability of every module from the guard. Blind spot: it is
*textual and necessary-only*. It says the declarations are in the environment the guard walks;
it says nothing about whether the elaborator is correct, whether `sanctionedAxioms` is the base
the documents claim, or whether the walk's filters let something through.

**`scripts/name_drift.py`** — every backticked Lean-looking name in the current-state documents
must occur somewhere in `Calculus/` — where *Lean-looking* means it carries a `_` or a `.`, **or
is a single word that is not one of four shapes the script skips** (`83d61df`; the four and the
reason for each are in `single_word_checkable`), so `Adm` and `Orth` are checked and a filename
or a naming pattern is not — with an `EXPECTED` table
carrying a reason per deliberate
exception (and failing if an entry there stops being cited, so the table cannot rot quietly).
**The docstring check was partly vacuous, and the fix needed a convention before it could
exist.** `occurring()` built its source set from raw file text, comments included, so a name
appearing *only* in a docstring was present in its own evidence and cleared itself. Adding
`Calculus/*.lean` to `CURRENT` (`6a90359`) therefore proved less than that commit's message
claimed: "none of the 763 dangles today" was established by a check that could not see the case
it was added for. Demonstrated: `literalNRule_holds_what_it_cannot_write` had been renamed,
three docstrings and this file still cited the old name, and the guard passed clean because
those citations were their own evidence. **And deleting the docstring archaeology is what
finally exposed one** — removing the prose that cited the old name removed the only thing
clearing it, so the next run went red, the circularity resolving itself in the one direction
that is useful.

`occurring()` now strips comments and docstrings (45.1% of `Calculus/` by character), so a
citation has to be answered by code. **The reason that took a convention change rather than an
exception list is the finding, and it is not the one the earlier note here predicted.** The
prediction was ~20 mathlib and Lean names, `Classical.choice` above all. Measured, the
mechanical classes were 99 of 169 hits and cost four *kinds* of entry rather than a longer list
of one kind — the language by root namespace, `src/`'s names at §8's boundary, the
specification's own notation, and per-document one-offs. What was not predicted is the other 60:
**docstrings that name a retired declaration on purpose, because §9 tells them to.** "Was
~~denoteωF~~", "~~encPair~~/~~decPair~~ are gone with the traversal",
"~~record_e_keeps_duplicate_keys~~ became unstatable when `M`'s keys became a `Finset`" — a
docstring records what the forced choice cost, and naming the thing that lost is how it does
that. Against a code-only source set those are indistinguishable from real drift: both are a
backticked token absent from code, and the difference is the *tense of the sentence*.

So §9 gained the marker — a retired name is written `~~oldName~~` and the guard reads only
unmarked citations — and the judgement sits with the person writing the sentence, who knows
whether the thing is dead. The marks are checked in the other direction too: `~~X~~` where `X`
is still in the sources is a **false retirement** and fails, so they cannot rot into decoration.
The alternative shapes were measured and are worse: declarations-only rejects every mathlib
lemma a proof actually appeals to (302 hits), and a per-name `EXPECTED` entry for each of the 60
would grow the table from 6 entries to ~85, roughly 60 of them the same sentence, taxing the
convention that produced them. **After the split, 18 stale pointers were left** — including one
that was a content defect rather than a name: `Discharge.lean` called `number` "a `refine` over
an ungated base", where `Combinators.lean` establishes under its own heading that there is no
ungated numeric base, `Attr.n` carrying `Numeral.WF`.

**Blind spot, stated in `7a91de8`: a count is not a name.** It cannot see "five theorems share
`term_depth_wf`" being false while all five names exist. It also clears a dotted name
component-wise, so a dotted citation passes whenever both halves occur anywhere.
**This document is in its `CURRENT` list.**

**And a second blind spot in its own tables: an entry fails when it stops being *cited* and
cannot fail when its *reason* goes stale.** `HOST`'s entry for the admission reader read "§10's
open question about wiring it into `union`'s resolver" for as long as that question was open and
for a while
after `ff75c6b` closed it — cited, so green, and describing a decision that had been taken. The
citation half is checkable and the prose half is not, which is the same asymmetry §9's docstring
rule has and the reason both are conventions rather than guards.

**`Orth` as an instrument, not only a classifier** (§5) — `Orth x y` is decidable, so it answers
`src/`'s declaration-time separation question by `decide`, and `src/lean.ts`'s `Separation`
carries the one direction that is a law: `src/` never refuses a pair the model certifies. What
it is blind to is the converse, and stating that plainly is the whole of using it — `Orth` is
*sufficient*, so its `false` is a decline and not a refutation, and 66 of 351 corpus pairs are
declines `src/` rightly accepts.

**It is also the first case where the model had an answer by `decide` that `src/` reached by
measurement.** `Orth (.set .string) (.set .number) = true` was true before `ff75c6b` was written;
`src/` refused that declaration, and the way the over-refusal was actually found was measuring
admission over a value corpus. Two instruments, one cheap and exact and already present, the other
statistical over whatever the corpus happened to contain — and the cheap one was not consulted
because nothing connected it to `src/`. That connection is what the bridge is; the lesson is that
a decidable model-side answer is worth wiring to the host guard it specifies *before* reaching
for a corpus.

**The vector bridge** (`src/lean.ts` → `Calculus/Vectors.lean`) — the differential check
between this model and `src/`: the generator emits one theorem per encode the library actually
performed, and the *kernel* decides whether the model agrees. Blind spot, and it cost a day:
**regeneration is not verification.** `src/lean.spec.ts` compares the emitter's bytes against the
committed samples, and those samples are generated *by that emitter* — so a stale generator
agrees with its own stale output and the test passes on the defect it exists to catch. A test
that compares a generator against what it produced cannot see the generator being wrong. It took
`db444e3` changing `Term.object`'s arity, ten commits of green, and `e9f5b31` to find it. What
verifies the bridge is elaboration, which is why `scripts/gate.sh` runs the samples and the full
refusal cross product through Lean rather than trusting the byte comparison. **Refusal vectors
are the other half of the same blind spot**: a positive vector is an agreement about what the
library wrote, so every value it *refuses* produced no vector at all — the half of the pair where
the two sides could disagree unobserved.

Two more, and both are about *which claims can reach the kernel at all* rather than about the
generator being stale.

**No vector asserts a decoded value, so (R) and (C) are tested on the `src/` side and never
elaborated.** Every emitted theorem is `(denote t).e v = some a` or `= none`; `.readverdicts.lean`
is a read-side differential but it compares `AdmA t a` against whether the library *accepted* the
attribute, which is a `Bool`, not the value that came back. So the kernel has never been shown a `p a = some v`.
The two laws most of this library's shipped defects lived in are the two the bridge cannot state.
`veq` (`Vectors.lean:379`, sound by `veq_sound`) is what would make them statable, and
`.resolutions.lean` already uses it for map-valued reads — the cost is a decode corpus and a
`Value` emitter for what comes back, and the same `Double` wall as everywhere else, since a
decoded numeral is a `Value.num` and that axiom has no closed terms. Not built here.

**And the terms the emitter refuses are exactly the terms whose laws a caller owes.** `held`,
`legacy`, `custom` and `lazy` — the four §7 names as carrying a caller's function — plus a
`refine` holding a JavaScript predicate rather than a `Value → Bool`, are unemittable because
nothing translates a closure into a Lean term, and emitting a *different* predicate would compile
and prove the wrong theorem. That refusal is right. What it means is that the bridge is blind
precisely where the model discharges an obligation the host cannot check either — `IsoCancels`,
`ReadsCoherently`, `custom`'s `Lawful` — so for those terms neither instrument is looking, and the
guarantee is a written premise on both sides.

**`scripts/doc_counts.py`** — computes the counts this document rests on and rewrites them
between `<!-- count:NAME -->` markers; `--check` exits 1 on disagreement. It exists because
**every count that drifted this month was a number typed by hand**, and `name_drift.py`
cannot see one: a count is not a name. It caught `Orthogonality.lean`'s length going 951 → 960
within a minute of being written, drift introduced by the commit that corrected §5's table.
Two blind spots, and the second is the same shape as the gap it closes:
- It measures the tree, not the argument. It will say six theorems sit in the *slot* row; it
  cannot say *slot* is the right phase for them. A row filed under the wrong phase keeps every
  total honest and the classification wrong.
- **Two of §5's twenty-five discharges are named in the prose beneath the by-phase table, not
  in a row, so no parser finds them and the script carries them as a hand-written list of two
  names.** A third limit that nobody adds to that list goes quietly missing from the total.

**`scripts/ratchet.py`** — four per-file counts held to the state they were in, failing when
one *rises*: hand-unfolding sites (332), retirement marks (72), public theorems with no
docstring (269 of 896), and decision points. The counts live in `scripts/ratchets.json` and are quoted here by *name* rather than by value, because three places typed this one by hand and gave 3972, 4042 and 5260. It exists because §10's two guards could not be bars: a docstring
coverage bar at 269 is a bar nobody can satisfy, so it would be switched off, where a ratchet
asks nothing on the day it lands and makes the next docstring cheaper than the argument for
skipping it. Baselines live in `scripts/ratchets.json` rather than in the script, so that the
guard's own source stays still and a change to a number is worth reading; a baseline key naming
a file that is gone fails, which is the rot `EXPECTED` demonstrated.

**It changes what gets written, not only what gets noticed**, and the first commit after it
landed is the evidence: `7fff6e8` generalised `sepV_refine_disjoint` with a `show` to
beta-reduce the goal — legitimate, and what its attribute-side twin does — which put the site
count at 333 against a 332 baseline, so the proof went in as `simp only` instead. Not a false
positive, and the reason a ratchet on a number in the hundreds is worth having: the bar it sets
is today's number, and what it buys is that the cheaper proof is the one that passes.

A metric absent from the baseline entirely fails rather than passing as twenty new files —
adding an instrument should not be a way to add an unmeasured number.

Two blind spots:
- **A ratchet accepts the state it was born in, so it cannot see a defect older than itself.**
  The 269 and the 332 are invisible to it by construction — it guards the derivative, not the
  value. `--accept` with a *lowered* number is the only way a baseline should ever move, and
  writing a rise needs `--allow-rise` on top, so that weakening the guard reads as a sentence
  in a commit message rather than as a tool invocation that happened to work.
- The mark count is the only check on a mark at all. `name_drift.py` verifies that a marked
  name is absent, never that it *deserved* marking, so a session that deletes a declaration and
  marks its citations in one commit is still trusted — the count is where that shows, which is
  why it ranges over the documents and not only the docstrings.

**`scripts/twins.py`** — one-sided inversions: an `X_e…` with no `X_p…`, or the reverse, paired
on `(stem, suffix)` so `_isSome` is only ever compared with `_isSome`. It exists because §4c's
rule had been applied to constructions and not to inversions, and **`vocab_audit.py`'s
completeness matrix cannot see that** — its `p-inv` column asks whether *any* lemma named
`restrict_p`-ish exists, one did (`restrict_p`, an iff about `= some v`), so the matrix scored
`restrict` complete on the day the missing `.isSome` twin was costing a 683× fan. Presence is
the wrong question and shape is the right one. Two blind spots:
- **Suffix matching is literal, so most of what it reports is not a pair.** 22 of 37 one-sided
  names are side-specific by construction — a suffix naming a `Value` constructor (`_num`,
  `_str`) cannot exist on the read side, one naming an `Attr` constructor (`_n`) cannot exist on
  the write side. Of the 15 that remain, the `opaq_p_*_agree` family's counterpart is
  `opaq_e_agree`, one lemma where the read side has one per constructor, and no string
  comparison sees that. **`@[simp]` on the surviving side is the filter that works**: it means
  one side rewrites where the other unfolds, and it selects the two real candidates out of 15.
- **It ranks nothing by itself.** A missing twin matters in proportion to the fan it would
  remove, which only `complexity.lean`'s `fanOf` can say. Run today: the two `@[simp]`-flagged
  candidates' one consumer went with the retired tables, so the actionable list is empty and
  `restrict_p_isSome` stays the only instance
  that cost anything. The instrument is prospective, not a backlog.

**`scripts/complexity.py`** — decision points per declaration and per file: pattern rows, `if`,
`dite`, `match`, `cases`/`rcases`/`obtain`/`induction`, `by_cases`, `<;>`, `all_goals`, `.elim`.
It exists because `vocab_audit.py`'s site count is a **vocabulary** measure — a `show` or a
`replace` is a proof taking a definition apart by hand — and says nothing about a proof that
does its work by wide case analysis. Per file the two rank at **Spearman 0.56**, so this is a
second number rather than a restatement: `Discharge.lean` is 8.9 branches per unfolding site
and `Orthogonality.lean` is 31.1, the first hand-unfolding heavy and the second case-analysis
heavy where the older guard is blind. `ratchet.py` holds the count. Two blind spots:
- **The per-file total counts decision points and not per-declaration cyclomatic numbers**,
  and the difference is the whole of whether the metric is usable. `1 + decisions` summed over a
  file adds one per declaration, so *extracting a lemma raises the total* even when it strictly
  reduces the work — which is backwards for §9, where a proof citing a lemma is the goal. Found
  on the metric's first real use: pulling two cases out of `AdmA_exact` cut its proof term from
  2754337 tree nodes to 59397 and the ratchet called it a rise. A guard that fires on the
  refactor it exists to encourage is a guard nobody keeps.
- **The density is the sharper reading and is deliberately not ratcheted.** `occV_sound` at 1.48
  branches a line is the densest proof here; `soundness_both` at 0.36 over 122 lines is a table,
  one line per typing rule, exactly as §5 claims — so the ratio is the number that vindicates
  the long proofs. But its denominator moves when a signature is re-wrapped, and this repo has
  already paid for a formatting-sensitive metric: `7fff6e8` moved `orth_unreach_lines`
  168 → 169 that way. The count does not — re-wrapping a signature onto four lines was run as a
  control and left it unchanged.
- **A `def`'s branch count is usually §3's row count, not a design choice.** `HObject` is 47
  because the object rule has that many cases and `aeq` is 23 because `Attr` has ten
  constructors. Theorems and defs are reported apart for that reason, and a reading that treats
  a table as a tangle is wrong about the specification, not about the code.

**`scripts/complexity.lean`** — what the kernel holds: proof-term size, the sharing behind it,
and direct dependency count, over a named watch list. `blast_radius.lean`'s walk, asked about
one declaration instead of its dependents. **Count the DAG, not the tree**, and that is the
whole reason this file has a header: `Expr` is a DAG, a naive recursive size counts every
occurrence of a shared subterm, and `AdmA_exact` reads as *tree 2754337 / dag 7239*. The tree
number would have been reported here as a finding — three hundred times the largest thing in
the development — when the kernel stores 7239 nodes and `Adm_exact`, at 8844, is **larger**.
**`dagSize` reports a number and never a location**, which is a gap worth stating rather than
discovering: a ratio says a fan is present and says nothing about where. `fanOf` closes it with
a full occurrence walk ranked by occurrences × own size, and on the one fan this development
had it named `inL.match_1` at 1053 occurrences of ~800 nodes.
- **The sharing ratio is the sharpest signal in the tree.** Everything measured sits at 2–19×;
  `AdmA_exact` is at **380×**, alone, which is a tactic duplicating one large subterm across
  every branch. No textual measure sees it — that proof is calm at 0.58 branches a line over
  unremarkable source. When something is slow to check and reads fine, this is the column.
- **Elaboration heartbeats are not deterministic, and that was checked rather than assumed.**
  The counter is a step count and not a clock, so it looks like the right instrument. Three
  `Meta.check` runs on one value in one process spread 1.2% to 13.7%, run 1 always highest —
  cold instance and `whnf` caches — so it measures the cost of checking under a cache state
  rather than a property of the declaration, and a ratchet on it fires on noise. It is a
  tripwire at an order of magnitude, and it corroborates the DAG count: heartbeats and DAG both
  put `Adm_exact` above `AdmA_exact`, the ordering the tree number reverses.
- **Transitive dependency count is a dead end, and it is measured so nobody rebuilds it.** The
  closure runs 750–3710 across the development and its *largest* values are `soundness_both`
  (3650) and `carrier_denote` (3710) — 79 kernel nodes each, the two simplest proofs in every
  other column. It measures which layer of §1's stratification a declaration sits in, not
  complexity. Direct deps (8–225) are worth something as coupling and track the branch count.

**`scripts/unreferenced.lean`** — a **diff instrument only**, not a verdict, and run by hand
(`lake env lean scripts/unreferenced.lean`; it is outside `Calculus/`, so `lake build` never
touches it). Two reasons it cannot be a guard:
- In a specification library the advertised results are unreferenced by construction —
  `Adm_exact`, `soundness_both`, every `not_*` refutation, every worked example. **~300 of
  ~1600.** There is no root set to measure against.
- **Members of a `mutual` block reference each other in no constant's value.** They are distinct
  projections of one induction principle — `Adm_exact` goes through the term family's
  auto-generated `binductionOn` and `Adm_exactO` through a *different* projection of it — so
  there is no edge to follow. `Adm_exactO` is mentioned by *zero* constants in the whole
  environment.

Both defects are stable across revisions, which is what makes the *difference* sound where the
absolute number is not: snapshot, change, compare.

**`scripts/blast_radius.lean`** — transitive dependents of a named declaration, closing over
each declaration's type *and* value. It costs a **declaration**, and it **cannot cost a
constructor**: asked about `Term.object` against `Term.string`, the partition came back 0 / 535 /
7, because the auto-generated `casesOn`'s *type* mentions every constructor, so the closure from
any one of them is "everything that touches `Term`". A constructor-shape change is a syntactic
question wanting a syntactic instrument — the `Body` refactor was costed by hand-classifying 60
hits into 57 code sites, and there was no shortcut. **And the syntactic instrument is `grep`,
which has two blind spots of its own.**

The first is a habit, not a limitation: **a `grep` piped into `head` is not a measurement.**
Twice in one session a truncated pipe produced a false reading here — once nearly asserting in
a commit message that `filter_map_AdmSpecs` and `filter_AdmSpecs` no longer existed, when the
`| head -10` had simply filled with `AdmSpecs` hits first. If a claim rests on a grep, run the
grep without a limit, or count it. The same pipe hides an exit code as readily as a line:
running each of these two guards into `tail` and reading the result reported both clean over a
tree the gate then failed, because what `$?` held was `tail`'s status and not the guard's.

The same habit has a second form on the writing side, and it cost more: **an edit anchor that
is not unique is not an anchor.** A scripted replacement in `src/codec.ts` matched in more
places than the one intended and removed **2300 lines** in a single pass. The suite caught it,
which is the only reason it is a paragraph here rather than a released defect. Anchor every
scripted edit on a whole block that occurs once, and check the line delta before writing —
a diff that is the wrong size is visible in one number and invisible in a review.

The second is real: **anonymous-constructor patterns.** Changing `Typed.held`'s arity
(`c66d493`) missed a consumer because `typed_μSyn` destructures it as `| _, _, _, .held h' _ =>`,
which matches neither `Typed.held` nor `@held` nor `case held`; only the build found it. When
costing a constructor change, grep the bare `.<name>` as well as the qualified form, and expect
the arity to be implicit in a positional match. The control experiment is in its docstring;
`86d3a42`'s commit message claimed otherwise and is wrong.

### The host's instruments, and what each of those is blind to

The TypeScript side has five instruments of its own, and this arc measured a blind spot for
each. They are here because §8 makes the host's obligations part of the correspondence, and an
instrument the host trusts wrongly is how one of those obligations goes unmet.

**The type checker's error count is a lower bound, not a measure.** Retyping a position and
counting the errors under-reports the sites four times over. Three were found in one arc: a
cast standing on the position, so the checker had nothing to say; a test whose subject rode on
a type it did not name, which kept passing while the fact it pinned stopped being checked; and
a comparison at the wrong level of nesting. The fourth is the sharpest, because it is a
deletion rather than a retyping: collapsing a union's option builder to the term-only form
type-checks **cleanly**, because the member's type already admits the absent case and there is
nothing to report,
and fails **eleven** tests. The suite is what closes the gap every time.

**`scripts/name_drift.py` cannot see a name that stops being the right one.** It chases a
declaration that was deleted, so every citation of it dangles and the guard fires. A
declaration that still exists while ceasing to be the one a passage cites is invisible: four
docstrings in `src/codec.ts` pointed at the definition union over a member whose type had
become the *term* half of it, and the guard was green from the change that moved them until the
pass that read them. Renaming is checked; re-pointing is not.

**The strictest checker mode existed and was switched off**, which is a blindness the tool
cannot report because nobody asked it anything. `tsconfig.json` set three strictness flags and
neither of the two that report an unused local or an unused parameter. Asking, with no file
changed, returned **39**
findings the same day — one dead helper in shipped code, one dead import, two dead bindings,
thirteen entity types in specs that asserted nothing, and the rest unused imports. A second
dead helper had been found by reading a week earlier, which is the argument: a checker that is
asked answers every time, and a reader answers when a reader happens to look.

**The type-level snapshot proves negatives, and sees only what a spec asserts.** `@ark/attest`
records an instantiation count and a resolved type per assertion, so a change that moves
neither moved nothing that any assertion covers — which is how a widened constraint was shown
to have changed no derivation, and how a whole-name rename was shown to be a rename. What it
cannot say is anything about a type no spec names, and the population it covers is a choice
somebody made rather than the surface.

**A red `vector emit` that returns in about a second has read nothing.** The bridge shares a
build cache, and a racing run fails immediately over an unchanged tree; the same tree passes on
re-run at twelve to fourteen seconds. Judge that check by its duration before judging it by its
exit code — a genuine failure costs the full elaboration first.

One more blind spot common to all of them: **none looks at `src/`.** `Vectors.lean` is the
only bridge between the model and the shipped TypeScript, and it checks generated vector lines
by kernel typechecking rather than by evaluation — `denote` is `noncomputable` because `Double`
is an axiom, so `#eval` and `native_decide` are both unavailable, and that is not a toolchain
gap to route around.

---

## 7. What is deliberately not modelled

Each of these is a *decision with a price*, not a gap, and each has a witness.

**Recursion under `union`.** `altCodec` resolves a union by *unique* admission, and
`OptionSem.byAttempt` derives admission from `(c.e v).isSome` — so growing a recursive result
grows admission, grows the filtered list from one option to two, and collapses the answer from
`some` to `none`. Unique admission quantifies over the *other* options: a negative condition,
anti-monotone in exactly the argument a fixpoint must grow. `altCodec_not_monotone` is the
`mono` obligation any ccpo construction would have to discharge and cannot; `stage_not_monotone`
shows the same collapse between two adjacent stages. Note the direction — the low-stage answer
is *over*-defined, not under-defined.

The refutation is specific to **counting**. Confluent resolution — where several options admit,
require only that they *agree* — is proved monotone **and** continuous (`selectF_mono`,
`selectF_continuous_list`), and is **not adopted**. `docs/codec-calculus.md` §5 ("A weaker
condition, proved and not adopted") records the trade: order-independence stops being
unconditional, holding only *given the obligation*, and a specification whose commutativity is
conditional is a worse specification. That is a spec call, not a mechanization call.

**§1's nesting bound.** `Nesting.lean` is **the one place `𝔸` is larger in the model than in the
store**, deliberately. `Attr.l` and `Attr.m` nest without limit by construction, so a derivable
term can write an attribute DynamoDB refuses — `not_storable_of_typed` is the witness: a
well-typed term, a value on its held set, an encoding outside `Attr.Storable`. The model must be
able to **state** this, because a target certified against a spec that cannot say it is
certified against a claim weaker than its users read. The honest repair is *not* a carrier
refinement: the witness violates no premise, because §3's rules simply do not mention depth. The
indexed-family alternative is `Attr : Nat → Type`, and the kernel accepts it where it rejects
the subtype — **but only in the mutual form**. The direct shape is refused:

    inductive A : Nat → Type where
      | l {n} (v : List (A n)) : A (n+1)   -- nested inductive parameters cannot
                                           -- contain local variables

so every list position needs a hand-rolled companion indexed alongside it, which is the price:
the same `List`-companion tax `Term` already pays, once per index. Against it, the benefit is
real — bounding the carrier turns the depth *measure* into an index and takes `opaqCodec`'s
input-side budget and its stabilization lemmas with it, and `Opaque.lean` names that budget
around 150 times. Not attempted; the trade is recorded so the next reader does not re-derive
the kernel error.

Note that `Attr.Storable` counts `L` and `M` only, and is a **different function** from
`Attr.depth`, which is a termination measure and charges a wire set a layer. Do not unify them.

**`set(held …)` and `set(legacy …)`**, given up by the `SetBase` index. Not lost:
`set(refine …)` and `set(literal …)` survive, because a restriction of the elements is a
restriction of the set — `setCodec_restrict` proves the two write the same attribute on the
nose, with `liftQ` carrying the predicate through. What is lost is an element-level adapter and
an element-level read widening. Neither appears in `src/`, and neither has a set-level
spelling: a set-level `held` would need `setImage` rather than the classical `Finset.image` to
stay injective, and a set-level `legacy` widens the whole attribute rather than each member.

**The n-ary literal as a union of singletons.** Derivable — `LiteralArity1.lean` is the proof,
including (U) on both sides through `uniqueAdmission_of_sharedBase` — and not taken, because the
union route cannot carry `ℓ` as a `Finset`. Read that module before proposing the collapse
again.

**A `Double` with no closed terms.** §1 axiomatizes the host's number rather than modelling
IEEE-754, because rounding is not a theorem of the calculus. The price is paid in four distinct
places, and they are collected here because each is met by someone doing something reasonable
and finding it impossible, at which point the question is *which* impossibility this is — they
close differently, and only one of them closed.

- **Term-inexpressible** — a numeric `literal`. `Term.literal GroundKind.number ls` needs
  `ls : NEFinset Double`, so there is no alternatives set to write and **no vector of either
  direction** names the term. Permanent.
- **Row-irreducible** — `AdmA .number`'s `.n` row goes through `Double.ofDec`, an axiom with no
  computation rule, so it reduces to neither `true` nor `false` and *both* assertions fail. That
  is how it is told apart from a disagreement: `AdmA .decimal` and `AdmA .string` reduce on the
  same attribute. Permanent.
- **Value-inexpressible** — a decoded numeric set. `union([string.set(), number.set()])` reads an
  `NS` back to a `Set<number>`, whose Lean form is `Value.numSet` over a `NEFinset Double`. The
  term and the attribute are both writable; the *answer* is not. Permanent.
- **Verdict-undecidable** — `veq` at `.num` and `.numSet`. `Double.decEq` is an axiom, so
  comparing two of them would neither reduce nor stay choice-free; the comparator answers
  `.exhausted`, which already means "carries no information". Permanent.

**And a fifth that was not this at all**, which is why the four are worth naming. A read landing
on a *map* also failed to close, and it looked like the same wall — it was the funext gap, `aeq`
having no `Value` twin, and `veq` closed it. `Term.number` itself was likewise refused by the
vector emitter for years on the ground that no value could be named at it: true of a positive
vector, false of a refusal, and deleting that guard gave `number` vectors. **Two of the six
apparent walls here were not the axiom.** Check which one you are at before recording it as
permanent.

**Non-malleability.** `Malleability.lean` records that we deliberately fail it, and why the
relational-format proposal that would have entailed it is refuted (`fmt_forced`): `Fmt` is the
fibre of `p`, so a relational presentation is the same model addressed by fibre, and one cannot
shrink a fibre to buy the agreement clause without losing completeness.

---

## 8. What the host owes, and what it does not

Everything above is about the model. This section is about the other side of the
correspondence, and it is here because the model's structural guarantees are not
self-enforcing in an implementation: §4a's criterion decides what becomes a type *here*, and a
type here is a question the host still has to answer.

**The rule, as JH states it:** prefer making a bad state **unrepresentable** over **guarding**
against it. What follows is what that costs a host, case by case.

### The three cases, and what each one owes

For every structural guarantee the model makes, a host is in exactly one of three positions.

| the host… | owes | why that is the whole debt |
| --- | --- | --- |
| **(a)** carries it structurally | **nothing** — verify by types and move on | the host type is doing the work; there is no gate to own and nothing to test that the type does not already say |
| **(b)** must gate | a **named** gate, in the module that owns the carrier, and a test that asserts **both** sides | *one owner*: a gate mirroring a carrier refinement belongs to the module that *is* the unrefined carrier, not the module that first needed it — a sibling entry point that must not import the first module will otherwise write a second answer to the same question. And a test that checks only our behaviour cannot tell a deliberate divergence from a reference implementation apart from a regression |
| **(c)** cannot express it | a construction-time **refusal**, a test that pins it, and a written **reason** | **the test is the half that goes missing.** An unexplained gate is indistinguishable from an un-migrated one and the next reader "fixes" the signature, so the reason is what the row was written to protect — and measured over this arc, the reason was written both times and the test was absent both times |

### The test is the half that goes missing, and both cases were found by deletion

The row above used to say the *reason* is the part that gets skipped. Two refusals in the
TypeScript host say otherwise, and neither was found by review.

`src/lean.ts`'s emitter refused a §4 field where a `Term` belongs, with the reason written
beside it, and had no test for the four months it existed. It has one now, reached through a
deliberate cast, asserting the message rather than the throw.

`termOf(...)` is the one place a child is taken from a codec a caller handed over, and it refuses a
field for the same reason. Deleting the refusal gives **one** type error — the narrowing is
what makes the return type-check — and a **completely green suite**. So the branch was load
bearing for the type and unobserved for behaviour, and the deletion is what said so; the test
written afterwards was verified by removing the refusal again and watching it fail.

The instruction that follows is not "write the reason", which both of these did. It is: **a
(c) refusal is not finished until a test reaches it past a cast.** A brand is not a proof and
a cast defeats a brand, so the caller the refusal exists for is exactly the caller the type
cannot see — and that caller is the one a test must impersonate.

### A guarantee moving from (c) to (a), and what the gate owes on the way out

The three cases are not a permanent assignment. A host that had to gate can later carry the
guarantee structurally, and when it does, **the gate stops refusing anything**: the constraint
already refuses it, and the gate's remaining content is its message.

The TypeScript host moved four this arc, all of them the same guarantee — a field is not a
codec. Once a field's type stopped claiming the two directions of a pair, and a codec's own
definition became a term rather than a declaration, two positional guards that had refused
`array(optional(string))` and `optional(optional(string))` refused nothing new. The measure was
the suppressions, not the reading: removing all six uses left every one of the eleven
`@ts-expect-error` directives across the element and marker tests with an error still to
suppress, so the type was doing the whole job.

**What such a gate owes on the way out is its message's content, moved where a refused caller
reads it.** The constraint's own diagnostic names the offending type and says a codec was
wanted; it does not say what to write instead. That sentence — here, that a name is the only
thing absence can be said of, and that `nullable` is the member for a value stored as `NULL` —
belongs on the constructor whose call was refused. A gate deleted without moving its sentence
loses the only part of it that was not already carried by the type.

### The exception: a gate a refutation depends on stays — and it is narrower than it was written

This inverts the rule, and the case for it used to be `(literal)`'s `ℓ ⊆ D`: the gate *can* be
typed, and typing it was said to delete the theorem exhibiting a literal that is held and
unwritable, which is (B) failing. For a model whose job is to be checked rather than trusted,
"this cannot be said" is weaker than "this can be said, and here is the theorem saying why it is
wrong" — the second ports to a test in the host and the first ports to nothing.

**That argument is right and its example was wrong, which narrows the exception.** `152ab6b`
typed the gate and the witness survived: it moved to `literalNRule`, an ungated transcription of
§3's rule that is deliberately not a `Term`, and
`literalNRule_holds_what_it_cannot_write` says what it always said. So the exception is not "a
refutation depends on this gate" but:

> Keep the gate only where the refutation **cannot be restated outside the term language**. If
> the thing being refuted is a rule rather than one of our constructors, a standalone
> transcription carries it and the gate can go.

The `℘⁺fin` repair is the case that still pays: typing it destroyed the only `Double`-free
witness that `opaque`'s exactness row over-claims, and no transcription recovers that one,
because the claim is about our own row.

### Measures do not port, so they are pure overhead

`denote`'s `fuel` was unnecessary — a structural definition compiles — and the host reading
sharpens why that mattered: **no line of `src/` has a fuel parameter.** A measure standing in
for a recursion the checker could not see corresponds to *nothing* in an implementation. So the
discipline is a hierarchy, not one rule, in descending order of what it buys:

1. **measure → structure.** No host counterpart at all, so deleting one costs the
   correspondence nothing. Worth an order of magnitude more than (2) on this codebase.
2. **gate → type**, where the condition is decidable from a constructor's own arguments at
   construction *and* the host can mirror it, or can pay (b) or (c) honestly.
3. **keep the gate**, where the exception above genuinely applies.

### Targets differ, and that is a fact about certification

The same structure ports with different fidelity. `NEFinset α` is not expressible for a
variadic in TypeScript and is a newtype with a private constructor in Rust.
`literal (k : GroundKind) (ls : NEFinset k.Carrier)` is a discriminated union of literal types
in TypeScript, easy to widen by accident, and in Rust an enum with a distinct payload per
variant — which *is* the indexed family, and is the clearest case where the model's newest shape
ports better than its old one. `Attr.n : WFNumeral` wants a checked newtype in both; TypeScript
has no nominal typing, so the branded-type trick is the closest thing and a cast defeats it.

A binary literal is the case where the *host* has the sharper instrument. `Attr.b` carries
bytes, and two byte arrays holding the same bytes are the same value in the model, which has no
reference identity to distinguish them. JavaScript does, so a binary literal's read side answers
with the **declared** array rather than with a copy: that is how the host spells "the value the
model means" where the model needs no spelling at all. A target with value semantics for byte
arrays owes nothing here, and one without owes the identity.

**A tag is stored as `S` or `N`, and the model reads a tag from a string literal only.** So the
host admits a discriminator at `string`, `number` or `decimal` — the tag reader carries all three — and
refuses `boolean` and `binary`, which name no tag a lookup could reach. `Denote.lean`'s
`tagsOfField` matches a string literal alone, so the model reads a numeric tag's set as empty and
the fourth-row discharge stops applying to that option. Nothing is unsound; a discharge is lost,
not a guarantee. The emitter refuses such a union rather than emitting a vector about a selection
the model reads as untagged, which is where the disagreement is written down until the host
narrows or the model widens. Measured when the refusal landed: every corpus union uses a string
tag, so no vector moved.

`legacy` is the opposite direction, and it was invisible until the emitter had to refuse it.
`Term.legacy` carries `r : Attr → Option Value` (`Calculus/Term.lean:73`); the host's definition
recorded only the current codec and dropped `r` entirely, so a term the host built did not
determine the codec the host ran. Nothing failed, and no test could have said so, because the
half that was missing was the half nothing read. **The emitter's refusal text was the only
record**: it said the definition drops the older readers, and it was right, and it was the
only place that fact was written down. A host obligation that no host code reads is found by
whatever has to serialise the host's own definition, or it is not found.

**A codec carries a `Term`, and that is case (a) reached by deletion.** `src/` kept two
descriptions of a codec: `Term`, the model's language, and a definition record that grew a row at
a time and kept what each reader needed. Three of that record's rows said something §3 cannot — a
`set`
holding an element *term* where the model indexes by a base, a literal's alternatives not indexed
by their base, a field marker's `inner` a codec where an object's field holds a term — so those
states were reachable here and unrepresentable there. That record is gone. A codec's `def` is a
`Term`, `denote` dispatches on it, and the conversion between the two is deleted with the language
it
converted from. The states stopped being reachable rather than being checked for, which is what
(a) buys: no gate to own and nothing to test that the type does not already say.

The flip had to be one commit, because `denote` dispatches on the one type: the moment the field
changes type, every constructor's literal is a type error and every row reads a shape nothing
writes. Two staged alternatives were refused and are worth naming, because both are the shape a
migration reaches for. A `Def | Term` union on the field compiles just as well half-migrated, so
nothing in the checker says when the transition has finished. A reverse conversion at the
construction site is a second conversion written in order to be deleted. What replaced them was a
meter: a table asserting `termFromDef(c.def)` deep-equal to `c.def`, one row per constructor,
which is exactly "this constructor has been flipped" and which no checker can answer. It read 8
of 20 before the pass and 20 of 20 after, at which point the conversion is the identity and the
table asserts nothing, so both were deleted together.

**So a guarantee that must be a gate in one target may be structural in another.** The three
cases are re-answered per target, at the time that target is certified — not in advance, and not
as a reason to shape the model around one language. The model's job is to make the guarantee
structural *in the model*; how much each target carries is that target's certification, which is
a separate and currently unmet obligation.

---

## 9. The proof vocabulary, and what a docstring is for

Absorbed from `VOCABULARY.md` when that file was deleted as archaeology. Its measurements went
with it; these are the rules, and `scripts/vocab_audit.py` is what holds the tree to them.

### The rule

> **A definition is unfolded once, in its own inversion lemma. Every proof downstream cites the
> lemma.**

Each construction gets two, proved in one step and being the *only* place that construction's
`Option` chain is ever taken apart:

    theorem X_e : (X …).e v = some a ↔ ⟨what X writes⟩
    theorem X_p : (X …).p a = some v ↔ ⟨what X reads⟩

Downstream, `obtain ⟨…⟩ := X_e.mp he` opens a proof in one line and `X_e.mpr ⟨…⟩` closes it in
one. What it replaces is the eight-line hand unfolding, repeated per site.

### The naming scheme — **normative**, so the next proof inherits it

| form | means |
| --- | --- |
| `X_e` / `X_p` | inversion — what `X` writes, what `X` reads |
| `X_eq` | `X` **is** an instance of a named construction, on the nose |
| `lawfulCore_X` / `lawful_X` / `carrier_X` | the three obligations, in that order |
| `Lawful.X` / `LawfulCore.X` | the same where the construction is itself namespaced; `Lawful.through` reads "`through` preserves `Lawful`", which is the better name. Both forms are sanctioned and `vocab_audit.py` prints the split rather than absorbing it |
| `f_sound` | a syntactic function agrees with the denotation (`Adm_sound`, `AdmA_sound`) |
| `equiv_X` | a §6 row |
| `not_X` | a refutation — a "Do not hold" row, or a repaired discharger |
| `onKind_X` | `X` is pinned to a kind (§3's "self-identifying") |

### What a docstring is for

**The source explains the code; the history is in `git log`.** In a docstring, keep:

- the **§ tag** — which rule or clause this is, which `fidelity_audit.py` counts and which lets
  a reviewer check a theorem in isolation;
- the **forced choice** — why the definition could not have been the obvious other one
  (`number`'s `p` gating on the round-tripped value, not the stored digits);
- what a **refutation is a refutation of**.

Move out: how a finding was made, what it cost, which audit missed it, and any argument another
document already states. And prefer a name that makes the sentence unnecessary —
`unionLiteralString` needs no gloss.

**A name the sources do not define is marked, not backticked — `~~oldName~~` — and this is
normative.** Usually it is retired: a docstring that records what a forced choice cost has to
name the thing that lost, and that is the convention above working, not drift: "Was ~~denoteωF~~", "~~encPair~~/~~decPair~~ are gone with
the traversal". But `name_drift.py` reads the code, and to it a deliberately dead name and a
renamed one are the same token absent from the sources — the difference is the tense of the
sentence, which no parser reads. The mark carries it. **An unmarked backticked name is a claim
that it is live, and the guard holds you to it**; a marked one is a claim that it is dead, and
the guard holds you to that too — `~~X~~` where `X` is still in the sources fails as a *false
retirement*. Occasionally the name never existed — `Value.depth`'s missing ~~depthP~~
companion, which the map row has no list to need — and the mark says the same useful thing
there. Sixty citations were relabelled when this came in and eighteen turned out to be
genuinely stale, so the ratio is roughly three to one: assume a name you are about to write in
the past tense wants the marker. §6 has the measurement and the shapes that lost.

**A backtick in this file means a Lean name, so a host identifier is written as a call, as a
path, or in prose.** The guard reads every backticked single word as a name `Calculus/` should
define, and it is right to: the alternative is a fifth category in `EXPECTED`, which would make
that table's entries stop meaning "this absence is deliberate". §6's host paragraphs are the
first passage here to need the distinction and they keep it.

Two further conventions, both load-bearing:

- **The core lemma is not a second proof.** `lawfulCore_X` and `lawful_X` share their clauses
  and differ only where the content differs, and `Lawful.core` is the projection that makes the
  weaker one a corollary rather than a parallel development. Today the difference is one place:
  `set`'s (C), where (MP)'s member-uniformity is replaced by the `(set)` rule's own premise.
- **An identity stated in prose gets cashed as an equation.** `arrayCodec_eq`, `tupleCodec_eq`
  and `objectCodecCore_eq` each say "this construction *is* that one" and carry every lemma
  across by `▸`; `record` gets the same service from a directional pair,
  `recordCodec_e_eq`/`recordCodec_p_eq`, because it is not definitionally the traversal.

Inline `--` comments are exempt. They are proof waypoints inside a long tactic block —
navigation, which is the one thing a name cannot supply.

### Length is not the metric; sites are

`soundness_both` and `carrier_denote` are near the top of the length table and belong there:
each is one line per typing rule, a table of which two combinator lemmas each rule cites. That
is the right shape for a theorem whose content *is* the rule-by-rule dispatch, and compressing
it would cost the reader the correspondence with §3–§5.

---

## 10. Open architectural questions

One line each, with the number or name that decides it.

**The value/attribute doubling.** Nearly every analysis declaration has an attribute twin, and
the question is whether the two sides should be one parametrised development. A probe found the
side-split stays **local** — it does not thread through the codec algebra, for §4c's reason:
`carriedCodec` states one codec for both sides — and that the mergeable bulk sits in
`Exactness.lean`. `set` is the standing exception, the one product that is not an instance
(§4c, `setCodec` in `Combinators.lean`).
*The numbers I was handed — 82 twin pairs, ~45 mergeable — are recorded nowhere in the repo and
I could not reproduce them.* A naming-based count over the declarations of `Calculus/`
(twin = `X`/`XA`, or a `V`→`A` or `Value`→`Attr` substitution) gives **72 pairs, 34 of them in
`Exactness.lean`**, over 1276 declarations; loosening the transform to include the write/read
`_e`/`_p` split gives 100. **Do not cost this on a pair count — every count here is an artifact
of its transform, and three passes have produced 82, 69 and 72.**

**Measured on the dimension that actually decides it, the merge is not worth doing.** Rename
each value-side declaration to its attribute-side twin, then compare the two bodies textually:

- The **40 pairs at ≥0.9 similarity average 5.1 lines each** — 203 attribute-side lines of
  membership lemmas, `mem` wrappers and one-line `Exact*` abbreviations. These are the
  mergeable ones, and they are mergeable *because* they are tiny.
- The **12 pairs of ≥15 attribute-side lines hold 363 of the 648** — more than half the twin
  mass — and average **0.67**, with the largest being the least alike: `ExactV_set`/`ExactA_set`
  **59 lines at 0.16**, `occV`/`occA` 22 at **0.06**, `occV_sound`/`occA_sound` 45 at 0.32,
  `AdmLit`/`AdmALit` 14 at 0.33, `Adm`/`AdmA` 38 at 0.58.

So the twins that are cheap to merge are cheap because there is nothing in them, and the twins
holding the bulk are twins in name only — which is §4c's point arriving from the other side:
`carriedCodec` states one codec for both sides precisely where the two sides *are* the same, and
where they are not, the doubling is content. A parametrised development would abstract 203 lines
of boilerplate and leave the 363 that matter untouched. The absolute ratios move with the
transform; the *ordering* does not, and the ordering is the verdict. Two passes over the same
648 lines, differing only in whether the value-side names were renamed to their twins before
comparing, gave 40 pairs ≥0.9 and 10 — but both put `ExactV_set`/`ExactA_set` at 0.16 and both
put the biggest twins at the bottom. **Neither the pair count nor any single similarity number
is the dimension; the size-against-similarity ordering is.**

**`select` over `List.attach` — probed, and it does not pay.** The queued item said that
because `List.filter` hands back a bare element, every proof needing "the surviving option came
from *this* term" recovers it by hand (`List.mem_of_mem_filter (by rw [hf]; simp)`, at ten sites
in `Exactness.lean` and `Orthogonality.lean`), and that attaching membership would carry it
through. Both halves were measured and both are wrong — and the ten was six.

A `select` written over `os.attach.filter` works: the iff re-proves with the *same* four
tactic lines,
and `select_admits` does get its membership free — `⟨o.1, o.2, hr⟩` where it used to call
`mem_of_filter_eq_singleton`. That saves one line, in one lemma. What the consumers see instead
is a filter equation over `os.attach`, a list of subtypes, with an `o.1` on every use of the
survivor. **And the membership `attach` hands back is the wrong one.** No consumer holds `os`;
they hold `opts : List Term` with `os = semsOf opts`, which is `opts.map`, so `o.2` proves
`o.1 ∈ opts.map f` when what all ten sites want is `t ∈ opts`. `List.mem_map.mp` is still
needed, on top of the projection. The obstruction is not removed, it is relocated and taxed.

The queued text also offered the filter-over-map commutation lemmas (`filter_map_AdmSpecs`,
`filter_AdmSpecs`) as evidence for the change. They exist and they do carry that commutation —
and they are an argument the other way: `(opts.map f).attach` has no clean commutation with
`map`, where `opts.map f |> List.filter` has one already proved twice.

The ten sites were never blocked on `select` at all: `mem_of_filter_eq_singleton`
(`Lists.lean:271`) already turns `hf : l.filter p = [x]` into `x ∈ l ∧ p x = true` in one term,
and the sites open-code it instead of calling it. **That is a six-site cleanup in one late
file, not a change to `select` deep in the graph** — no clean build window required, and it is
the whole of what the queued item was actually after.

*Done, and the ten-site count was mine and was wrong.* Six of the ten hold a filter *equation*
and are `(mem_of_filter_eq_singleton h).1`. Two more (`mem_allTags`, twice) applied a pair of
one-sided `List.filter` lemmas to the same membership hypothesis, where `List.mem_filter.mp`
gives both halves at once. The last two, in `Orthogonality.lean`, recover
from a membership hypothesis and need exactly the one lemma they already call — nothing to do.
Sixteen lines changed, no behaviour, `Orthogonality.lean` untouched.

**~~`adm (.literal .number ls)` is not exact~~ — closed at JH's call, by the carrier route.**
`GroundKind.number.Carrier` is now `{d : Double // Numeral.WF d.toDec = true}`, so `inL` splits
on the element's own gate and ~~LiteralD~~ is deleted, which made the per-aspect literal row
exact with **nothing added to it** — the two rows were the same function. The alternative
route, tightening the row, would have broken that row's `rfl` and every ~~SepV~~ over
literals; the carrier route broke the `rfl` too, and nothing else.

*And the reason it was a fidelity call turned out to be misstated, in this file and in three
docstrings.* The witness `literalNRule_holds_what_it_cannot_write` was said to record a defect in
**§3's rule**. It does not: §3's `(literal)` premise line is `ℓ₁ … ℓₙ ∈ T`, and at `g = number`
the base's held set is §1's `D`, so **the rule already requires `ℓ ⊆ D`** — `hD` was transcribing
it faithfully, not compensating for its absence. What the witness shows is that the rule's
premise is *load-bearing*: omit it and (B) fails. That claim needs an ungated prism to be about,
not an ungated `Term`, so it is restated on `literalNRule` (`Refutations.lean`), which is
deliberately not a `Term`. `docs/codec-calculus.md` needed no change; the rule is unchanged.

**~~`(dunion)`'s two premises~~ — narrowed at JH's call, and the narrowing bought nothing
mechanical.** The discriminator's literal is arity one; n-ary literals stay everywhere else. **The
expectation was proof simplification and there was none**, which is the result worth recording:
every proof over `(dunion)` consumes only the tag set's *nonemptiness* — `tagsOf_ne_nil`'s
four-job inversion, `dunion_stamp`, `uniqueAdmission_byTag`, `ExactV_dunion`/`ExactA_dunion` — and
not one of them consults the arity. The premise went from `Nonempty` to `card = 1`, one three-line
bridge recovers the weaker fact, and the machinery measured 39 declarations / 350 lines before and
40 / 353 after. Nothing shrank because nothing was ever waiting on it. The payoff is that the
language no longer admits a variant answering to two tags, which is a statement about what a
lookup is and not a lever on the model. **`src/` is aligned as of `999b877`**: `EveryOptionTagged`
refuses a multi-valued discriminator literal at compile time and the constructor refuses one at
construction. It cost four deliberate tests, which that commit records.

**`(held)`'s iso premise is stronger than the proof consumes.** The doc demands total
cancellation on the carriers; `IsoCancels` restricts both directions to `(c.e ·).isSome`, and
`soundness_both` closes on the restricted form. So the specification asks for more than the
mechanization needs — the mirror image of a premise that is too weak, and the same defect
class. Reported, never resolved: either the doc's premise is loosened to what the proof uses,
or the model is asked to discharge the stronger one. Carried here from the representation audit,
which is deleted.

**§1's `℘⁺fin` and `⇀fin` are not in the carrier, and the two omissions cancel — which nothing
else states.** `Attr.ss []` is well-formed and `M` admits duplicate keys, and `Domain.lean`
records the list-for-set choice as being about *order* only. That is not the whole of it.
`HSet` is a nonempty **list**, so `set [x,x]` encodes to `ss [s,s]` and reads back, and (R)
holds. Under §1's actual `℘⁺fin` the wire set would collapse and **(R) would fail on that
input**. So the two widenings are load-bearing on each other: tightening either one alone
breaks `lawful_setCodec`. This project has already paid for that class of error once, at
`HOpaque` admitting `set []`. The audit that found the coupling said the coupling was stated
nowhere; this paragraph is now the only place it is, which is why it is here rather than gone.

**§6's held-set row is closed on one of its two readings, and the other is the open half.**
`typed_T_identity` proves `(denote t).T v ↔ T v` at all twenty-one rules, so the judgement's
held-set index is a **pure description of the denotation** — it carries nothing the pair does
not already determine. (`§3` throughout this paragraph is `docs/codec-calculus.md`'s, not this
file's.) `HeldSet.lean` separates the two claims the row ran together: (A) `T = (denote t).T`,
now proved — and definitional at a `union`, which is `altCodec_T` — and (B) `T = dom(e)`, which
is false there and keeps `not_TIsDomE_unionLiteralString` as its witness. **(B) is what is still open; (A) is not.**

The obvious consequence — the index is redundant, delete it and index the judgement by
`(denote t).T` — is **declined, and not on cost.** The rules are the model's transcription of
§3, and a rule whose held set is spelled `(denote t).T` cannot be read against the document it
transcribes; the identity is what makes the transcription checked rather than advertised, and
it only means that because the two sides are written independently. Deleting one side would
delete the claim, not prove it. The line cost is in the commit that landed it.

*What the probe expected to fail and did not is worth recording, because in each case an
earlier move had already closed it.* `literal` at `number`: the rule's `HLit k ls` and the
denotation's are one expression, because the carrier is gated (§4a) — the same fact that
removed `typed_TSub`'s five-way split there. `object`'s open part: an undeclared key under
`drop` or `refuse` is refused by **both** sides, `R` being `none` by `TypedRest` and `rcOf`
`none` by definition, so the branches agree rather than diverge. `opaque` at numerals: closed
when `HOpaque`'s `num` row gained its `D` premise. Three predicted obstructions, three already
paid for — which is the argument for probing a claim about the tree before costing it.

**§6's commutativity row was the adjacent transposition, and is now the permutation.**
`equiv_altCodec_swap` proved the adjacent case only, and the table's "all" was worth what one
transposition is worth: the generating argument needs `≡` to compose, which
`Refutations.not_equiv_trans` refutes. `README.md` was always honest about this and the change
log's "twenty of twenty" was not. `altCodec_perm` closes it at any `List.Perm`, and closes it
at a claim the row did not ask for — reordering the options yields the **same codec**, not an
equivalent one, so the lift never enters `≡` and never meets its failure of transitivity. The
whole of it is `select_perm`: `select` reads its list only through the filter, `List.Perm`
carries the filter along, and the two lengths at which `select` answers at all — none and one
— are the two a permutation pins. The `≡`-is-not-transitive caveat still bounds what a table of rewrites licenses; it no
longer bounds this row.

**Two guards on `Axioms.lean`'s principle — built, and one of them is not the shape this
section asked for.** `scripts/ratchet.py` (§6) holds `vocab_audit.py`'s site count and fails
when it rises, which makes §9's rule enforceable rather than aspirational. The second was
specified here as a docstring-coverage *bar* on public theorems — that a reader who knows the
specification can tell what a theorem says from its name and one line. Measured, 269 of 896
public theorems carry no docstring, so a bar is decoration: it would be switched off or exempted
into meaninglessness, and the number it would have to name is the number it exists to reject.
A ratchet needs nothing of the kind, costs zero to satisfy on the day it lands, and is what
shipped. **The bar above is still the right target; it is not the right instrument.** (This
section also said `fidelity_audit.py` reports both numbers, and it does not: it reports
docstring and §-tag coverage, and the site count is `vocab_audit.py`'s.)

**~~The admission reader's violation list, and wiring it into `union`'s resolver~~ — done, at JH's
call, and
the list was six times longer than the item said.** `admits(c, v) ⟺ !isError(c.encode(v))` was
false one way because encoding did not validate. The item named four codecs; the repo's own
pinned test said **twenty-three of thirty-two** and had since it was written. Eleven gates closed
all of them, because **twelve were loose only through their elements** — a `tuple` took a byte
array of the right length because its positions did, and the wrappers, the field table,
`legacy`, `held`, `lazy` and both unions inherited the same way. Five ground gates closed
seventeen; only the six loose in their *own* row needed one each. `opaque` and `custom` are
carved out, because admission reaches them **by asking the codec to write**, so consulting it
there would not terminate.

The resolver's write side decides through admission now, and the swap changed no test — which is
the evidence the law had to land first. It also closed a recorded defect neither of its two
candidate repairs would have needed: a union of a date adapter over `decimal` with `string`
could not write a date at all, and the cause was in the defect's own prose — with no `κ` the
resolver falls back to attempting, and `string` wrote whatever it was handed. **The ambiguity was never real; it
was the write side's looseness wearing an ambiguity's clothes.**

**~~The resolver's read side, through a port of `AdmA`~~ — rejected on measurement, and the
guard a port would have needed is what landed instead.** The read side **already validates**,
because it parses data somebody else wrote; the write side trusted its argument's *type*, and
that asymmetry is the whole of why wiring gained there and would gain nothing here. Measured
over 864 (codec, attribute) pairs from the vector corpus: `AdmA t a` and whether the library's
read accepted it agree at **861 of 861 checkable pairs** and disagree at none.

The remaining three are **stuck, not divergent**: `AdmA .number`'s `.n` row goes through
`Double.ofDec`, an axiom with no computation rule, so it reduces to neither `true` nor `false`
and *both* assertions fail — which is how it was told apart from a disagreement, `AdmA .decimal`
and `AdmA .string` reducing fine on the same attribute. Note the shape against `number`'s other
boundary (§6): a positive *vector* there is impossible because no `Value.num` can be **written**,
while here the term and the attribute are both writable and the **row** will not compute.

So a def-reading port would be a second description of what the read side already computes
exactly, and two descriptions of one thing need a guard between them. The differential is that guard —
`src/lean.ts`'s `ReadVerdict`, generated and elaborated by `scripts/gate.sh` beside the refusal
and separation artifacts. **Do not re-open this as a port without first showing a pair where the
two disagree.**

**And the read-side twin — built, internal, after the admission reader itself stopped being
public.** The
first answer was to decline it as API, and then JH's reading changed the question: *"admits
should not be a public api in the first place. Those and the proposed one are internal utils."*
So the **six definition readers** — admission, the value-kind and member readers, the constant
reader, the set-base reduction and the path walk — left the published surface, and the twin arrived
as an internal one.

The mechanism is the finding, because those two were not separable. It was public **only**
because `src/Rotorise.ts` said `export * from './codec'`; this library has no package-private,
no `@internal` convention and nothing testing its surface, so "internal but importable" did not
exist. Moving the function to its own module hits a real import cycle — it needs `codec.ts`'s
helpers and `codec.ts`'s resolver needs it. What remained was to **enumerate**: `export type *`
for the sixty-six types and a list for the thirty values that are API, twenty-three of them
pinned by name in `Rotorise.spec.ts`. Adding a codec is a
line in that list now, which is the cost, and the point — an export becomes a decision rather
than a consequence of where a function happens to live. `46cb950` shipped it public with
no such decision taken.

**And the enumeration is what made the twin expressible**, which is the only reason it was
built: `codec.ts` can export freely now without reaching the surface. Two places had already
written it — `testing.ts` as `reads`, `lean.ts`'s read-verdict generator as the same six lines
inlined — and neither could see the other's. The read-side predicate is those two, once. It
**asks the codec** and is not a reader of the definition: admission had to read rows because the
write side
was loose, and this must not, because the read side is already exact (`a41f874`). A future
proposal reaching for twenty-one rows here is repeating that rejection.

---

### The white-room arc's open findings, triaged

Two findings from the arc that made a codec carry its `Term`. Each is stated in the present
tense, because each is true of the tree as it stands.

**The generators have left the codec object.** A `custom`'s generator and shrinker were a
projection of the term, written by `denote` at `custom` alone and read by the two derivers in
`src/testing.ts` before the term was consulted — one fact on two paths. The term is the only source now, `custom`'s parameter
record still states them because that is how a hand-written codec says how it generates, and a
caller that wants to share a generator names it rather than reading it back off a pair.

**A refusal renders the value it rejects, and rendering runs the caller's code.** Converting a
value to a string reaches that value's own conversion methods, which the caller wrote. An object
made with a null prototype has none, so the conversion throws: a value of that shape reaching
`string`, `number`, `decimal`, `boolean`, `binary` or either literal form raised the host
language's type error out of the write half instead of returning the pair's own error — an
expected refusal becoming an exception inside the refusal path. The conversion is caught at that
seam now. There is no total renderer to write instead, because the conversion methods are
arbitrary user code.

### What the arc closed

**A union cannot hold an option no value can select, and `union([opaque, X])` is refused.** JH's
ruling. It is not `opaque` with `X` beside it: §5's `select` acts only where *exactly one* option
admits, and `opaque` admits every value `X` does, so the union is **undefined** wherever `X`
admits and `opaque` everywhere else. `X` is declared and can never be chosen. That is §5's
failure rather than a question of precedence — no ranking resolves it, because ranking would
choose an option the model says is not chosen.

The guard exempted an `opaque` option instead of comparing it, on the ground that its occupancy is
`⊤`. §5 separates the two things a `⊤` covers: *unknown*, which is an adapter, a `custom` and a
host `lazy`, and *everything*, which is what `opaque` is by design. The model states the second as
a **closed form**, and the host now does too — `occV` and `occA` answer every constructor at
`lossy` and every one but the numeric at `refuse`, where they used to answer nothing. `Orth1` then
finds the meeting and the pair is refused at the declaration.

**The corpus's refusal set moves from 17 pairs to 32**, all fifteen new ones with `opaque` on a
side, every one of the fifteen theorems holding — `Orth (Term.opaq false) Term.string` is `false`
— so the one-directional law `.separations.lean` pins is untouched. The resolver is not touched
either: `.resolutions.lean` stays at 455 and `.readverdicts.lean` at 921, which is the check that
this changed a declaration and not a resolution. With the declaration refused, an `opaque` option
reaches a union only alone, so the resolver's reading of `opaque` no longer decides anything and
the value-kind reader keeps it.

**The type level already refused the pair, and had before this rule.** `opaque` reads back as
`unknown`, which absorbs every other option's type, so the type-level option check reports
"options 0 and 1 read back as the same type" at compile time. What this adds is the runtime half, reached by a
caller who casts past that type or writes plain JavaScript. So the change is breaking for those
callers and for no one else, and the refusal names `opaque` as the option to remove, in the
caller's vocabulary rather than the term's.


**The host's two value alphabets are not two vocabularies for one thing.** `1060c01` recorded
them as a merge
for a later pass. They are the codomains of two different functions: the first is what the value
classifier in `src/value.ts` answers about a **value**, coarse because an empty set belongs to no
family and telling `strSet` from `numSet` means inspecting elements; the second is what `occV`
answers about a **term**, where the base is in hand. **No total function takes a value to a `Slot`**, so neither replaces
the other and the merge is not available.

**A guard's own table goes stale, and two did.** `name_drift.py`'s `HOST` exempts a name from the
drift check, and seven of its thirteen entries named declarations that no longer existed —
including one this tree never declared at all. That is why §5 could name two dead functions with
every check green. `Rotorise.spec.ts`'s surface guard had the same shape: eight of twelve rows
named deleted functions, and the host's own-property test answers false for a name nothing
declares, so they asserted nothing while their live replacements went unguarded. Both tables are
the live names now, and `name_drift.py` checks its own with an **anchored** declaration grep,
because a name can be live as a local variable while its declaration is gone — the path walk was.

**A deleted declaration leaves its docstring behind.** Three passes running, ten sites in total.
`scripts/docstring_anchor.py` is the check: a docstring that another docstring immediately
follows binds to nothing, since JSDoc takes the last. Deliberate two-part prose marks the earlier
block `@anchored`. It found a type-level marker's docstring stranded 1,176 lines from its
declaration, and it found a hole in its own first version — a doc comment opening and closing on
one line was invisible to it — by failing to report a planted orphan.

---

## 11. If you change something

- New module under `Calculus/` → reachable from `Axioms.lean` (§1), and `ratchet.py
  --accept` to admit its counts (§6) — a new module has no prior state, so it is
  baselined rather than judged.
- New stratum in the term family → all nine companions (§2), counted per side.
- New rule → put each premise in one of the three places, `Typed`/`Obligations`/`MPOk` (§2).
- New term recursion → `term_depth_wf`, and new inequalities beside `Term.depth` (§3).
- New analysis row → prefer asking the codec over describing the set (§4b); then prove its
  exactness clause, because a missing row is a silent `⊤` and `⊤` is sound.
- Sharpening a `⊤` row at a container → check what was relying on the slack (§5), and cost it
  with `scripts/blast_radius.lean`, not with grep.
- Citing a Lean name in `README.md`, this file, or
  `docs/codec-calculus.md` → `python3 scripts/name_drift.py` must exit 0. Single-word
  citations are covered as of `83d61df`; four categories are skipped by shape and the reason
  for each is in the script.
- Stating a count in this file → put it between `<!-- count:NAME -->` markers and add it to
  `scripts/doc_counts.py`, then `--check` must exit 0. An unmarked count is unguarded, and
  every count that drifted this month was an unmarked one.
- Deleting a declaration → snapshot `scripts/unreferenced.lean` before and after and read the
  *difference*.
- Touching a normative document, the advertised axiom base, or `src/` behaviour → that is the
  user's decision. Deliver the measurement and stop.
- Committing anything → `scripts/gate.sh`, and gate on its **exit code**. Eight checks: the five
  Python guards on the host, `lake build` in the container, then **vector emit** (generating the
  four bridge artifacts) and **vector bridge** (elaborating them beside the two committed vector
  samples). It prints one line per check and exits nonzero if any failed. `--no-build` drops the
  three that need the container and is honest only when nothing you touched can reach the
  elaborator — a `.lean` docstring can, and a comments-only edit still
  moves the counts `doc_counts.py` guards, so it is not the "docs" flag it looks like. Two commits (`eed1b58`,
  `e3bd71f`) claimed a green tree over a red one by printing exit codes instead of testing
  them; that is the defect the script exists to make unavailable.

### …and on the `src/` side, per structural guarantee (§8)

- Which of §8's three cases is this host in? Answer it before writing the gate, not after.
- **(a)** Name the host type that carries it. No gate, no test.
- **(b)** The gate lives in the module that owns the carrier, not the first caller. One owner.
- **(b)** The test asserts *both* sides wherever the behaviour diverges from a reference
  implementation — otherwise a deliberate divergence and a regression look identical.
- **(c)** Construction-time refusal, a test that pins it, and a comment saying why the type
  cannot carry it.
- Does a refutation depend on this being a gate *in the model*? Only then keep it, and only if
  the refutation cannot be restated outside the term language (§8).
- Is it a *measure* rather than a guard? Then it has no host counterpart and is overhead (§8).
- **Un-typeable never means un-checkable.** A constraint that fails "can it be a type?" is not
  disposed of; it is handed to the next question, "does anything enforce it?". Filing it as
  closed on the first answer is a recorded failure mode of this project's own auditing.
