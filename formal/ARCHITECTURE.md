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
| What changed and why, historically | `docs/codec-formalization.md` |
| Findings, refutations, prices | `docs/codec-audit.md` |
| Module table, modelling decisions, how to build | `README.md` |
| Whether the model *is* the specification | `FIDELITY.md` |
| How a proof is meant to read | `VOCABULARY.md` |

One standing rule from `WORKING-AGREEMENT.md` governs this file too: **record why, not what**,
and **a documented verdict is a hypothesis**. Everything below was re-checked against the
sources rather than inherited; where a recorded claim did not survive, the correction is
stated inline.

---

## 1. The layering, and the one thing the build enforces about it

21 modules, and the import graph is an almost-linear spine — `Domain` → `Codec` →
{`Combinators`, `Term`} → `Denote` → `Typing` → `Soundness` → the analyses (`Discharge`,
`HeldSet`, `Nesting`, `Equations`, `Malleability`) → `Exactness` → `Orthogonality`, with
`Axioms` as the sink. `python3 scripts/guard_reach.py --graph` prints it; nothing else is
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

> `README.md`'s module table predates five of the 21 modules — `Exactness.lean`,
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

**The pattern, so a fifth stratum is written correctly.** A stratum owes seven companions,
and the existing four each have them:

| Companion | For `Body` | Why it is owed |
| --- | --- | --- |
| a depth clause | `Body.depth` | §3's termination measure must see through it (§3 below) |
| a denotation clause | `bodySem` | `denote` must dispatch without a case split at the use site |
| a spec projection | `Body.spec` | `select` counts an object option by its names, not its contents |
| a member/tag projection | `Body.tags` | the union residues read this, not the payload |
| an admission row | `AdmBody` | exactness is per-row; a stratum with no row cannot be exact |
| a premise carrier | `ObligationsBody` | semantic side conditions are structural, not global |
| a law exemption | `MPOkBody` | `legacy`'s (MP) exemption propagates through the stratum |

Miss one and the failure is not a build error but a silent `⊤`: the analysis will still be
*sound* and will have stopped saying anything. That asymmetry is the subject of §5.

`Body`'s projections (`Body.fields`, `Body.at`, `Body.rest`) are written by hand — a `mutual`
block admits no `structure`. Rows needing all three still pattern-match on `.mk`, which keeps
the equation compiler's iota reductions available.

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

`term_depth_wf` is the shared `decreasing_by` tactic. **Three** declarations use it, all in
`Soundness.lean`: `soundness_both`, `typed_TSub`, `carrier_denote`. Their goal sets differ, so
some alternatives in the block are dead at each site — that is what `unreachableTactic` reports
there, and it is why the option is disabled at those declarations rather than the block being
specialised three ways.

**Its docstring said *five* until `7a91de8`**, naming `Adm_sound` and `AdmA_sound`. Those do not
recurse: `Adm_exact`/`AdmA_exact` are structural mutual recursions with no `termination_by`, and
the two `_sound` results are one-line corollaries. The claim was true before the exactness
rewrite and nothing was keeping it honest — see §6 on why `scripts/name_drift.py` could not
catch it.

Anything new recursing on a term takes `term_depth_wf`, and if it needs an inequality the block
does not offer, the inequality goes in `Term.lean` beside `Term.depth_lt_object_req` and
friends — not inline.

---

## 4. The three recurring design moves

These are the architecture, more than the module list is.

### 4a. A premise becomes an index

Repeatedly, a typing-rule side condition turned out to be expressible in the *type* of the
constructor, at which point violating it stops being possible rather than being refused.

- **`SetBase`.** §3 `(set)`'s premise was `⊢ c : T ⇝ μ` with `setMember μ = some μS`, and
  `setMember` is partial — so the constructor accepted element terms the rule then refused
  (`set(union(string, boolean))` was the standing witness). `SetBase` is the four bases that
  survive the premise; `SetBase.member` is now a total function of the index, and the refusal
  is a type error.
- **`GroundKind`.** Three literal constructors — arity-one, `literalS`, `literalN` — became
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

### 4b. A row asks its codec instead of describing it

The analysis tables in `Discharge.lean` (`κ`, `ident`, `adm`, `admA`) approximate what a codec
writes and reads. A row can either *describe* the set or *call the codec and ask*. `custom`
always asked (`(cp a).isSome`, because `p := cp`). Over two arcs, six more converted:

| Row | What it asks | The excuse it retired |
| --- | --- | --- |
| `opaq` | `((opaqCodecω lossy).p a).isSome` | "`opaque` needs a rule of its own" |
| `admA .number` | `(numberCodec.p a).isSome` | "`Double.ofDec` is an axiom, so no syntactic set bounds it" |
| `admALit .number` | `((literalCodec .number ls).p a).isSome` | the same, at a literal |
| `admALit .decimal` | `((literalCodec .decimal ls).p a).isSome` | could be spelled out; asking keeps *one* definition |
| `refine` (read side) | `refineReads t q a` | "`q` tests the value a read produces" |
| `nullable` | `Codec.ownsNull` | "`ownsNull` is a disjunction over both halves of the pair" |
| `union` | the count, given the options' exactness | "a count is anti-monotone" — true of the *table*, recorded as a fact about the row |

Every one of those excuses was a correct observation reaching a wrong conclusion, and the
pattern is identical: *no syntactic set names it* is a reason to stop being syntactic, not a
reason to give up. `denote (.literal .number ls)` **is** `literalCodec .number ls` by `rfl`, so
the row that asks is `dom(p)` on the nose.

**The corollary is the load-bearing part, and it generalises past this repo:** a description
must be kept in agreement with what it describes; a question cannot drift. When you are about
to add a row, prefer asking. The price is only that the row becomes `noncomputable` when the
codec is, which costs nothing here — `Double`'s equality is a field of an axiomatized interface
already.

### 4c. The guards exist because prose does not typecheck

Every instrument in §6 was built after a description drifted from what it described: an axiom
claim in prose (`#assert_axioms_all`), a `@[simp]` attribute asserting a behaviour that had
stopped being true (`#lint_calculus`), a citation of a deleted name (`scripts/name_drift.py`), a
regex passed off as a reachability measurement (`scripts/unreferenced.lean`), a grep passed off
as a refactor estimate (`scripts/blast_radius.lean`). None of them was added speculatively.

---

## 5. Two generations of analysis, and why both stay

`Discharge.lean` holds §5's per-aspect approximations — `κ`, `ident`, `adm`, `admA`, `μSyn` —
with the separation predicates `SepV` and `SepA`, each a **two-disjunct** disjunction (labels
disjoint, *or* admissible sets disjoint).

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
  never be separated by `SepV` (both `κ`s are `[map]`, both `adm`s are `⊤`, so neither disjunct
  is available) — and that is the point.
- Restate the discharger on `SepJV` and the pair *does* separate, while `select` still attempts
  both options, so (U) genuinely fails. **The premise gets stronger and the theorem becomes
  false.** The witness is two objects with the same names and different field terms
  (`objReqStr`, `objReqNum`), both derivable, both closed, both lawful — so no other premise is
  what declines them.

**The boundary, and it is sharp:** the `object` row is the *whole* obstruction.
`admitV_Adm_nonObject` and `admitA_AdmA_nonObject` are the containments the discharger needs,
and they hold from exactness alone for every term whose `specOf` is `none` — which is every term
but an `object`.

So: do not delete `Discharge.lean`, and if you sharpen an `adm` row at a container, check
whether you have just broken a discharge that was relying on the slack. `scripts/blast_radius.lean`
exists to cost exactly this question and prints the four-way partition (old only / new only /
both / neither).

---

## 6. The instruments, and what each is blind to

The blind spot is the part that matters; the check is the part you can read off the script.

**`#assert_axioms_all`** (`Axioms.lean`) — the advertised base is
`[propext, Quot.sound, Calculus.Double, Calculus.numericHost]`, four names where there were
seven, because the `Double` facts now project out of one `NumericHost` interface rather than
being five independent assertions. It is a *build error*, not an assertion in prose; that is the
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
must occur somewhere in `Calculus/`, with an `EXPECTED` table carrying a reason per deliberate
exception (and failing if an entry there stops being cited, so the table cannot rot quietly).
**Blind spot, stated in `7a91de8`: a count is not a name.** It cannot see "five theorems share
`term_depth_wf`" being false while all five names exist. It also clears a dotted name
component-wise, so a dotted citation passes whenever both halves occur anywhere.
**This document is in its `CURRENT` list.**

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
hits into 57 code sites, and there was no shortcut. The control experiment is in its docstring;
`86d3a42`'s commit message claimed otherwise and is wrong.

One more blind spot common to all five: **none of them looks at `src/`.** `Vectors.lean` is the
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
indexed-family alternative (`Attr : Nat → Type`, which the kernel does accept, unlike the
subtype) is priced in `docs/codec-audit.md` §12.4.

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

**Non-malleability.** `Malleability.lean` records that we deliberately fail it, and why the
relational-format proposal that would have entailed it is refuted (`fmt_forced`): `Fmt` is the
fibre of `p`, so a relational presentation is the same model addressed by fibre, and one cannot
shrink a fibre to buy the agreement clause without losing completeness.

---

## 8. Open architectural questions

One line each, with the number or name that decides it.

**The value/attribute doubling.** Nearly every analysis declaration has an attribute twin, and
the question is whether the two sides should be one parametrised development. A probe found the
side-split stays **local** — it does not thread through the codec algebra — and that the
mergeable bulk sits in `Exactness.lean`. `set` is the standing exception: its attribute side is
a choice among three wire constructors rather than one prism, argued at the section note above
`carriedCodec` (`Combinators.lean:1213`).
*The numbers I was handed — 82 twin pairs, ~45 mergeable — are recorded nowhere in the repo and
I could not reproduce them.* A naming-based count over 1296 declarations (twin = `X`/`XA`, or a
`V`→`A` or `Value`→`Attr` substitution) gives **69 pairs, 32 of them in `Exactness.lean`**;
loosening the transform to include the write/read `_e`/`_p` split gives 100. Treat 82/45 as
unverified and re-measure before costing the merge.

**`select` over `List.attach`.** `select` filters a list of options and acts through the one
that answers alone, and `List.filter` hands back a bare element — so every proof that needs "the
surviving option came from *this* term" recovers it by hand (`List.mem_of_mem_filter (by rw [hf];
simp)`, at roughly ten sites), and the filter-over-map commutation needs its own lemmas
(`filter_map_AdmSpecs`, `filter_AdmSpecs`). Attaching membership would carry it through. Queued
as a standalone strict improvement; it touches `Combinators.lean`, deep in the graph, so it needs
a clean build window. **Recorded only in the handoff, nowhere in `docs/`.**

**`adm (.literal .number ls)` is not exact** — it is `inL`, missing the `Numeral.WF d.toDec`
gate. Note the exact row already has it: `AdmLit` is `inL` conjoined with the numeral condition,
which is why `Adm_exact` covers the literal. So this is a defect in the *older* generation only.
Two routes, and the second is a **fidelity call, not a cleanup**: tighten the row (breaks
`adm_literal_num`'s `rfl` and every `SepV` over literals), or make `GroundKind.number`'s carrier
the gated subtype, which is probed, works, and deletes `LiteralD` entirely — at the cost of
making `literalN_holds_what_it_cannot_write` unstatable. That witness records a defect in **§3's
rule**, not in our constructor.

**`admits`' violation list and wiring it into `union`'s resolver** — both behaviour changes in
`src/`, both the user's call. See the handoff.

---

## 9. If you change something

- New module under `Calculus/` → reachable from `Axioms.lean` (§1).
- New stratum in the term family → all seven companions (§2).
- New term recursion → `term_depth_wf`, and new inequalities beside `Term.depth` (§3).
- New analysis row → prefer asking the codec over describing the set (§4b); then prove its
  exactness clause, because a missing row is a silent `⊤` and `⊤` is sound.
- Sharpening a `⊤` row at a container → check what was relying on the slack (§5), and cost it
  with `scripts/blast_radius.lean`, not with grep.
- Citing a Lean name in `README.md`, `FIDELITY.md`, `VOCABULARY.md`, this file, or
  `docs/codec-calculus.md` → `python3 scripts/name_drift.py` must exit 0. A count in prose is
  not covered; verify counts by hand.
- Deleting a declaration → snapshot `scripts/unreferenced.lean` before and after and read the
  *difference*.
- Touching a normative document, the advertised axiom base, or `src/` behaviour → that is the
  user's decision. Deliver the measurement and stop.
