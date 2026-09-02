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
| How a proof is meant to read | `VOCABULARY.md` |

One standing rule from `WORKING-AGREEMENT.md` governs this file too: **record why, not what**,
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

**The pattern, so a fifth stratum is written correctly.** A stratum owes eight companions —
seven kinds, with the admission row counted on both sides — and `db444e3`'s own table is the
list. `Term` and `Body` have all eight; `Field` has no spec projection (`Body.spec` matches on
the field inline) and `Rest` has neither spec nor tags, because a policy answers to no name and
carries no tag. So the two name-reading projections are owed only by a stratum that holds
names; the other five are owed unconditionally:

| Companion | For `Body` | Why it is owed |
| --- | --- | --- |
| a depth clause | `Body.depth` | §3's termination measure must see through it (§3 below) |
| a denotation clause | `bodySem` | `denote` must dispatch without a case split at the use site |
| a spec projection | `Body.spec` | `select` counts an object option by its names, not its contents |
| a member/tag projection | `Body.tags` | the union residues read this, not the payload |
| an admission row, per side | `AdmBody`/`AdmABody` | exactness is per-row; a stratum with no row cannot be exact |
| a premise carrier | `ObligationsBody` | semantic side conditions are structural, not global |
| a law exemption | `MPOkBody` | `legacy`'s (MP) exemption propagates through the stratum |

Miss one and the failure is not a build error but a silent `⊤`: the analysis will still be
*sound* and will have stopped saying anything. That asymmetry is the subject of §5.

`Body`'s projections (`Body.fields`, `Body.at`, `Body.rest`) are written by hand — a `mutual`
block admits no `structure`. Rows needing all three still pattern-match on `.mk`, which keeps
the equation compiler's iota reductions available.

### Where a side condition goes, and why there are three places

The first thing to settle when adding a rule, and `Typing.lean`'s module header states it —
`Typed` keeps only the "*syntactic and fuel-free*" premises:

| A premise that is… | goes in | consumed by |
| --- | --- | --- |
| decidable from the term | `Typed` (`Typing.lean`) — `(union)`'s is `hD : DIncomp Ts` | the judgement itself |
| about what a codec *does* — `e`, `p`, an iso, a resolution | `Obligations` (`Soundness.lean`) — `UAtAct opts`, `IsoCancels`, `ReadsCoherently` | both soundness theorems |
| §2's `(MP)`, which `legacy` is exempt from | `MPOk` (`Soundness.lean`) — `.legacy _ _ => False`, structural elsewhere | `soundness` alone |

`MPOk` is not a rule premise at all: it is a predicate on the *term* saying the derivation is
legacy-free, and it is the single hypothesis separating `soundness_core` (`LawfulCore` — (R),
(C), (W)) from `soundness` (`Lawful`, adding (MP)). Choosing wrong is not a build error: a
semantic premise in `Typed` makes the judgement undecidable, a syntactic one in `Obligations`
becomes a burden every caller carries. All three recur structurally, which is what the
companion table's last two rows owe. (That header carried two stale spots of exactly this
kind, invisible to the guards because no name was dangling: the semantic premises were called
"fuel-indexed" where `Obligations` says "**Structural, and no longer fuel-indexed**", and
`literalS`/`literalN` were named as live constructors though `GroundKind` had retired them.
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

`term_depth_wf` is the shared `decreasing_by` tactic. **<!-- count:term_depth_wf_users -->Three<!-- /count -->** declarations use it, all in
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
decidable premise. §2's rule about a new stratum costing all eight companions is the same
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
hand. And it would strip the arbitrary pair out of `adm_custom`, `admA_custom` and
`adm_custom_exact`, whose content *is* the arbitrariness — `adm_custom`'s docstring says so:
"not a bound on the pair but the pair itself". Last, it is the one instance of this move that
crosses a stated decision rather than realizing one: `Term.lean:11` says `custom` "carries its
pair as data; its *laws* are premises of the typing rule (§3), exactly as in the doc", and
`Typing.lean`'s header puts the *syntactic* premises in `Typed` and the *semantic* ones —
naming `(custom)`'s laws — in `Obligations`, "stated where they can mention the denotation".
`(held)`'s premise-to-index move (`c66d493`) was the syntactic kind and landed; this is the
semantic kind. **The criterion is necessary, not sufficient — measure the site count too.**

### 4b. A row asks its codec instead of describing it

The analysis tables in `Discharge.lean` (`κ`, `ident`, `adm`, `admA`) approximate what a codec
writes and reads. A row can either *describe* the set or *call the codec and ask*. `custom`
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
| `admA .legacy` | `admA t a \|\| (r a).isSome` — the subterm's row, or `r` | "`extendRead` widens `p` past the subterm's admissible set, which is the direction `admA` bounds" |

**The last row is the odd one and the difference matters.** It does not ask its codec; it names
both of `r`'s and the subterm's channels and takes the union, keeping the subterm's
*over-approximation* rather than reaching past it. Asking was probed — the row
`((denote (.legacy t r)).p a).isSome` is exact and compiles at a one-line cost — and **refused**,
because it sees through `admA (.object _) = ⊤`, which §5 records as load-bearing slack rather
than looseness. Two objects cannot be separated by `SepA` (both rows `⊤`); wrapped in a `legacy`
they could be, while `select` still attempts both options, which is `not_uAtCan_of_sepJ`'s
failure one wrapper out. So this row is as sharp as it can be *without* becoming unsound, and
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

`Combinators.lean` is <!-- count:combinators_lines -->4008<!-- /count --> lines of the tree's
<!-- count:tree_lines -->17551<!-- /count -->, and this is its organizing idea; without it
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
  §9's twin question is askable at all: the doubling is in the analyses, not the algebra.
- `set` is the one deliberate non-instance: its attribute side is a choice among three wire
  constructors rather than one prism (`setCodec`, `Combinators.lean`), so its inversion names all
  three families (`setCodec_p_eq`).

### 4d. The guards exist because prose does not typecheck

Every instrument in §6 was built after a description drifted from what it described: an axiom
claim in prose (`#assert_axioms_all`), a `@[simp]` attribute asserting a behaviour that had
stopped being true (`#lint_calculus`), a citation of a deleted name (`scripts/name_drift.py`), a
regex passed off as a reachability measurement (`scripts/unreferenced.lean`), a grep passed off
as a refactor estimate (`scripts/blast_radius.lean`). None of them was added speculatively.

---

## 5. Generations of analysis: two that stay, one that does not pay

`Discharge.lean` holds §5's per-aspect approximations — `κ`, `ident`, `adm`, `admA`; the fifth
aspect, `μSyn`, is `Denote.lean`'s, because `denote` needs the member index itself — with the
separation predicates `SepV` and `SepA`, each a **two-disjunct** disjunction (labels
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
whether you have just broken a discharge that was relying on the slack.

**And do not expect `scripts/blast_radius.lean` to cost that**, which this section used to say
it did. Measured on the `admA .legacy` sharpening (§4b): the four-way partition is *identical*
before and after — 75 old-only, 19 both, 136 new-only, 1433 neither — and the old-only set is
unchanged name for name. It has to be: the walk measures dependence on a **name**, and
sharpening a row changes a definition's *body*, not who depends on it. The instrument costs
deleting or replacing a declaration; it is blind to a row that stays and says something
different. What caught the consequence was the build (`AdmA_le_admA`'s `legacy` case stopped
being `rfl`), and what caught the *hazard* was reading this section. Neither is an instrument.

### And a third machine, `Orth`, which does not pay — measured

`Orthogonality.lean` is the fourth-largest file at <!-- count:orth_file_lines -->969<!-- /count --> lines: a decidable certificate for a
fragment of (U), over-approximating each term's occupancy per side (`occV`/`occA`) and
certifying a pair whose occupancies are disjoint, `by decide`. **Measured against what it
replaces it does not pay**, and its own by-phase table is the measurement — the <!-- count:orth_total_theorems -->25<!-- /count --> hand
discharges it names, 23 as rows and 2 in the prose beneath them, out of a
<!-- count:sep_family -->32<!-- /count -->-theorem `sep*`/`uAtCan_*`/`uAtAct_*` family:

| | theorems | lines of proof |
| --- | --- | --- |
| reachable by `Orth` itself — phase *slot* | <!-- count:orth_slot_theorems -->6<!-- /count --> | <!-- count:orth_slot_lines -->70<!-- /count --> |
| reachable only through `Separates`, the `Prop` interface — phase *alternatives*, where `DecidableEq Double` makes a `Bool` test noncomputable | <!-- count:orth_alt_theorems -->7<!-- /count --> | <!-- count:orth_alt_lines -->75<!-- /count --> |
| unreachable on principle — an arbitrary `q` or `f`, a different constructor, `SepJA`'s member disjunct, or `UAtCan` itself failing (`uAtAct_array_literals`) | <!-- count:orth_unreach_theorems -->12<!-- /count --> | <!-- count:orth_unreach_lines -->168<!-- /count --> |

*Re-measured, and the previous version of this table was wrong in three ways.* It said 23
where the section names 25; it counted 11 unreachable theorems against a line total of 162
that silently included a twelfth (`uAtAct_array_literals`, 53 lines, named in the row's own
description but in no row); and `uAtCan_number_opaque` (24 lines) was reachable — the pair
form of two *slot* discharges, and `orth_number_opaque` certifies it `by decide` — while
appearing in no row at all. The reachable total is therefore **<!-- count:orth_reachable_lines -->145<!-- /count --> lines, not 116** — the
verdict below does not move, but it was being stated with a number 24 lines too kind to
the hand proofs and 24 too harsh on `Orth`.

And **nothing was deleted** — `6daa5e3`, `0335cdb` and `5763b6d` touch only the new module and
two import lines — so <!-- count:orth_file_lines -->969<!-- /count --> lines stand *beside* the <!-- count:orth_reachable_lines -->145<!-- /count --> they could replace. It stays anyway,
because its value moved. The classifier framing did not pay; but confluent admission —
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
must occur somewhere in `Calculus/` — where *Lean-looking* means it carries a `_` or a `.`, so a
one-word citation (`Adm`, `Orth`, `Fmt`) is never checked at all — with an `EXPECTED` table
carrying a reason per deliberate
exception (and failing if an entry there stops being cited, so the table cannot rot quietly).
**And the docstring check is partly vacuous, which is a defect in the extension not the
original.** `occurring()` builds its source set from the raw file text, comments included, so a
name appearing *only* in a docstring is present in its own evidence and clears itself. Adding
`Calculus/*.lean` to `CURRENT` (`6a90359`) therefore proves less than that commit's message
claims: "none of the 763 dangles today" was established by a check that cannot see the case it
was added for. Demonstrated — `literalN_holds_what_it_cannot_write` was cited in three
docstrings and here while the declaration had been renamed to
`literalNRule_holds_what_it_cannot_write`, and the guard passed clean; the citations are fixed,
the guard did not find them.

Stripping comments from the source set was tried and **over-corrects**: it then rejects
legitimate citations of things deliberately *absent* from the code — `Classical.choice` above
all, which the whole axiom base exists to keep out, plus mathlib names and Lean keywords
mentioned but not used. Doing it properly means extending `PRELUDE` and `EXPECTED` for roughly
twenty such names, which is its own piece of work and not this arc's. Reverted, recorded here.

**Blind spot, stated in `7a91de8`: a count is not a name.** It cannot see "five theorems share
`term_depth_wf`" being false while all five names exist. It also clears a dotted name
component-wise, so a dotted citation passes whenever both halves occur anywhere.
**This document is in its `CURRENT` list.**

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
grep without a limit, or count it.

The second is real: **anonymous-constructor patterns.** Changing `Typed.held`'s arity
(`c66d493`) missed a consumer because `typed_μSyn` destructures it as `| _, _, _, .held h' _ =>`,
which matches neither `Typed.held` nor `@held` nor `case held`; only the build found it. When
costing a constructor change, grep the bare `.<name>` as well as the qualified form, and expect
the arity to be implicit in a positional match. The control experiment is in its docstring;
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
| **(c)** cannot express it | a construction-time **refusal**, a test that pins it, and a written **reason** | the reason is the part that gets skipped and the part that matters: an unexplained gate is indistinguishable from an un-migrated one, and the next reader "fixes" the signature |

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

**So a guarantee that must be a gate in one target may be structural in another.** The three
cases are re-answered per target, at the time that target is certified — not in advance, and not
as a reason to shape the model around one language. The model's job is to make the guarantee
structural *in the model*; how much each target carries is that target's certification, which is
a separate and currently unmet obligation.

---

## 9. Open architectural questions

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
  `adm`/`admA` 45 at 0.47, `AdmLit`/`AdmALit` 14 at 0.33, `Adm`/`AdmA` 38 at 0.58.

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
on the element's own gate, `LiteralD` is deleted, and `adm`'s literal row and the joint row are
the same function (`adm_literal_eq_Adm`) — which makes the older generation exact at this row
with **nothing added to it** (`adm_literal_exact`). The alternative route, tightening the row,
would have broken `adm_literal_num`'s `rfl` and every `SepV` over literals; the carrier route
broke `adm_literal_num`'s `rfl` too, and nothing else.

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
lookup is and not a lever on the model. `src/` is not aligned and that is a separate call
(`codec.ts:4415` records multi-tag options as deliberate).

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

**§6's commutativity row is the adjacent transposition, not the permutation.**
`equiv_altCodec_swap` proves the adjacent case, which generates every permutation — but the
`List.Perm` lift is not written down, so the table's "all" is worth what one transposition is
worth. `README.md` was always honest about this and the change log's "twenty of twenty" was
not. The row also inherits the `≡`-is-not-transitive caveat, which bounds what a table of
rewrites licenses at all. The `List.Perm` lift is the next probe.

**`admits`' violation list and wiring it into `union`'s resolver** — both behaviour changes in
`src/`, both the user's call. See the handoff.

---

## 10. If you change something

- New module under `Calculus/` → reachable from `Axioms.lean` (§1).
- New stratum in the term family → all eight companions (§2), counted per side.
- New rule → put each premise in one of the three places, `Typed`/`Obligations`/`MPOk` (§2).
- New term recursion → `term_depth_wf`, and new inequalities beside `Term.depth` (§3).
- New analysis row → prefer asking the codec over describing the set (§4b); then prove its
  exactness clause, because a missing row is a silent `⊤` and `⊤` is sound.
- Sharpening a `⊤` row at a container → check what was relying on the slack (§5), and cost it
  with `scripts/blast_radius.lean`, not with grep.
- Citing a Lean name in `README.md`, `VOCABULARY.md`, this file, or
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
