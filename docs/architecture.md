# Architecture of the Lean development

What this system is. Read this before changing anything under `Calculus/`.

This file carries no count, no line number and no measurement. A count is short lived: it belongs
in the commit that measured it, in `defects.md` where it pins an issue, or in the output of a
guard. What is here is the structure, the invariants, the models and the mechanics of an
operation, which are the things that stay true across passes.

This file cites no section number, in this document or any other, so that a renumbering cannot
make it wrong. It names declarations and files instead.

A backtick here means a Lean name that `Calculus/` defines. A host identifier is written as a
path, as a call, or in prose.

| For | Read |
| --- | --- |
| The system this arc is building toward | `docs/architecture-v2.md`, which does NOT govern yet |
| The rules, normatively | `formal/docs/blueprint/src/content.tex` |
| Future states, and what decides each | `docs/roadmap.md` |
| Known, suspected and partially mitigated issues | `docs/defects.md` |
| What changed and why | `git log` |
| Module table and how to build | `formal/README.md` |

---

## The epistemic structure

This repository is two developments and one bridge between them.

`src/` is a published TypeScript library. `Calculus/` is a Lean model of part of that library.
The bridge is a generator in `src/codec/lean.ts` that emits Lean theorems from encodes the library
actually performed, and the Lean kernel decides whether the model agrees.

The three carry different warranties, and keeping them apart is the whole discipline.

- **The model proves.** A theorem in `Calculus/` is checked by the kernel against an advertised
  axiom base.
- **The bridge checks agreement.** A vector is a proposition about one operation the library ran.
  Elaboration is what verifies it. Comparing the generator against output the generator produced
  verifies nothing, because a stale generator agrees with its own stale output.
- **A written premise is neither.** Where the model discharges an obligation the host cannot
  check, the guarantee is a sentence on both sides and no instrument is looking.

The asymmetry that governs the analyses: **a missing analysis row is sound and says nothing.**
An approximation that answers "everything" is always correct and never useful, so the failure mode
here is silence rather than error, and silence does not fail a build.

---

## The layering, and what the imports guarantee

`Calculus/` has two layers. The generic layer states the codec algebra for every universe. An
instance layer gives one universe its carriers and the facts of those carriers. DynamoDB is one
instance, and JSON is a second instance.

**The generic layer** is the namespace `Calculus.Alg`, in the modules whose names start with `Alg`.

| module | states, for every universe |
| --- | --- |
| `Alg/Codec.lean` | the record `Codec` and its laws `Lawful` and `LawfulCore`, over the carriers `V`, `A` and `M` |
| `Alg/Combinators.lean`, `Alg/Relations.lean` | the combinators, the join by the first admitter, the order, the equivalence, `Compat`, `Canon` and `Sub` |
| `Alg/Lists.lean`, `Alg/Positions.lean`, `Alg/Maps.lean` | the traversal and `entrywise`, the positional theory, the image of a function over a key set, and `MapOf`, which keeps the namespace `Calculus` |
| `Alg/Containers.lean`, `Alg/Recursion.lean` | `listCodec` and `objectCodec` over prisms, and `muCodec` over two depth functions |
| `Lang/Term.lean`, `Lang/Typing.lean` | the term family over a signature, `denote`, the guard, `Typed` and `Obligations` |
| `Lang/Guarded.lean`, `Lang/Sound.lean`, `Lang/HeldFree.lean` | `contractive_body`, `soundness`, and `compat_of_HF` |
| `Lang/Meet.lean`, `Lang/MeetRows.lean` | the class `Leaf`, the structural meet `Term.meet` over a signature, and the rows of the meet that read no admission |
| `Lang/MeetV.lean`, `Lang/MeetA.lean`, `Lang/MeetWrites.lean`, `Lang/MeetTyped.lean` | the theorems of the meet: `Adm_meet`, `AdmA_meet_both`, `meet_writes`, and `typed_meet` |

`Rows.lean` is generic too, in the namespace `Calculus`. It states the row combinators of the
analyses over one carrier type, and each side of the pair instantiates it.

`Lawful` takes the member of an attribute as a parameter. (W) reads that function, and no law
reads more of the store.

**A universe is a signature in two parts.** `Syn` holds the syntax: the values that a `held`
maps, the primitives, and the predicates. The class `Sem` over a `Syn` holds the meaning: the
stored carrier, the member, the codec of each primitive, the evaluation of a predicate, the
depths, the formers and the top. The term family reads `Syn` alone. The compiled code of a
function over `Term S` takes `S` as a real argument, because `casesOn` takes the parameter of the
family as a real argument. The semantic fields are `noncomputable` at DynamoDB: `inL`, `setCodec`,
`Ω` and `Pred.eval` are. One structure would make each function over terms `noncomputable` at
DynamoDB, `Term.meet` and `Term.hasVar` included. The split keeps a term as data that code can
compute with.

**A universe owns these facts, and the generic layer owns none of them.**

| the fact | the field | at DynamoDB | at JSON |
| --- | --- | --- | --- |
| the carriers | `Syn.V`, `Sem.A`, `Sem.M` | `Value`, `Attr`, `Member` | `Json`, `Json`, `JMember` |
| the member of an attribute | `Sem.member` | `Attr.member` | `Json.member` |
| the primitives and their codecs | `Syn.Ground`, `Sem.ground`, `Sem.lawful_ground` | `Ground`, `groundCodec` | `JMember`, `ground` |
| the predicates | `Syn.Pred`, `Sem.eval` | `Pred`, `Pred.eval` | a function on `Json` |
| the depths | `Sem.dV`, `Sem.dA` | `Value.depth`, `Attr.depth` | a constant |
| the list and map formers | `Sem.list` as a `ListF`, `Sem.map` as a `MapF`: a prism on each side | `dList`, `dMap` | none |
| the set former | `Sem.set` as a `SetF`: a lift and its laws | `dSet`, over `setCodec` | none |
| the obligation on a set element | `SetF.elem`, which `SetObl` reads | `SetElem` | none |
| the top | `Sem.top`, `Sem.lawful_top`, `Sem.topHeld` | `Ω`, `HOpaque` | `idCodec` |
| the top laws | `TopLaws`, a class with one instance for each universe | `Ω_topLaws` | `id_topLaws` |
| the admission row of a primitive, and its exactness | `PrimAdm`, `PrimAdmA` | `inBase` and `AdmLit`, `inBaseA` and `AdmALit` | the kind test |
| the leaf meet: two primitives, a primitive and the top, two predicates | `Leaf` | `dynLeaf`: `Ground.meet`, `Ground.meetTop`, `Pred.isData`, `Pred.meetM` | `jsonLeaf`: one kind |
| the laws of the leaf meet | `LeafAdm`, `LeafAdmA`, `LeafWrites` | `dynLeafAdm`, `dynLeafAdmA`, `dynLeafWrites` | `jsonLeafAdm`, `jsonLeafAdmA`, `jsonLeafWrites` |
| the set laws that the meet reads | `FormerAdm`, `FormerAdmA` | `dynFormerAdm`, `dynFormerAdmA` | `jsonFormerAdm`, `jsonFormerAdmA` |
| the former class of each value and attribute, and where each former lands | `Shapes` | `dynShapes`: the root constructor | `jsonShapes`: every value is a primitive |

A former is an `Option`. A universe without a former denotes the term of that former as the
bottom. `TopLaws` is outside `Sem`, because soundness and the judgement read none of its laws. Only
the held-free theory and the read side of the meet read them. `PrimAdm` and `PrimAdmA` are outside
`Sem` for the same reason: only exactness reads them.

**The meet is structural, and a universe supplies its leaves.** `Alg.Term.meet` has one row per
constructor of the left operand. Only two rows read a fact of a universe: a primitive met with a
primitive or with the top, and a predicate met with a predicate. `Leaf` holds those two meets and
the test for a predicate that the meet can carry. `Leaf` is outside `Sem` and holds computable
fields only, so the meet stays computable, and the kernel evaluates a closed pair. At DynamoDB,
`Term.meet` is the generic meet at `dynLeaf` and at the closed pairing `pair0`.

**The meet reads two open terms at a pairing of their binders.** `p i j = some k` says that the
left variable `i` and the right variable `j` are the variable `k` of the answer. Two variables
meet where the pairing names them one binder, and a variable beside a constructor refuses. Two
recursive terms meet at the recursive term of their bodies met, with the two new binders paired.
A recursive term beside another constructor unfolds, and its binder pairs with nothing. The set
row refuses an element that reads a variable, because the set laws are stated over closed terms.

**The theorems of the meet hold at every signature, from the laws of the leaves and the formers.**
`Alg.Adm_meet` says that the meet admits exactly the values that both factors admit, under every
three environments that agree with the pairing (`PairedV`). `Alg.AdmA_meet_both` says the same of
attributes (`PairedA`), and that the meet reads an attribute as each factor reads it. `Alg.meet_writes` says that a member the meet names is each factor's member.
`Alg.typed_meet` says that the meet of two derivable terms is derivable, and reads no law. Each
proof recurses on the left operand, as the meet does. The laws are classes outside `Sem`, because
only the theorems of the meet read them. `LeafAdm`, `LeafAdmA` and `LeafWrites` say that each
leaf answer is exact. `FormerAdm` and `FormerAdmA` say that the set former carries an element meet
to a set meet. Each read-side law states a read domain only. The reading agreement at a leaf row
and at a set row is no law of a universe: each term of the row is held-free, so each lies below
the top, and below one bound the read domains decide the reads (`Alg.readAgree_of_sub`,
`Alg.admAAt_of_HF`). At DynamoDB, a leaf law is a fact about `inBase` and `inL`, and a set law is
a fact about `setCodec`. The DynamoDB theorems, such as `Adm_meet` and `AdmA_meet`, state the generic
theorems at the DynamoDB names. At JSON, two kinds meet where they are one kind, and each set law
holds because the signature has no former and both sides admit nothing.

**A universe is a container, and the disjointness of two formers is a theorem.** The carrier of a
universe is the W-type of a container, and the member of a value is its root shape. Each former
lands in one class of root shapes: a primitive, a set, a list or an object. The classes of distinct
formers are disjoint, because the carrier is a coproduct. `Shapes` gives the class of each value
and of each attribute, and the landing fact of each former: a primitive codec, the set lift, the
list prism and the map prism. So two formers in different classes share no value and no attribute
(`Shapes.prim_set`, `Shapes.prim_setA` and their companions), and the catch-all rows of the meet
read those theorems. A set and a keyed map are quotient containers, so the set laws stay a class
of each universe. At DynamoDB, the class of a value or an attribute is its root constructor.

**The set former is a lift, and not a prism.** The list and map formers are prisms from `List`
and `MapOf` of the carrier onto the carrier. A set former cannot be such a prism: the kernel
refuses a `Finset` of the datatype that it declares, as a nested occurrence. So `SetF` carries a
codec transformer `lift` with its law, its agreement one layer down, and its held set. At
DynamoDB the lift is `setCodec`, over the three wire-set constructors of `Value`.

**The theorems of the algebra hold at every signature.** `Alg.soundness` proves `Lawful` for each
closed typed term whose obligations hold, in any universe. The universe supplies the laws of its
primitives, of its formers and of its top, and the generic combinators supply the rest.
`Alg.compat_of_HF` proves two held-free terms compatible from `TopLaws` and a canonical top,
when the second term is lawful.

**The instance names the generic declarations.** At DynamoDB, `Codec` and `Lawful` are
abbreviations at the DynamoDB carriers, and `Term`, `Typed` and `Obligations` are abbreviations
at `dynSyn`. A `match_pattern` abbreviation keeps each constructor spelling, such as
`Term.string` and `Term.literal`. `Term.casesD` keeps the case tags `base` and `literal`. A
cited DynamoDB theorem, such as `soundness` or `Adm_exact`, states the generic theorem at the
DynamoDB names.

**The DynamoDB `denote` is the generic `denote`, and a simp set gives its rows.** `denote`,
`μSyn`, `Adm`, `AdmA` and their companions are abbreviations of the generic functions, typed at
`Term`. So a constructor argument such as `.base k` resolves in the DynamoDB namespace. A proof at
DynamoDB reads `baseCodec`, `setCodec` and `listCodec` by name. A generic equation states a row
through the signature, and `simp only [g]` unfolds an abbreviation `g` and reads no other
equation. So each row at the DynamoDB constructors is a `rfl` lemma in a registered simp set:
`denote_rows`, `μSyn_rows`, `Adm_rows` or `AdmA_rows`. A proof names the set where it named the
function. `rw` matches the head symbol, so a lemma stated at an abbreviation does not rewrite the
generic head. `exact` compares up to unfolding, and accepts both.

**Exactness holds at every signature.** `Alg.Adm` and `Alg.AdmA` give a row per constructor, and
`Alg.Adm_exact` and `Alg.AdmA_exact` prove each row equal to the domain of `denote t`, from the
exactness of the primitive rows alone. A universe states the primitive rows, so a verdict at a
primitive reduces without the codec. The DynamoDB `Adm` and `AdmA` are the generic rows, and
read their DynamoDB rows from a simp set, as `denote` does.

**The other analyses are DynamoDB tables.** `Meet`, `Separation`, `Slice` and the certificate read
the constructors of the DynamoDB carriers. No generic form of them exists. Inside the DynamoDB layer the import graph is an almost-linear spine: `Domain`, then
`Codec`, then the combinator algebra at the DynamoDB carriers as `Prisms`, `Products`, `Objects`,
`Sums`, `Carriers`, `Lawful` and `Frontier`, and `Term`, then `Denote`, `Typing`, `Soundness`,
then `ExactV`, `ExactA` and `Separation`, then `Orthogonality`, with `Axioms` as the sink. Each instance module imports the
generic module that it instantiates. Several analyses sit off the spine: no module but
`Axioms.lean` imports them. `Malleability` is one of them: a lawful codec has one attribute per
value (`Lawful.fmt_subsingleton`).

**What the imports guarantee.** No generic module imports `Domain` or another instance module,
directly or through its imports. So a generic declaration that cites a fact of the DynamoDB
carriers is an unknown identifier, and the build fails. `JSON/Basic.lean` imports the generic layer and
no DynamoDB module, so `Calculus.Value` is an unknown identifier under `import Calculus.JSON.Basic`. The
laws, the combinators, the join and soundness are therefore facts of the algebra, and not facts of
one store. The gate runs `scripts/layer_order.py` on the import lists. The guard fails when a
generic module imports a universe, when one universe imports the other, or when a module imports
a higher layer.

**A second property of the graph is checked.** `Axioms.lean` walks the environment, and the
environment is what `Axioms.lean` imports, which is a hand-maintained list. A module that nothing
on that list reaches is silently unguarded. `scripts/guard_reach.py` fails when any module under
`Calculus/` sits outside the transitive closure of the guard's imports. `Axioms.lean` imports
`JSON` for this reason: no other module under `Calculus/` imports it.

So a new module under `Calculus/` must be reachable from `Axioms.lean`. `Axioms.lean` cannot
import the aggregator instead, because the aggregator imports the guard, and inverting that would
let the default build run with no guard at all.

Lean catches a cycle, and `scripts/layer_order.py` holds the order of the layers. Nothing else
about the graph is enforced.

---

## The term family, and what a stratum owes

`Term S`, `Body S` and `ObjectSlot S` are inductives in one `mutual` block over a signature `S`,
in `Lang/Term.lean`. At DynamoDB, `Term`, `Body` and `ObjectSlot` are their abbreviations at
`dynSyn`. **The point of the split is negative: no `Term` position accepts an `ObjectSlot`.** A
slot is not a term, so a nonsensical term is a type error rather than a rule somebody must
remember to refuse.

`Body` bundles the object payload — the declared key set, the slot at each key, and the one open
block — into one thing. Two consequences are the reason to do it again:

- Every table over terms gets a one-argument object row that delegates to a `Body` companion.
  Threading the payload's parts by hand is what made them agree by convention rather than by type.
- A `Finset Name` together with a function off the membership subtype makes the no-duplicate-keys
  premise disappear. Both a repeated name and two orderings of one object stop being
  representable. `ObjectSlot` sits in the function's codomain, which is strictly positive.

A primitive is one constructor, `prim`, over the primitives of the universe. At DynamoDB the
primitives are `Ground`, with the constructors `base` over a `GroundKind` and `literal`, so a
table over terms states every ground base in one row. `opaq` denotes the top of the universe.

`ObjectSlot` carries the current-schema rule only. A required slot remains required on both
current-schema sides. An alternate reader is `Codec.extendRead`, over the codec of one current
`Term`.
Structural operations, including `meet` and union certification, operate on `Term`. The operations
cannot observe or propagate an alternate reader.

`Body`'s projections `Body.fields`, `Body.at` and `Body.wild` are written by hand, because `Body`
is an `inductive` with one constructor. The `mutual` block of `Term`, `Body` and `ObjectSlot` also
elaborates with `Body` as a `structure`, and with a `MapOf ObjectSlot` argument in place of the key
set and the slot function. `Body` takes neither form. Rows needing all three match on the
constructor, which keeps the equation compiler's reductions available.

**A stratum owes a companion in each of these places.** Miss one and the failure is not a build
error but a silent "everything": the analysis stays sound and stops saying anything.

| Companion | For `Body` | Why it is owed |
| --- | --- | --- |
| a depth clause | `Body.depth` | the termination measure must see through it |
| a denotation clause | `bodySem`, generic, with its DynamoDB row in `denote_rows` | `denote` must dispatch with no case split at the use site |
| a spec projection | `Body.spec` | a slice reads an object option's names and literals off the spec |
| an admission row, per side | `AdmBody` and `AdmABody` | exactness is per row; a stratum with no row cannot be exact |
| a premise carrier | `ObligationsBody` | semantic side conditions are structural, not global |
| an emitter clause | the object row of `src/codec/lean.ts` | the bridge writes terms in this language, and a constructor it cannot spell breaks it |

The depth clause, the denotation clause and the premise carrier are generic, and each universe
inherits them. The admission rows are generic too. The spec projection is a DynamoDB table. The DynamoDB rows
of `denote` in `denote_rows` are owed too. A missing row fails only a proof that reads the
row.

The spec projection is owed only by a stratum that holds names. A policy answers to no name.
Every other row is owed unconditionally.

The spec projection separates a name's presence from what the name holds. The split is
Rémy's, from the 1989 record and variant extension of ML. A field type carries presence
beside the value type, so an analysis keeps exact negative information about a name.
`litSubAt` reads both: the one current-schema presence fact, and the literal a name is pinned
to. No reader reads a codec.

The emitter clause is owed for the same reason as the rest: the bridge is part of the
correspondence, and a stratum whose shape the emitter cannot spell produces committed vector
output that typechecks against nothing.

---

## Where a side condition goes

The first thing to settle when adding a rule. `Typed` keeps the syntactic, fuel-free premises
only.

| A premise that is | goes in | consumed by |
| --- | --- | --- |
| decidable from the term | `Typed` | the judgement itself |
| about what a codec does: its write half, its read half, an iso, a resolution | `Obligations`, as `PairwiseCompat` and `IsoCancels` are | `soundness`, and `extendRead_lawfulCore` through it |
| a rule of one universe on a set element | the `elem` field of the universe's `SetF`, which `SetObl` puts in `Obligations` | no law: `soundness` takes it as a premise and does not read it |

`Term` has no alternate reader. Therefore `soundness` proves `Lawful`, which is retract, canon and
writes, for every typed term whose obligations hold. The induction proves `Lawful` alone.
`Lawful.core` gives `LawfulCore` from it. An alternate reader is `Codec.extendRead` at the codec layer.
`ReadsCoherently` is its condition, and `extendRead_lawfulCore` proves `LawfulCore` for it over a
typed term whose obligations hold.

Choosing wrong is not a build error. A semantic premise in `Typed` makes the judgement
undecidable; a syntactic premise in `Obligations` becomes a burden every caller carries.

---

## Termination

`Term.depth` exists because `Typed` is a `Prop`-valued mutual family with no recursor over
derivations, so proofs recurse on the term. The built-in size measure cannot serve: the object
payload's field table is a function, and that measure is blind to functions. `Term.depth` takes a
supremum over the key set where a list would fold.

What matters is that the measure is **derived from the term**, so it appears in no statement, no
`Obligations` and no rule. That is the whole difference between it and a fuel parameter.

`term_depth_wf` is the shared tactic for a term recursion. Anything new recursing on a term takes
it, and an inequality the block does not offer goes beside `Term.depth` rather than inline.

A recursive term recurses on its input, not on the term. `muCodec` reads each input at the stage
that the input's own depth names, by the depths of the universe: `Sem.dV` on the write side and
`Sem.dA` on the read side, which are `Value.depth` and `Attr.depth` at DynamoDB.
That budget is a structural recursion on the input, so a closed recursive term still reduces by
`rfl`, and the bridge states its vectors. A well-founded budget evaluates and does not reduce in
the kernel.

---

## Recursion

**A recursive term is a guarded binder.** `Term.mu b` binds `Term.var 0` in `b`, with de Bruijn
indices. `denote` takes an environment of codecs for the variables, and a closed term is denoted in
the empty one, where a variable is the bottom. `denote (.mu b) ρ` is `muCodec` of the body
`fun c => denote b (c :: ρ)`. The stages start at the bottom, and each applies the body to the
one before. Each input reads the stage its own depth names.

**The guard is a checked condition on the syntax.** `Term.use i t` is the level at which `t` reads
the variable `i`. The four levels are absent, under a container, at the input, and under a `held`.
`Term.guarded` asks, at each binder, that the body reads its variable under a container at most.
It refuses two shapes, and `Discharge.lean` pins each refusal:

- a variable that reads the binder's own input, as in `mu (var 0)` (`not_typed_unguarded_binder`)
  and `mu (union [var 0, string])` (`guard_refuses_option_at_binder_input`). The stages of such a
  term never grow;
- a `held` between the binder and its variable (`guard_refuses_held_on_path`). The `f` of a
  `held` can make the input deeper, so a container on the path does not bound the depth.

`Typed.mu` carries the guard as a premise, because the guard is decidable from the term. A type
would need a second term family for the body of a binder, and every table over terms would gain a
family.

**Stability needs the guard alone.** `Contractive` says that a body reads its argument only at
inputs strictly shallower than its own input, on both sides. `contractive_body` derives it from the
guard, through one congruence over the term family (`denote_agree`). From it the stages agree past
the depth of the input (`muStage_agree`). The limit is a fixed point of its body (`muCodec_e_fix`,
`muCodec_p_fix`), and lawful stages give a lawful limit (`lawful_muCodec`). The lawful limit reads
both sides at the stage of the larger depth, so no lemma about depth preservation is owed. No
option of a body has to be disjoint from another for any of these.

**Soundness runs over the environment.** `Obligations` takes the environment. A `mu` owes the
premises of its body at each stage, given that the stage before is lawful. `soundnessIn` proves
`Lawful` for an open term whose variables the environment gives lawful codecs, and `soundness` is
the closed case. A recursive codec's held set is its write domain, so the held-set theorems stay
closed: at `mu` they are definitional.

**`opaque` is the construct at a fixed body.** `opaque` denotes `muCodec opaqStep`, where `opaqStep
c` is one layer of everything self-identifying over `c`. `contractive_opaqStep` is the contraction
at that body. Kind-disjointness gives the compatibility of its options (`compat_of_onKinds`, with
`compat_opaque` as the instance). That makes each layer lawful (`lawful_opaqStep`), and
`lawful_opaq` is the general limit theorem at that body.

**The analyses read a recursive term through its body.** `Adm` and `AdmA` take the environment
that `denote` takes. A variable asks the codec that the environment gives the variable, and a
`mu` asks its own codec, as the rows of `opaque` do.

**The meet reads a recursive term stage by stage.** Two recursive terms meet where their bodies
meet under every three stages that meet, because each stage is the body over the stage below
(`stage_meetV`, `stage_meetA`). A recursive term beside another constructor reads the stage below
the depth of the input (`Adm_mu_unfold`, `mu_p_unfold`). Neither row needs the guard. Where the
body met reads no variable of the pair, the answer is the body with its free variables lowered by
one, because such a binder denotes its body on both sides (`denote_mu_vacuous`). Elsewhere the
answer `mu z` is stated only where `mu z` is guarded, because `Typed.mu` asks the guard.

**The host spells recursion as a thunk, and the bridge prints the binder.** The emitter marks each
term object that a thunk returns during the printing of that object. It prints `Term.mu` at the
object and `Term.var k` at the thunk, where `k` counts the binders between the two. Any other thunk
prints the term it returns, because the model has no thunk. Each recursive vector asserts that the
guard accepts its term. The host's `union` refuses the two shapes the guard refuses. One is an
option whose spine reaches a recursive thunk. The other is an option where a `held` sits between the
term that a recursive thunk returns and the thunk. The host's `union` also refuses a thunk that
throws. Recursion below a list or an object stays declared, and the certificate decides it. The
host's `heldFree(t)` answers `false` at a recursive thunk. The model's `HF` reads through a binder,
so the host is the narrower of the two.

---

## The four recurring design moves

These are the architecture, more than the module list is.

### A premise becomes an index

Repeatedly a typing-rule side condition turns out to be expressible in the type of the
constructor, at which point violating it stops being possible rather than being refused.
`GroundKind` makes a literal's carrier concrete and
its equality decidable, so `ℓ ⊆ T` is the carrier rather than a premise beside it. `NEFinset`
makes nonemptiness, pairwise distinctness and homogeneity properties of the type wherever a wire
set is written.

**The criterion.** A premise becomes structural when its satisfying set is finitely enumerable at
declaration time, or when it is a property of one argument expressible in that argument's own
type. It does not when the premise relates one argument to other arguments' behaviour at a shared
input.

That last clause is the boundary, and **compatibility is the case on the wrong side of it**: it
is not a property of an option but a relation between two options at an input both act on.
Indices make per-thing properties structural, and this is not one.

**The discriminated union is the case that left the term language rather than crossing into it.**
A dissection is a `union` of object members whose pairwise structural meet is empty: two members
differ at a required literal name with disjoint alternatives, or the name intervals they declare
cannot be satisfied at once. `select` admits an object option by attempt, as it admits every other
option. The meet certifies both cases: the two bodies meet at the bottom. A sub-selection of a
certified union stays certified, because the certificate is `Pairwise` and `pairwiseCompat_sublist` carries the obligation under it. A
tag table keyed by the discriminating literals is an index the host builds over such a union, and
no term carries it.

**The criterion is necessary and not sufficient.** A move can pass it and still not pay, when the
bundling it invites re-threads the parts a stratum exists to bundle, or when it crosses a stated
decision about where a law belongs. Measure the site count too.

### A row asks its codec instead of describing it

A row can describe the set it stands for, or call the codec and ask. **Prefer asking.** A
description must be kept in agreement with what it describes; a question cannot drift.

Every excuse this pattern retired was a correct observation reaching a wrong conclusion, and the
shape recurs: *no syntactic set names this* is a reason to stop being syntactic, not a reason to
give up. The denotation of a numeric literal **is** the literal codec by reduction, so the row
that asks is the domain of the read half exactly.

The price is that a row becomes `noncomputable` when its codec is. That costs nothing here,
because `denote` is `noncomputable` already: `inL` is, and `denote` reads it.

An alternate reader is deliberately outside the term rows. `Codec.extendRead` tries the current
reader first and then the alternate reader. No structural analysis reads the alternate reader.

### One codec, stated once for both sides of the pair

A constructor is a prism — `Ctor`, with the laws `out_into` and `into_out` — and those two are the
round-trip and completeness clauses at a constructor, so the prism half of every lawfulness proof
is discharged once.

Two shapes sit over the prisms. `pointCodec` is the degenerate case, one payload type on both
sides, and the point codecs share one lawfulness proof through it. `carriedCodec` is the
load-bearing one: a payload pair between two prisms, the shape underneath every product. **The
model states a codec once for both sides**, so the doubling in this development is in the analyses
rather than in the algebra. Its two inversions `carried_e` and `carried_p` are what every
product's proof goes through.

The prism inventory is partial on both sides on purpose. The gaps are the constructions that are
not one payload between one pair: the numeric constructor, where the numeral gate stops the
projection being onto its image, and the wire sets. `setCodec` is the one deliberate non-instance,
because its attribute side is a choice among wire constructors rather than one prism, and its
inversion names all of those families.

**The rule reaches inversions, not only constructions.** An inversion stated on one side only
makes every proof on the other side unfold the definition by hand, which means unfolding the
matcher for a whole table and paying for every row at every rewrite. A one-sided inversion is a
defect of this rule, not a gap in coverage.

### The guards exist because prose does not typecheck

Every instrument here was built after a description drifted from what it described: an axiom claim
in prose, an attribute asserting a behaviour that had stopped being true, a citation of a deleted
name, a regex passed off as a reachability measurement, a grep passed off as a refactor estimate.
None was added speculatively.

---

## The analyses, and the one test that decides both sides

Every separation is one appeal to `Separates`, which takes two families of allowed values, one
per side, and asks only that each be pairwise disjoint. Kinds, members, tags
and admissible sets are ways of building those families rather than four separate conditions.

`ExactV.lean` holds `Adm` and `ExactA.lean` holds `AdmA`, exact at every constructor, with no
hypothesis and no escape hatch. Its value-side separation predicate is one clause, because the
joint predicate absorbs what a kind table used to carry. The attribute-side predicate is also one
clause. An alternate reader cannot add a structural exception because `Codec.extendRead` is
outside `Term`.

**One test decides both.** `select` attempts every option, so option admission *is* the row at
every constructor: `admitV_le_Adm` and `admitA_le_AdmA` hold from exactness alone, with no premise
on the term and no exception for an object. For the same reason, the row of a `union` is the
disjunction of its options' rows (`Adm_union`). So the joint predicate and the admission a
discharger consumes are one test, and `pairwiseCompat_of_separated` proves that a separated
union of lawful options meets its obligation.

**The direction has a standard name.** It is the abstract interpretation of Cousot and Cousot,
1977: a coarse test that over-approximates a precise one transfers disjointness downward, and a
tighter test does not. The principle is why a certificate may be proved over an approximation at
all. This development spends it once. `writeView`
and `readView` admit each value and each attribute that the term admits (`writeLe_of`,
`readLe_of`), so two views that meet at the bottom separate the terms.

**The outer carrier has a separate read-side fact.** An alternate reader can read an attribute
outside the current term's member. `extendRead_reads_n` records a string core that reads a numeric
attribute through its alternate reader. The structural classifier has no row for the outer
carrier.

`Orthogonality.lean` states the discharge on what the resolver consults rather than on what the
row says. `Separates` reads the row of each option, `isSome_e_eq_Adm`
identifies that row with what the option writes, and `pairwiseCompat_of_separated`
is the discharger stated on what `select` actually decides by.

### The classifier, and what it is the specification of

The union obligation is compatibility, and the certificate is sufficient for it. `certPair`
certifies a pair where the two terms are orthogonal (`viewsNever`).

**The certificate is orthogonality.** A term denotes a partial isomorphism. `writeView`
states its domain and `readView` states its range. In an inverse semigroup, two elements whose
domains and ranges are disjoint meet at the bottom (Lawson, *Primer on inverse semigroups I*,
Lemma 2.16). `certPair` meets the two caller views and the two stored views with `Term.meet`.
`Term.meet` refuses a `held`, and a view holds no `held`, so a `held` reaches the certificate
through its views. On a term with no `held`, the caller view is the term itself. The
view of a `union` is the union of the views of its options. The view of `mu b` is `mu` of the view
of `b`, and a variable stays a variable, so a `held` below a recursion reaches the certificate too.

**The stored view drops a predicate over a variable.** The stored view keeps a predicate only
where the inner term holds no `held` and no variable. A variable denotes a stage of its binder,
and the view reads each variable as a possible `held`. A finer view reads a variable as a `held`
only where the binder's body holds one. The two views give one verdict except at a data predicate
over a variable, and the host builds no data predicate. So no host-built term observes the
narrowing, and a Lean example pins the pair that the certificate refuses there.

**The meet reads a closure through its inner term.** The admission of a `refine` at a `closure`
is a function. A refinement admits a part of what its inner term admits,
so the meet answers the bottom where the inner term meets the partner at the bottom, and `none`
elsewhere. A closure refinement beside an option that writes and reads other slots meets at the
bottom.

**Its value is that it is half of the specification of the library's declaration-time guard, and
a checked half.** The `union` combinator in `src/` accepts a pair on one of four warrants. It
refuses every other pair, because the pair is not shown compatible.

| warrant | the host asks | the model proves the pair compatible by |
| --- | --- | --- |
| the never side | one option is `never` | `pairwiseCompat_never_left`, `pairwiseCompat_never_right` |
| held-free | both options are held-free | `pairwiseCompat_of_HF`: both sit below `opaque` |
| the common bound | `below(x, y)` or `below(y, x)` holds | `pairwiseCompat_of_sub`: the wider option is the bound |
| the certificate | `separable`: `certPair`, which meets the views at the bottom, and the meet of the terms at the bottom where the host has no views | `pairwiseCompat_of_separated` |

The host's rule `below(x, y)` in `src/codec/term.ts` is narrower than the model's `Sub`. It has
five rows: a literal is below its base and below itself; a union is below a term that each of its
options is below; a term is below a held-free union where the term is below one option; a `held` is
below the same adapter where its stored side and its held side are each below; and a term with no
payload is below itself. The union row asks for a held-free union, because `sub_union_mem` bounds
the options by `opaque`, and an option with a `held` has no such bound. So `decimal('1')` beside
`union([decimal('1', '2.5'), string('A')])` is refused, although the first is below one option of
the second.

**The host reads an unknown as a refusal.** The read side of an alternate reader is caller code,
and the declaration cannot bound its domain. So the host's meet refuses where it must read an
alternate reader, and a refusal certifies nothing. A container of an alternate reader beside a
term of another kind meets at the bottom, and reads no reader. An unknown read as "no meeting" is
the permissive direction, and so the unsound one.

**The host reads a thunk that throws as a free variable.** At a declaration, a thunk that names
the union under declaration throws. The model spells the thunk as a variable, and the theorems of
the meet hold under every environment of the variables. So the host's meet reads the thunk as a
variable that pairs with no binder. Beside the bottom the meet is the bottom, and beside any other
term the meet refuses. A list of such a thunk beside a string meets at the bottom.

**The caller view of a `held` is its held side.** The host's `decimal` over literals records the
string literals of its texts there, so its caller view is exact, and the views certify it beside a
string literal it does not write. A caller-built `held` keeps the held side that the caller gave.

**The bridge checks both directions.** The separation class in `src/codec/lean.ts` emits one
theorem per emittable pair of the sample codecs, generated and elaborated by `formal/scripts/gate.sh`. For a
pair the library accepts, the theorem states that the two terms meet `PairwiseCompat` where both
denote lawful codecs, proved by the warrant the library used. For a pair the library refuses, the theorem states that `certPair` does
not certify it.

**`certPair` is sufficient and not necessary.** A decline by `certPair` is not a refutation of
compatibility. Two restrictions of one adapter are compatible in the model
(`compat_of_common_bound`), and no certificate reaches such a pair where the two overlap. The
library accepts such a pair where `below(x, y)` shows one option below the other, as
`decimal('1', '2.5')` beside `decimal`. It refuses every other overlapping pair, as
`decimal('1', '2.5')` beside `decimal('2.5', '3')`.

`Separated` is what names the separation guarantee over the option list, with
`separated_of_unionOk` as the certificate's bridge into it.

---

## The instruments, and what each is blind to

The blind spot is the part that matters. The check is the part anyone can read off the script.

**The axiom assertion** in `Axioms.lean` makes the advertised base a build error rather than a
claim in prose. The base admits `Classical.choice`, in part because mathlib resolves membership in a
`Finset` through an instance whose injectivity field is proved classically, so no theorem here
carries a constructive warranty that this guard checks. It walks imported modules only, which is why the reachability guard exists. Its
filter admits theorems, so **a definition that acquires an axiom is not checked at all** — run the
axiom query on definitions, not only on theorems.

**The environment linters** over the `Calculus` namespace have no sanctioned hit today: the list is
empty, and the mechanism stays, because a hit this tree keeps owes a row and a reason beside it. The
docstring linter is excluded rather than sanctioned, because whether the docstring convention reaches
helper definitions is a judgement and not a defect, and an exclusion is visible where a mass sanction
would not be.

**`scripts/guard_reach.py`** is textual and necessary-only. It says the declarations are in the
environment the guard walks. It says nothing about whether the elaborator is correct or whether
the advertised base is the base the documents claim.

**`scripts/name_drift.py`** holds every backticked Lean-looking name in the current-state
documents to occurring somewhere in `Calculus/`, with a table carrying a reason per deliberate
exception, and failing when an entry there stops being cited so the table cannot rot quietly. Its
source set strips comments and docstrings, so a citation has to be answered by code rather than by
its own evidence.

Its blind spots are the shape of the whole problem. **A count is not a name**: it cannot see a
claim about how many declarations share a tactic being false while every name exists. It clears a
dotted name component-wise. **An entry fails when it stops being cited and cannot fail when its
reason goes stale**, which is the same asymmetry the docstring convention has, and the reason both
are conventions rather than guards. And it cannot see a name that stops being *the right one*: a
declaration that still exists while ceasing to be the one a passage cites is invisible. Renaming
is checked; re-pointing is not.

**`scripts/ratchet.py`** holds per-file counts to the state they were in and fails when one rises.
It exists because the bars this development wanted could not be bars: a coverage bar set at a
number nobody can satisfy is a bar that gets switched off, where a ratchet asks nothing on the day
it lands. Baselines live beside the script rather than in it, so a change to one is worth reading.
**A ratchet accepts the state it was born in, so it cannot see a defect older than itself** — it
guards the derivative, not the value. Lowering a baseline is the only move that should be routine.

**`scripts/docstring_anchor.py`** checks that no docstring in the library sits above a declaration
that is not its own. The host's documentation convention binds the *last* docstring before a
declaration, so where two blocks close and open with nothing between them, every block but the
last describes nothing a reader can reach: it renders in no tooltip, no link resolves to it, and no
other check here reads it. That is the shape a scripted deletion leaves behind — the declaration
goes and its prose drifts down onto whatever follows. **Nothing else can see it**: the type checker
and the formatter read no comment, the name guard reads the model's side, and the suite passes
either way. Its blind spot is that the signature is structural rather than semantic. It finds two
blocks with nothing between them; whether a stranded block is deliberate two-part prose is a
judgement, so such a block carries a marker and the guard takes it at its word.

**Grep is the instrument that is left, and it has two blind spots of its own.** A grep piped into a pager is not
a measurement, and the same pipe hides an exit code as readily as a line — reading a status
through a pager reports the pager's success. And an edit anchor that is not unique is not an
anchor: anchor a scripted edit on a whole block that occurs once, and read the line delta before
writing, because a diff of the wrong size is visible in one number and invisible in a review. The
second real blind spot is the anonymous-constructor pattern: a positional match names neither the
qualified constructor nor the case, so when costing a constructor change, grep the bare dotted
form too and expect the arity to be implicit.

### The bridge, and the claims that cannot reach the kernel

**Regeneration is not verification.** What verifies the bridge is elaboration, which is why the
gate runs the committed samples and every emittable pair of the sample codecs through Lean rather than
trusting a byte comparison. **Refusal vectors are the other half of the same blind spot**: a
positive vector is an agreement about what the library wrote, so a value the library refuses
produces no vector at all — the half of the pair where the two sides could disagree unobserved.

**No vector asserts a decoded value.** Every emitted theorem is about the write half or about a
refusal, and the read-side differential compares a decision rather than the value that came back.
So the kernel has never been shown that the read half returns a particular value, and the two laws
most of this library's shipped defects lived in are the two the bridge cannot state. `veq`, sound
by `veq_sound`, is what would make them statable.

**The terms the emitter refuses are exactly the terms whose laws a caller owes.** The constructors
carrying a caller's function, and a refinement holding a host predicate, are unemittable because
nothing translates a closure into a Lean term, and emitting a different predicate would compile
and prove the wrong theorem. That refusal is right. Its consequence is that the bridge is blind
precisely where the model discharges an obligation the host cannot check either, so for those
terms the guarantee is a written premise on both sides.

**A red bridge check that returns immediately has read nothing.** The bridge shares a build cache,
and a racing run fails at once over an unchanged tree. Judge that check by its duration before
judging it by its exit code.

The bridge checks generated lines by kernel typechecking rather than by evaluation, because the
denotation is `noncomputable`. Evaluation and decision by compilation are both unavailable, and
that is not a toolchain gap to route around.

### The host's instruments

**The type checker's error count is a lower bound, not a measure.** Retyping a position
under-reports the sites: a cast standing on the position leaves the checker nothing to say, a test
whose subject rides on a type it does not name keeps passing while the fact it pins stops being
checked, and a comparison at the wrong level of nesting reports nothing. The sharpest case is a
deletion rather than a retyping — collapsing an option builder to the term-only form typechecks
cleanly, because the member's type already admits the absent case, and fails a row of tests. The
suite is what closes the gap.

**The type-level snapshot proves negatives and sees only what a spec asserts.** It records an
instantiation count and a resolved type per assertion, so a change that moves neither moved
nothing any assertion covers. What it cannot say is anything about a type no spec names, and the
population it covers is a choice somebody made rather than the surface.

**A strictness flag that is off reports nothing**, and that is a blindness no tool can announce
because nobody asked it anything. Asking, with no file changed, is what turns an unasked question
into an answer.

---

## What is deliberately not modelled

Each of these is a decision with a price, not a gap, and each has a witness.

**The nesting bound.** `Nesting.lean` is the one place the attribute algebra is larger in the
model than in the store, deliberately. The list and map constructors nest without limit by
construction, so a derivable term can write an attribute the store refuses, and
`not_storable_of_typed` is the witness: a well-typed term, a value on its held set, an encoding
outside `Attr.Storable`. The model must be able to **state** this, because a target certified
against a specification that cannot say it is certified against a weaker claim than its users
read. The honest repair is not a carrier refinement, because the witness violates no premise: the
rules do not mention depth. The indexed-family alternative is accepted by the kernel only in
mutual form, so every list position needs a hand-rolled companion indexed alongside it, which is
the price. `Attr.Storable` counts the two nesting constructors and is a different function from
`Attr.depth`, which is a termination measure. Do not unify them.

**The DynamoDB set rules, outside the set algebra.** `set` is the finite-powerset lift of any
element term, and a lawful element gives a lawful set (`lawful_setCodec`). Three rules of a stored
set are DynamoDB facts and not rules of the algebra. The element types `S`, `N` and `B` and the
absent empty set live in the carrier: `Value.strSet`, `numSet` and `binSet` over `NEFinset`. That
the element writes one member of `S`, `N` or `B` is an obligation, `SetElem`, beside `(union)`'s
compatibility. `SetElem` is the `elem` field of the DynamoDB set former `dSet`, and the generic
`SetObl` reads it. The carrier holds no set of `Value`, for two reasons. The kernel rejects a
nested `Finset`, `Multiset` or `Quot` of the datatype being declared. A list carrier needs a
canonical spelling that every set codec enforces by refusal.

**The n-ary literal is a union of singletons.** A literal carries one value, and several
alternatives are a `union` of singleton literals whose members are separated because the values
differ. `LiteralArity1.lean` is the derivation. The route was refused while a literal held a set: the
bridge from a `Finset` of alternatives to the list `Term.union` takes is `Finset.toList`, which
reaches `Classical.choice`. One value leaves no such set, so there is no bridge to cross. The host
keeps the n-ary call as a builder that writes the union, because the hand-written union costs the
type checker in proportion to the number of alternatives where the call is flat.

**A host numeric type.** The model carries a number exactly, as `WFNumeral`, and declares no
axiom. A host numeric type, such as a binary64 float, is not modelled, because rounding is not a
theorem of this calculus. A port adapts the host type to `WFNumeral` inside the port. The emitter
refuses a JS number for the same reason: writing one down as a `WFNumeral` is a rounding that the
model does not state.

---

## What the host owes

The model's structural guarantees are not self-enforcing in an implementation. A type here is a
question the host still has to answer.

**The rule: prefer making a bad state unrepresentable over guarding against it.**

For every structural guarantee the model makes, a host is in exactly one of three positions.

| the host | owes | why that is the whole debt |
| --- | --- | --- |
| **(a)** carries it structurally | **nothing** — verify by types and move on | the host type is doing the work; there is no gate to own and nothing to test that the type does not already say |
| **(b)** must gate | a **named** gate, in the module that owns the carrier, and a test asserting **both** sides | one owner: a gate mirroring a carrier refinement belongs to the module that *is* the unrefined carrier, or a sibling entry point writes a second answer to the same question. And a test checking only our behaviour cannot tell a deliberate divergence from a reference implementation apart from a regression |
| **(c)** cannot express it | a construction-time **refusal**, a test that pins it, and a written **reason** | the reason is what stops the next reader from "fixing" the signature, and **the test is the half that goes missing** |

**A (c) refusal is not finished until a test reaches it past a cast.** A brand is not a proof and
a cast defeats a brand, so the caller the refusal exists for is exactly the caller the type cannot
see, and that caller is the one a test must impersonate. A refusal whose deletion leaves the suite
green was load-bearing for the type and unobserved for behaviour.

**The three cases are not a permanent assignment.** A host that had to gate can later carry the
guarantee structurally, and when it does the gate stops refusing anything and its remaining
content is its message. **What such a gate owes on the way out is that message, moved where a
refused caller reads it.** A constraint's own diagnostic names the offending type; it does not say
what to write instead. A gate deleted without moving its sentence loses the only part of it the
type did not already carry.

**The exception that keeps a gate.** Keep it only where the refutation depending on it **cannot be
restated outside the term language**. If the thing refuted is a rule rather than one of our
constructors, a standalone transcription carries it and the gate can go: a prism written out
beside the codecs, deliberately not a `Term`, is such a transcription. Where the claim is about one
of our own rows, no transcription recovers it and the gate pays.

The numeric instance of this has since retired itself. Its transcription existed to hold a value
outside the base's held set, and the value carrier is that set now, so there is nothing left to
point at. A refutation needs a representable counterexample, and a gate that moves into a carrier
takes its own refutations with it.

**A measure has no host counterpart, so it is pure overhead.** No line of the library has a fuel
parameter. A measure standing in for a recursion the checker could not see corresponds to nothing
in an implementation. The discipline is a hierarchy: turning a measure into structure costs the
correspondence nothing and is worth the most; turning a gate into a type is worth less and is
available where the condition is decidable from a constructor's own arguments and the host can
mirror it or pay honestly; keeping the gate is for the exception above.

**Targets differ, and that is a fact about certification.** The same structure ports with
different fidelity. A nonempty finite set is not expressible for a variadic in TypeScript and is a
newtype with a private constructor in Rust. An indexed literal is a discriminated union of literal
types in one and an enum with a payload per variant in the other, which *is* the indexed family.
A checked numeral wants a nominal newtype in both, and where a language has no nominal typing the
branded-type trick is the closest thing and a cast defeats it.

**Sometimes the host has the sharper instrument.** Two byte arrays holding the same bytes are the
same value in the model, which has no reference identity to distinguish them. A host that does
have one answers a binary literal's read side with the declared array rather than a copy: that is
how the host spells "the value the model means" where the model needs no spelling. A target with
value semantics for byte arrays owes nothing here, and one without owes the identity.

**Where the two sides disagree, the emitter is where it gets written down.** A tag is stored as a
string or as a numeral. A numeric literal carries a `WFNumeral`, which is a closed term, and the
host's `decimal` literal is that literal under the text adapter `numeralOfStoredText`. So a
discriminator at either base emits.

**What bounds the emitter is which terms have closed forms.** A caller's closure has none. The
emitter refuses a term that holds one, rather than emitting a vector about a codec the model
cannot express, and its message says so in the caller's vocabulary. That refusal is the record,
and it is the shape every gap of this kind takes.

**A core union requires its discriminator.** The model selects only an input that carries the
required discriminator. A caller that accepts an old input extends the whole union's codec with
one alternate reader (`Codec.extendRead`). The alternate reader owns that migration after core
selection refuses.
`Body.spec` contains no migration field.

**A host obligation that no host code reads is found by whatever has to serialise the host's own
definition, or it is not found.** A term the host builds must determine the codec the host runs.
Where a definition record kept only what each reader needed, a channel the model carries was
dropped and nothing failed, because the half that was missing was the half nothing read.

**A codec carrying a `Term` is case (a) reached by deletion.** Keeping two descriptions of a codec
— the model's language and a record that grew a row at a time — made states reachable in the host
that are unrepresentable in the model. One description means those states stop being reachable
rather than being checked for, which is what (a) buys. Such a flip has to be one commit, because
the denotation dispatches on one type: a union of the two types on the field compiles just as well
half-migrated, so nothing in the checker says when the transition has finished, and a reverse
conversion at the construction site is a second conversion written in order to be deleted. What
says when it is finished is a table asserting the conversion is the identity, one row per
constructor — which no checker can answer, and which asserts nothing once it is complete.

**Test machinery drives the generators; it does not hold them.** An adapter states its own
generator and shrinker where its pair is partial, because how a codec generates is a fact about
that codec rather than about testing, and `held` takes the conversion and the two generators
together as data — they go into the term, which is the codec's whole definition. What lives in the testing entry point is the
machinery that *drives* them: the derivers that walk a term to build a generator, the shrinker, and
the law checkers. **The term is the only source.** Where a generator was a projection of the term
that the derivers read before the term was consulted, one fact travelled two paths and could
disagree with itself; now a caller that wants to share a generator names it rather than reading it
back off a codec.

**A value that the codec's own read produced is evidence.** A law checker that generates a value
through the read of a `held`, and finds that the codec declines to write the value, reports a (C)
failure with the value and the seed. The decode check in `src/codec/testing.ts` discards a
declined write of any other value, up to a bound, and throws with the seed past the bound.

**So a guarantee that must be a gate in one target may be structural in another.** The three cases
are re-answered per target at the time that target is certified, not in advance, and not as a
reason to shape the model around one language. The model's job is to make the guarantee structural
in the model. How much each target carries is that target's certification.

---

## The proof vocabulary, and what a docstring is for

**The rule.** A definition is unfolded once, in its own inversion lemma. Every proof downstream
cites the lemma. Each construction gets two, proved in one step, and they are the only place that
construction's option chain is ever taken apart: one for what the construction writes, one for
what it reads.

**The naming scheme is normative**, so the next proof inherits it.

| form | means |
| --- | --- |
| `X_e` and `X_p` | inversion — what `X` writes, what `X` reads |
| `X_eq` | `X` **is** an instance of a named construction, on the nose |
| `lawfulCore_X`, `lawful_X`, `carrier_X` | the three obligations, in that order |
| `Lawful.X` and `LawfulCore.X` | the same where the construction is itself namespaced |
| `f_sound` | a syntactic function agrees with the denotation |
| `equiv_X` | a rewriting row |
| `not_X` | a refutation, or a repaired discharger |
| `onKind_X` | `X` is pinned to a kind |

**What a docstring is for.** The source explains the code; the history is in `git log`. Keep the
rule or clause tag, so a reviewer can check a theorem in isolation. Keep the forced choice: why
the definition could not have been the obvious other one. Keep what a refutation is a refutation
of. Move out how a finding was made, what it cost, which audit missed it, and any argument another
document already states. Prefer a name that makes the sentence unnecessary.

**A name the sources do not define is marked rather than backticked, and this is normative.**
Usually it is retired, because a docstring recording what a forced choice cost has to name the
thing that lost. To the name guard a deliberately dead name and a renamed one are the same token
absent from the sources, and the difference is the tense of the sentence, which no parser reads.
The mark carries it. An unmarked backticked name is a claim that it is live and the guard holds
you to it; a marked one is a claim that it is dead, and a mark on a name still in the sources
fails as a false retirement. Occasionally the name never existed, and the mark says the same
useful thing there.

Two further conventions, both load-bearing. **The core lemma is not a second proof**: the weaker
obligation and the stronger one share their clauses and differ only where the content differs,
with a projection making the weaker a corollary rather than a parallel development. **An identity
stated in prose gets cashed as an equation**, so that every lemma carries across by rewriting
rather than by restatement.

**Length is not the metric; sites are.** A theorem whose content *is* a rule-by-rule dispatch
belongs at the top of the length table, one line per typing rule, and compressing it would cost
the reader the correspondence with the rules. Inline comments are exempt from the naming
convention: they are proof waypoints, which is the one thing a name cannot supply.

---

## If you change something

- New module under `Calculus/` → make it reachable from `Axioms.lean`, and baseline its counts,
  because a new module has no prior state to be judged against.
- New stratum in the term family → every companion in the table above, counted per side.
- New law of the algebra → state it in an `Alg` module, which imports no instance module. A
  statement that needs a fact of a carrier belongs to that universe.
- New universe → a `Syn`, a `Sem` instance, its `TopLaws` where the held-free theory or the read
  side of the meet must hold, its `PrimAdm` and `PrimAdmA` where exactness must hold, its `Leaf`
  where the meet must compute, and its `Shapes` and the laws of the meet where the theorems of the
  meet must hold. A read-side law of the meet states a read domain only. Make the module reachable
  from `Axioms.lean`.
- New rule → put each term premise in exactly one of `Typed` and `Obligations`.
- New term recursion → `term_depth_wf`, and any new inequality beside `Term.depth`.
- New analysis row → prefer asking the codec over describing the set, then prove its exactness
  clause, because a missing row is silent and silence is sound.
- Sharpening a row that answers "everything" at a container → find what relied on the slack
  before you sharpen it. Nothing measures transitive dependents any more, so the cost is a grep
  with the two blind spots above, read against what the analyses say the slack is carrying.
- Citing a Lean name in a current-state document → the name guard must exit 0.
- Reaching for a count in a document → do not. No guard holds a document to a number any
  more, so a count in prose is unguarded by construction. It belongs in the commit that
  measured it, in `defects.md` where it pins an issue, or in a guard's output.
- Deleting a declaration → resolve every path and every name the deletion leaves cited, because
  no guard resolves a cited path and the name guard clears a citation that any file in its source
  set happens to mention. `git log -S` on the name is what says whether it was ever declared.
- Touching a normative document, the advertised axiom base, or the library's behaviour → that is
  the owner's decision. Deliver the measurement and stop.
- Committing anything → run the gate, and gate on its **exit code**. Printing an exit code is not
  checking it.

### On the host side, per structural guarantee

- Which of the three cases is this host in? Answer that before writing the gate, not after.
- **(a)** Name the host type that carries it. No gate, no test.
- **(b)** The gate lives in the module that owns the carrier, not in the first caller. One owner.
  The test asserts both sides wherever the behaviour diverges from a reference implementation.
- **(c)** Construction-time refusal, a test that reaches it past a cast, and a written reason.
- Does a refutation depend on this being a gate *in the model*? Only then keep it, and only if the
  refutation cannot be restated outside the term language.
- Is it a measure rather than a guard? Then it has no host counterpart and is overhead.
- **Un-typeable never means un-checkable.** A constraint that fails "can it be a type?" is not
  disposed of. It is handed to the next question: does anything enforce it? Filing it as closed on
  the first answer is a recorded failure mode of this project's own auditing.
