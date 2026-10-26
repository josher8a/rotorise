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
| The rules, normatively | `formal/docs/blueprint/src/content.tex` |
| Future states, and what decides each | `docs/roadmap.md` |
| Known, suspected and partially mitigated issues | `docs/defects.md` |
| What changed and why | `git log` |
| Module table and how to build | `formal/README.md` |

---

## The epistemic structure

This repository is two developments and one bridge between them.

`src/` is a published TypeScript library. `Calculus/` is a Lean model of part of that library.
The bridge is the emitter in `src/codec/lean.ts`. The emitter states the decisions that the library
made as Lean data: encodes, refusals, reads, verdicts, separations, disjointness, slices and paths.
The Lean kernel decides whether the model makes each decision.

The three carry different warranties, and keeping them apart is the whole discipline.

- **The model proves.** A theorem in `Calculus/` is checked by the kernel against an advertised
  axiom base.
- **The bridge checks agreement.** A vector is a proposition about one operation the library ran.
  Elaboration is what verifies it. Comparing the emitter against output the emitter produced
  verifies nothing, because a stale emitter agrees with its own stale output.
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
| `Alg/Codec.lean` | the record `Codec` and its laws `Lawful` and `LawfulCore`, over the carrier `V` and the members `M` |
| `Alg/Combinators.lean`, `Alg/Relations.lean` | the combinators, the union computed by the first admitter, the order, the equivalence, `Compat`, `Canon` and `Sub` |
| `Alg/Lists.lean`, `Alg/Positions.lean`, `Alg/Maps.lean` | the traversal and `entrywise`, the positional theory, the image of a function over a key set, and `MapOf`, which keeps the namespace `Calculus`, with the union of two records `MapOf.union` and the product of two sums of records `MapOf.prod` |
| `Alg/Containers.lean`, `Alg/Recursion.lean` | `listCodec` and `objectCodec` over prisms, the pairing `objAt_union` of two closed objects, and `AgreeLe` over one depth function |
| `Alg/Agree.lean` | agreement `Agree` at an orientation, whose two halves are the host and the dual, one lemma per combinator, `compat_iff_agree`, and the join law of a union `altCodec_eq_join` |
| `Lang/Term.lean` | the signature `Sig`, the syntax `Syn`, the meaning `Mean`, and the tables of adapters |
| `Alg/System.lean` | the solution of a system of codecs, `contractive_of_guarded`, and the flat scope with `scope_solution` |
| `Lang/Scope.lean`, `Lang/ScopeSound.lean`, `Lang/ScopeHeldFree.lean` | the closed codec `Scoped.Closed` and its meaning, the judgement `Scoped.Typed` and `Scoped.Obligations`, `Scoped.Closed.sound`, `Scoped.Closed.meaning_sub`, and the product of closed objects `Scoped.Term.product` |
| `Lang/Universe.lean`, `Lang/ScopeDisjoint.lean` | the class `Leaf`, the one walk of the decisions (`Scoped.Row`, `Scoped.walk`) over pairs of terms, the structural disjointness decision `Scoped.disjoint` over two closed codecs with its soundness `Scoped.disjoint_sound`, the view `viewG` at an orientation, and `views_apart` |
| `Lang/ScopeFuel.lean`, `Lang/ScopeExact.lean` | the adequacy of the fuel of the walk on a flat system, for each row that meets `Scoped.RowMono` and `Scoped.RowNever`, the witness laws `Scoped.WLaws`, the fragment `Scoped.Frag`, and the exactness `Scoped.disjoint_exact`; `Dynamo/Analysis/ScopeExact.lean` and `JSON/ScopeExact.lean` give the two universes |
| `Lang/ScopeCompat.lean`, `Lang/ScopeCompatFuel.lean` | the compatibility decision `Scoped.compatPair` over two closed codecs, the row of agreement on the one walk, `Scoped.compatPair_sound`, and the adequacy of its fuel |
| `Lang/CodecPath.lean`, `Lang/ScopePath.lean` | the write of the store at a path `putPath` with `path_law`, the frontier of a closed codec `Rooted.at`, the strong law `Closed.strong_law`, and narrowing `narrowC` with `narrowC_law` |

`Rows.lean` is generic too, in the namespace `Calculus`. It states the row combinators of the
analyses over one carrier type, and each side of the pair instantiates it. It states the row
`rowOfG` that a `list` shape assigns to a length, at any element type.

`Lawful` takes the member of an attribute as a parameter. (W) reads that function, and no law
reads more of the store.

**A universe is a signature, a meaning, and an orientation.** The signature `Sig` holds the syntax:
the primitives, and the predicates and the adapter generators at each absolute side. The term family
reads `Sig` alone, and names no orientation. The class `Mean` over a `Sig` holds the absolute
meaning: the carrier of each side, the member of the stored side, the codec of each primitive, the
evaluation of a predicate at each side, the depths, the formers and the top. A universe `Syn` is a
signature and an orientation `Orient`, a pair of two different sides. The readings in the namespace
`Syn` read the predicates and the depths at the orientation. A meaning has one carrier at both
sides: a codec is a partial bijection of that carrier, and the dual orientation is its inverse. The codecs and the member are the meaning itself at every orientation,
and an analysis reads a codec at its orientation. The dual universe `Syn.op` keeps the signature and
swaps the orientation, so the dual term type is the term type, and the converse of a term is the
term. The compiled code of a function over `Term S`
takes `S` as a real argument, because `casesOn` takes the parameter of the family as a real
argument. The meaning is computable: no definition carries `noncomputable`, and `#eval` runs
`Closed.meaning` and `Closed.AdmA` at DynamoDB.
The split keeps a term as data that code can compute with.

**Each stored-side law of the generic layer is the caller-side law at the dual orientation.** A law
of the scoped decisions takes the orientation as a parameter (`Scoped.Laws`, `Scoped.disjoint_sound`),
and the stored-side law is the law at the dual. At DynamoDB the
two sides hold one carrier. The wire format fixes `Attr`, and `Value` names the same type at the
caller side, because no law reads a difference between the two sides.

**A universe owns these facts, and the generic layer owns none of them.** The top is not among
them: `Syn.top` is the identity codec `idCodec` of the carrier at every universe, because the
top reads every datum and sends each datum to itself.

| the fact | the field | at DynamoDB | at JSON |
| --- | --- | --- | --- |
| the carrier and the members | `Mean.V`, `Mean.Mem`, read as `Syn.V`, `Syn.M` | `Attr` (`Value` names it at the caller side), `Member` | `Json`, `JMember` |
| the member of an attribute | `Mean.mem` | `Attr.member` | `Json.member` |
| the primitives and their codecs | `Sig.Ground`, `Mean.ground`, `Mean.lawful_ground` | `Ground`, `groundCodec` | `JMember`, `ground` |
| the predicates | `Sig.P`, `Mean.eval`, and the truth `Mean.truth`, at each absolute side | `Pred`, `Pred.eval`; the stored side names the truth `()` alone | a function on `Json` |
| the generators of the adapters | `Sig.G`, `Sig.decG`, at each absolute side | `DynGen` | `Empty` |
| the older readers | `Sig.R`, `Mean.read` | `Attr → Option Value`, read as itself | `Json → Option Json`, read as itself |
| the constants of a fill slot | `Sig.K`, `Mean.const` | `Value`, read as itself | `Json`, read as itself |
| the depth | `Mean.d`, one function of the carrier | `Attr.depth` | a constant |
| the list and map formers | `Mean.list` as a `ListA`, `Mean.map` as a `MapA`: one prism of the carrier | `dList`, `dMap` | none |
| the set former | `Mean.set` as a `SetF` over the carrier of the meaning: a lift, its laws, and the member of a set from the member of its element (`SetF.member`, with `SetF.lift_μ`) | `dSet`, over `setCodec` | none |
| the obligation on a set element | `SetF.elem`, which soundness does not read | `SetElem` | none |
| the top laws: each primitive, and the set lift, below the top, and the set lift over a restriction of the top acts where its element acts | `TopLaws`, a class with one instance for each universe | `Ω_topLaws` | `id_topLaws` |
| the admission row of a primitive, and its exactness | `PrimAdm` | `inBase` and `inL` (`dynPrimAdm`), and each primitive is self-dual (`ground_selfdual`) | the kind test (`jsonPrimAdm`) |
| the leaf: two primitives apart | `Leaf` | `dynLeaf`: `Ground.apart` | `jsonLeaf`: one kind |
| the law of the leaf | the primitive law of `Scoped.Laws` | `dynLaws`, at each orientation | `jsonLaws`, at each orientation |
| the set law that the decision reads | the set law of `Scoped.Laws` | `dynLaws`, at each orientation | `jsonLaws`, at each orientation |
| the former class of each value and attribute, and where each former lands | `Shapes` | `dynShapes`: the root constructor | `jsonShapes`: every value is a primitive |

**The member of a node is the meaning's member, at every universe (`μG_sound`).** `μG` reads
a primitive's member off its codec, and a set's member through `SetF.member`. `SetF.lift_μ` requires the lift to stamp that same member. Without the
law, the `⇝` index of the judgement states nothing about the codec.

A former is an `Option`. A universe without a former denotes the term of that former as the
bottom. `TopLaws` is outside `Sem`, because soundness and the judgement read none of its laws. Only
the held-free theory, the views, and the bound by the top in the compatibility decision read them. `PrimAdm`
is outside `Sem` for the same reason: soundness and the judgement read none of its rows.

**The disjointness decision is structural, and a universe supplies its leaf.** `Scoped.disjoint`
reads the flat graph of two closed codecs, has one row per operation of the left operand, and
decides that the two closed codecs share no datum. Only
one row reads a fact of a universe: a primitive beside a primitive. `Leaf` holds the apart test of
two primitives. The row of a refinement reads through the refinement, because a refinement accepts
a part of what its inner term accepts.
`Leaf` is a fact of the signature, so the dual universe has the leaf of the universe. `Leaf` is outside `Sem` and holds computable fields only, so the test stays computable,
and the kernel evaluates a closed pair.

**The decision assumes a pair of entries below a guard.** Below a guard, the decision assumes a pair
of entries while it compares the two bodies, and a pair already assumed is apart (`pairX`). At an
unguarded position, the decision unfolds an entry. A fuel bounds the walk, and an empty fuel answers
`false`. The row of a left refinement reads its inner term. On the right, a union reads its options
and a refinement reads its inner term (`rightC`). So a right refinement hides no option from the
left row. A pair with a closed side runs the row at the same fuel (`pairX`), because a closed term
is a finite tree. The compatibility decision runs on the same walk (`Scoped.walk`) with its own row,
so the table, the fuel and `pairX` are one definition for both decisions. Both rows read two
spreading lists through one function (`alignedRows`): the aligned rows at each common length, from
the lowest length that both admit to one past the length where both re-spread. The disjoint row asks
for one apart pair at each length, and the compatibility row asks that every aligned pair agree. The
set row compares the two elements as any other pair below a guard, with the assumed pairs. Each
child of a container is an entry, so each cycle passes a pair of entries, and the decision meets
each cycle at a pair that it can assume. A `held`, a `legacy` and the top are disjoint only from the
bottom, because their admission is a function that the decision does not read.

**The soundness of the decision holds at every signature, from the laws of the universe.**
`Scoped.disjoint_sound` says that where the decision answers `true`, no datum of any depth is
accepted by both meanings at the orientation. Where the decision answers `true`, the pairs that the
walk covers form a post-fixed point of the rows, up to the unfolding of two entries. The proof is
one rule induction on the evaluation of the left meaning, and it reads the rows at each pair. The
proof holds at every fuel. The closure of the walk is one lemma (`Scoped.vis_postW`), and
`Scoped.compat_sound` reads it with the rows of agreement. The laws are outside
`Sem`, because only the soundness theorems read them.
`Scoped.Laws` holds two laws at one orientation: two primitives that the leaf keeps apart share no
datum, and two sets whose elements share no datum share no set. The decision reads no
orientation, because orthogonality is self-dual, so one decision serves the value side at the host
and the attribute side at the dual. The `refine` row needs no law: a refinement accepts a part of
what its inner term accepts (`refine2_acc`). At DynamoDB, a leaf law is a fact about `inBase` and
`inL`, and a set law is a fact about `setCodec`. At JSON, two kinds meet where they are one kind,
and the set law holds because the signature has no set former.

**The decision is exact over the fragment.** `Scoped.disjoint_exact` says that the decision answers
`true` exactly where the two meanings share no datum, for two closed codecs whose entries are in the
fragment `Scoped.Frag`. The fragment is the free constructors that the universe has: a primitive,
a union, the bottom, a list, an object with no fill, and a set over the primitives that the
universe holds in a set. `Scoped.WLaws` holds the dual laws: two primitives that the leaf does not
keep apart share a datum, and two sets over elements that share a datum share a set. A common
datum comes from a path of the walk, by induction. The fuel of `disjoint` suffices, because on a
flat system each step of the walk lowers a measure of the table and the unguarded height. The
measure reads the walk and not the row, so the fuel of `compat` suffices by the same theorem.
Outside the fragment the converse fails: the decision does not read the admission of a
refinement, a fill, a `held`, a `legacy` or the top, a set of booleans at DynamoDB accepts nothing,
and JSON has no list former.

**A universe is a container, and the disjointness of two formers is a theorem.** The carrier of a
universe is the W-type of a container, and the member of a value is its root shape. Each former
lands in one class of root shapes: a primitive, a set, a list or an object. The classes of distinct
formers are disjoint, because the carrier is a coproduct. `Shapes` gives the class of each datum,
and the landing fact of each former at each orientation: a primitive codec, the set lift, the list
prism and the map prism. So two operations of different classes share no datum at either orientation
(`former_of_run`, `AB.of_cls`). The catch-all rows of the decision read those theorems. A set and a keyed map are quotient containers, so the set laws stay a class
of each universe. At DynamoDB, the class of a value or an attribute is its root constructor.

**The set former is a lift, and not a prism.** The list and map formers are prisms from `List`
and `MapOf` of the carrier onto the carrier. A set former cannot be such a prism: the kernel
refuses a `Finset` of the datatype that it declares, as a nested occurrence. So `SetF` carries a
codec transformer `lift` with its law, its agreement one layer down, and its held set. At
DynamoDB the lift is `setCodec`, over the three wire-set constructors of `Value`.

**The theorems of the algebra hold at every signature.** `Scoped.Closed.sound` proves `Lawful` for
each entry of a typed closed codec whose obligations hold, in any universe. The universe supplies the laws of its
primitives and of its formers, and the generic combinators supply the rest.
`Scoped.Closed.meaning_sub` proves from `TopLaws` that the meaning of a held-free closed codec is a
restriction of the top.

**The instance names the generic declarations.** At DynamoDB, `Codec` and `Lawful` are
abbreviations at the DynamoDB carriers, and `Scoped.Term` is an abbreviation at `dynSig`.
`Closed.Typed` and `Closed.Obligations` state the generic judgement and the generic obligations of
a closed codec at the DynamoDB tables. A `match_pattern` abbreviation keeps each constructor
spelling, such as `Term.string` and `Term.literal`. A cited DynamoDB theorem, such as `Closed.sound`, states the generic theorem at the
DynamoDB names.

**The DynamoDB meaning is the generic meaning of a closed codec.** `Closed.meaning` reads the
solution of the scope of a closed codec at the DynamoDB tables, and `μG` reads the member of a
graph term. A proof at DynamoDB reads `baseCodec`, `setCodec` and `listCodec` by name.
`Scoped.interp_held` and `Scoped.interp_refine` state the rows of `held` and `refine` over a
scope term.

**A `held` carries an adapter word, and the meaning reads a table.** A word is a list of signed
generators. The sign `true` names the converse of a generator: the pair of the generator with its
two functions swapped. A table `α` gives each generator its caller-side function and its
stored-side function, and the meaning of a closed codec reads the tables of the two absolute sides.
`TableAt.word` interprets a word by composition, with the first letter outermost on the caller
side.
The empty word is the identity at every table. The pair of two words in sequence is the composite
of the two pairs (`TableAt.word_append`). So two nested `held`s are one `held` of the concatenated
word, under a `refine` by the inner caller-side restriction (`Scoped.equiv_held_comp`). The dagger
of a word (`Word.dagger`) reverses the letters and flips each sign. The dagger law states that the
pair of the dagger is the pair of the word, swapped (`Table.word_dagger`). A `held` carries one
absolute side `s` and a non-empty word at `s`. The other side has no adapter and no restriction.
A `held` with the empty word has no representation, and a restriction with no adapter is a
`refine`. A two-sided adapter is two nested `held`s (`held1_nest`). The obligation of a `held` is
`Obl1`: `IsoCancelsAt` on the pair of the word at the orientation whose caller side is `s`, and
the member fact of the exit function where `s` is the side of the attributes. A `held` owes one
obligation for one half, because caller code is opaque. The store of DynamoDB names no generator,
so each `held` of DynamoDB is at the side `false`, and its obligation is `IsoCancels`.

At DynamoDB, `libTable κ` gives `decimalText` the text adapter, and gives `caller n` the pair that
the caller table `κ` supplies. A verdict vector prints a caller adapter as `caller n`, and the
theorem of an accepted pair quantifies `κ`, so the verdict holds at every pair of functions. An
evaluation vector reads `libTable noCallers`, because the emitter refuses a caller adapter outside
a verdict.

**No admission row stands beside the meaning.** A universe states the primitive rows (`PrimAdm`),
so a verdict at a primitive reduces without the codec. The read row of a closed codec,
`Closed.AdmA`, is the domain of the read of its meaning.

**The other analyses are DynamoDB tables.** `Separation`, `ScopeSlice` and the certificate read
the constructors of the DynamoDB carriers. No generic form of them exists. Inside the DynamoDB layer the import graph is an almost-linear spine: `Domain`, then
`Codec`, then the combinator algebra at the DynamoDB carriers as `Prisms`, `Products`, `Objects`,
`Sums`, `Carriers`, `Lawful` and `Frontier`, and `Term`, then `Scope` and `ScopeSound`,
then `ScopeSeparation` and `Separation`, with `Axioms` as the sink. Each instance module imports the
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

A term of a scope is an `SFlat` over the term container `TSig B`, in `Lang/Scope.lean`. An
`SFlat` is a leaf, a node that keeps the names, a container whose children are entries (`down`), or
a wall whose children are closed terms (`wall`, over `Flat … 0`). `TOp B`
holds one operation per constructor, with the data of the constructor, and `TOp.Pos` types the
children of each operation. At DynamoDB, `Term`, `Body` and `ObjectSlot` in the namespace
`Scoped` are their abbreviations at `dynSig`. **The point of the typed positions is negative: no
term position accepts a slot.** A slot is a `SlotMode` and a term, and only a key of an object
holds one, so a nonsensical term is a type error rather than a rule somebody must remember to
refuse.

`TOp.obj` holds the object payload — the declared key set, the presence of the slot at each key,
and the count of the open block — in one operation. Two consequences are the reason to do it
again:

- Every table over terms gets one object row. Threading the payload's parts by hand is what made
  them agree by convention rather than by type.
- A `Finset Name` together with a function off the membership subtype makes the no-duplicate-keys
  premise disappear. Both a repeated name and two orderings of one object stop being
  representable.

A primitive is one operation, `prim`, over the primitives of the universe. At DynamoDB the
primitives are `Ground`, with the constructors `base` over a `GroundKind` and `literal`, so a
table over terms states every ground base in one row. `opaq` denotes the top of the universe.

`SlotMode` carries the current-schema rule. A required slot remains required on both
current-schema sides. A `fill` slot is required on the write, and its read gives an absent name
the slot's constant. `req` and `opt` are self-dual and the fill is not. An alternate reader of a
present value is `Codec.extendRead`, over the codec of one current term.
Structural operations, including disjointness and union certification, operate on closed codecs.
They cannot observe an alternate reader. They read a fill through its presence only: on the read,
union certification accepts a fill beside a `req` slot and beside no other slot.

**A stratum owes a companion in each of these places.** Miss one and the failure is not a build
error but a silent "everything": the analysis stays sound and stops saying anything.

| Companion | For the object | Why it is owed |
| --- | --- | --- |
| a denotation clause | the `obj` row of `TOp.run`, generic | the meaning must dispatch with no case split at the use site |
| a spec projection | `Closed.spec` | a slice reads an object option's names and literals off the spec |
| a premise carrier | `Scoped.Obligations`, at the object node | semantic side conditions are structural, not global |
| an emitter clause | the object row of `src/codec/lean.ts` | the bridge writes terms in this language, and a constructor it cannot spell breaks it |

The denotation clause and the premise carrier are generic, and each universe inherits them. The
spec projection is a DynamoDB table.

The spec projection is owed only by a stratum that holds names. A policy answers to no name.
Every other row is owed unconditionally.

The spec projection separates a name's presence from what the name holds. The split is
Rémy's, from the 1989 record and variant extension of ML. A field type carries presence
beside the value type, so an analysis keeps exact negative information about a name.
`litSubAt` reads both: the one current-schema presence fact, and the pin of a name: its
adapter word and its set of alternatives. No reader reads a codec.

The emitter clause is owed for the same reason as the rest: the bridge is part of the
correspondence, and a stratum whose shape the emitter cannot spell produces committed vector
output that typechecks against nothing.

---

## Where a side condition goes

The first thing to settle when adding a rule. `Scoped.Typed` keeps the syntactic, fuel-free
premises only.

| A premise that is | goes in | consumed by |
| --- | --- | --- |
| decidable from the term | `Scoped.Typed` | the judgement itself |
| about what a codec does: its write half, its read half, an iso, a resolution | `Scoped.Obligations`, as the compatibility of a union and `IsoCancels` are (`TOp.obl`) | `Scoped.Closed.sound`, and `Closed.extendRead_lawfulCore` through `Closed.sound` |
| a rule of one universe on a set element | the `elem` field of the universe's `SetF`, which `Scoped.Obligations` does not carry | no law: soundness does not read it |

`TOp.rule` answers `none` for the alternate reader (`legacy`), so a typed closed codec holds none.
Therefore `Scoped.Closed.sound` proves `Lawful`, which is one inverse law over
the orientation (retract at the host, canon at the dual) and writes, for every typed closed codec
whose obligations hold. The induction proves `Lawful` alone.
`Lawful.core` gives `LawfulCore` from it. An alternate reader is `Codec.extendRead` at the codec layer. Its read passes only what the current
codec writes, so `Closed.extendRead_lawfulCore` proves `LawfulCore` for it over a typed closed
codec that meets its obligations, with no premise. `ReadsCoherently` is the coherence of the alternate reader:
where both readers read an attribute, and the current codec can write the older answer, the two
answers agree. `extendRead_p_union` proves the premise equivalent to order-freedom: the first-match
presentation equals the order-free union of `p` and the gated `r`.

Choosing wrong is not a build error. A semantic premise in `Scoped.Typed` makes the judgement
undecidable; a syntactic premise in `Scoped.Obligations` becomes a burden every caller carries.

---

## Termination

A proof by recursion on a term of a scope is a structural recursion on `SFlat`: each child of a
node is a value of the argument function of the node, a child of a container is an entry, and a
child of a wall is a closed `Flat` term. So no measure appears in a statement, in
`Obligations` or in a rule. That is the whole difference between it and a fuel parameter.

A recursive codec recurses on its input, not on the term. The solution of a closed codec reads each
input at the stage that the input's own depth names, by the depth of the universe: `Syn.d`, which
is `Attr.depth` at DynamoDB. The depth reads no orientation, so a stage is one stage at both
orientations. That budget is a structural recursion on the input, so the meaning of a closed codec
still reduces in the kernel, and the bridge states its vectors. A well-founded budget evaluates and does not reduce in
the kernel.

---

## Recursion

**A recursive codec is a closed codec.** A closed codec is one flat guarded scope
(`Scoped.Closed`): a system of entries. Each entry is a term that names the
entries of the scope. Above every guard an entry names an earlier entry, below a container any
entry, and below a wall no entry. The meaning of a closed codec at a root entry is the solution of
that scope at the root (`Scoped.Closed.meaning`), `solve` of its normal form. The stages of the
scope start at the bottom, and each applies the entries to the one before. Each input reads the
stage its own depth names.

**The guard is a checked condition on the graph.** `Flat.Guarded` asks that each entry occurs
below a container and below no `held` and no older reader. The guard of a graph, `Graph.guarded`, is
`graphGuard`: no leaf under a wall, and no cycle of unguarded edges. The graph that the host prints for a
closed codec has no leaf under a wall. The graph form of a stratified system passes `graphGuard` under each
renaming of its entries (`graphGuard_of_rename`, `SSys.graphGuard`). So a graph that `Graph.guarded` refuses
has no stratified form. The guard refuses two shapes, and each is a graph with no stratified form:

- an entry that reads its own input, as an entry whose body is `ref 0`
  (`Graph.unguarded_no_strat`) or `union [ref 0, string]` (`Graph.option_at_input_no_strat`).
  The stages of such a term never grow;
- a `held` between an entry and its reference (`Graph.held_on_path_no_strat`). The caller-side
  function of a `held` can make the input deeper, so a container on the path does not bound the
  depth.

A stratified term names an entry above every guard only below its own entry, and names no entry below
a wall, so a stratified system carries the guard by construction. The graph form of a closed codec
(`SSys.graph`) has no leaf under a wall, and each unguarded edge lowers the entry (`SSys.order`).

**A wall reaches no cycle.** A wall is an operation of kind `wall`: a `held`, including the
library adapters `number`, `decimal` and `opaque`, or an older reader. A wall reads its argument
through caller code at any depth. A wall that reads an entry on a cycle makes the flat system
non-contractive. The host refuses a wall whose argument reaches an entry on a cycle. So a closed
codec is one flat guarded scope, and the scope has one solution at the maps (`scope_solution`).

**Stability needs the guard alone.** `ContractiveV` says that agreement below a depth at every
entry gives agreement one layer deeper. `contractive_of_guarded` derives it from the guard. From it
each stage and each later stage agree below the depth of the stage (`sysStage_agree`). The
solution is a fixed point of its system at each orientation (`solve_fix`), and lawful stages give
a lawful solution (`lawful_solve`). No option of a body has to be disjoint from another for any of
these.

**Soundness runs over the scope.** `Scoped.Closed.Obligations` asks the obligations of the scope at
each stage of its normal form, given that the stage before is lawful. `sound_term` proves
`Lawful` for a term of a scope whose entries are lawful, and `lawful_strat` carries the laws to
the solution (`Scoped.Closed.sound`). An entry of the solution has its write domain as its held set
(`SSys.sol_eq`), so the held-set theorems stay closed.

**`opaque` is the identity.** With one carrier, each datum identifies itself, so the union of
everything self-identifying (`opaqUnfoldClosed`) sends each datum to itself. `opaque` denotes the identity
codec `Alg.idCodec`, and it owes no compatibility and no contraction. The union is a theorem:
`Closed.Adm_opaqUnfold` and `Closed.AdmA_opaqUnfold` state that the union admits what `opaque` admits.

**A held-free closed codec is a restriction of `opaque`.** An adapter reads its argument through
caller code: a `held`, an older reader, or an object with a fill slot. A closed codec is held-free
(`Closed.HF`) where its root reaches no adapter on its graph (`belowTop`). Such a codec writes only what `opaque` writes (`Closed.confluence_W`), and reads only what `opaque`
reads (`Closed.confluence_R`). A `held` re-indexes the values of the caller, so
the inclusion does not reach a `held`.

**The analyses read a recursive codec through its meaning.** The read row `Closed.AdmA` reads the
meaning of the closed codec. An entry reads the codec that its scope solves, as the rows of
`opaque` do.

**The host spells recursion as a `ref` node, and the bridge prints a closed codec.** A `ref` node
names an entry of the scope that binds it, and an unbound name is a node with no target. The
emitter prints one flat scope: the entries of each cycle of the term graph, cycle by cycle, and a
cycle comes after each cycle that it reaches. Then come the root, where no cycle holds it, and each
child of a container that is not yet an entry. A child below a wall prints in place.
Each term of a cycle is an entry, and a `ref` node whose target is an entry prints as the reference
to that entry. Any other `ref` node prints the term it names. The emitter refuses a term with no
scoped form: an unguarded cycle, a wall that reaches a cycle, or an open fragment. The host refuses a wall whose argument reaches an entry on a
cycle, at the wall where each `ref` of the argument has a target, and at the scope that binds a
`ref` of the argument otherwise. A wall over an acyclic entry stays legal: the emitter prints the
acyclic `ref` in place, so that entry is no leaf of the model. A guard row prints the graph of the term instead: one flat
system with no order on its entries, which the flat guard `graphGuard` decides. Each recursive vector asserts that the
guard accepts its term. The host's `union` refuses the two shapes the guard refuses. One is an
option whose spine reaches a recursive `ref`. The other is an option where a `held` sits between the
entry that a recursive `ref` names and the `ref`. The host's `union` also refuses a `ref` that no
scope binds. Recursion below a list or an object stays declared, and the decision decides it. The
host's `heldFree(t)` reads through a recursive `ref`, as the model's `Scoped.Closed.HF` reads each
entry that the root reaches.

---

## A path into a closed codec, and the strong law

**A path is a list of segments.** A segment (`Seg`) is a name into a map, or a position into a
list. `Rooted.at` gives the frontier of a closed codec at a path: each frame that can stand at the
path, or a refusal. A frame (`GFrame`) is a graph term of the scope of the codec. One
segment reads the slot of a name, the term of a position (`listChildG`), the options of a union,
and the body of an entry. An entry unfolds through the graph of its scope. The unfoldings have a
bound, the count of the entries plus the first step, so the walk ends.

**The store refuses a segment apart from the term.** A term that stores one member (`μAt`, which
reads the element of a set through the body of its entry) apart
from the member of the container of the segment gives no frame (`apartG`). So a name on a list,
a position on a map, and a primitive of another member give no frame. A closed object at a name
that the object does not declare gives `never`, and so does a list shape with no spread at a
position past its prefix: no readable value holds the segment. `opaque` gives `opaque` at every
segment. A `refine`, a `held` and an alternate reader give a refusal where
they are not apart, because a frontier cannot carry a restriction. A position past the prefix of a
list shape with a suffix is a refusal, because the term of the position depends on the length.

**The write of the store at a path is `putPath`.** A name of a map takes the value (`MapOf.put`). A
position inside a list takes the value, and a position past the end appends the value. Each
segment before the last must hold an entry. The store refuses every other attribute.

**The strong law: an attribute that a closed codec reads stays readable after a write at a path.**
`Closed.strong_law` takes a typed closed codec whose obligations hold, and a writer that agrees
with each frame of the frontier: each frame reads what the writer writes. An attribute that the
codec reads stays readable after the store puts, at the path, what the writer wrote.
`GFrame.path_law` composes the law from one law per segment, `StepLaw`. Where a frame reads an attribute, the store refuses
the segment there, or one child reads the entry and keeps the attribute readable under a write of
a value that the child reads. Each operation of the graph proves its law one time: the object at
a name, the list at a position, the union through its options, an entry through its body at the
solution, the bottom, the top, and each term that is apart from the segment.

**The law reads lawful frames, and a typed term gives them.** A primitive, a set, a `held`, a
`refine` and an alternate reader that are apart from the segment read no attribute that the store
accepts there, where the codec is lawful. So the step laws read a lawful node at each frame that
the path reaches. `Closed.lawfulNodes` gives that premise from `Closed.sound`: a typed closed codec
whose obligations hold is lawful at each node of its graph, at the solution.

**Narrowing is the restriction by a range idempotent, and the stored views decide it.** A clause
is a closed codec whose root entry is an open object: each named key is required at a term, and
every other name is open. Each option of a union is a closed codec with its own root. `narrowC`
keeps each option whose stored view the graph decision does not separate from the stored view of
the clause. The precondition of a read is the stored admission, and the stored view admits each
attribute that its term admits (`views_apart` at the dual). The decision reads a raw `held` as
disjoint from the bottom alone, so a tag behind an adapter separates only under the stored view. On
an attribute that the stored view of the clause admits, the narrowed options read what the options
read (`narrowC_reads`), and a dropped option reads nothing that the stored view of the clause reads
(`narrowC_drops`). The slice of a certified union (`AltClause.extractC`) keeps fewer options: the
options that the clause describes.

**The host takes the clause as a codec.** `extract(codec, pattern)` keeps the options of the codec
that fit the pattern, and `exclude(codec, pattern)` keeps the rest. A field that may be absent,
against a pattern that requires its key, splits the option into a present part and an absent part:
the extraction keeps the present part with the key required, and the exclusion keeps the absent
part. A dissection splits no member. A pattern has no decode of its own, so a pattern is a set of
values: an option fits where every value that the option decodes, as written, is a value of the
opening of the pattern. The opening holds every undeclared name of an object pattern at `opaque`.
The host decides this on a fragment, and the order is the value order of the meet: an option fits
exactly where the meet that reads the option as written and the pattern open is the option. `opaque`
is the top, and a term that holds no value is the bottom. The value side reads a key that holds
undefined as an absent key, because DynamoDB stores no undefined: `undefinable(...)` decodes the
absent row to that key, and `opaque` refuses that key on a write. An open block that admitted the
key would relate the absent row to two values, and decode would be no function. So `opaque` is the
top of the values only up to that reading. A literal fits a literal of one base and adapter, and a
literal fits its base. A base fits itself. A set fits a set where its element fits. An option fits a
union that holds a member of the option. A refinement fits where its inner term fits, and an option
fits an older reading where it fits the current form. Two objects compare on the alignment of their
names: each slot of the option fits the slot of the pattern, and the open block of the option fits
the open block of the pattern. At the absent row, a required slot fits every slot, an
`undefinable(...)` slot fits an `optional` slot, an `optional` slot and an undeclared name of a
closed option fit only an `optional` slot. A `withLegacyRead(...)` slot always gives a value, so the
slot fits as a required slot, as the model's `AltClause.admitsC` reads a fill. A name that the
pattern leaves to an `opaque` block fits every slot. A list with fixed positions fits a list pattern
with the same positions where each position fits. A list fits a list of one element where each
position fits that element. An array declares no position, because its length is a run-time fact, so
an array fits no fixed pattern. Any other pair fits only where the two terms are one term. The meet
of two codecs reads the same walk at the relation order, which counts the absent row of a stand-in,
so a `withLegacyRead(...)` slot lies below only a slot of the same stand-in. `narrow(...)`,
`disjoint` and the stored apartness read the stored rows, through the walk of the separation. A
pattern that no option fits is an answer: the extraction is `never`, and the exclusion is the whole
codec. The extraction of `never` is `never`. A pattern that holds a refinement is a refusal, because
no function decides whether an option lies inside a predicate. An object with a union at a field is
the union of the objects (`Term.product_join`), and a fixed list is the same product over its
positions. The slice goes into that field or position, and the result stays compact, as the Extract
of TypeScript reads it. An option with a union at a field keeps the part of the union that fits the
pattern, in place. So the extraction has no option that the original lacks. The rejection has one
option for each field or position that the pattern names, because the complement of a product is no
product. A union pattern is no product of its keys, so it splits the option, and the parts that fit
stay. A dissection changes no member, because its tag table is keyed by literals.

**The strong law after narrowing needs a condition on the update, and the port states the condition
as data.** `narrowC_law` holds for an item that the stored view of the clause admits, and a write to
another item can reach a dropped option. The DynamoDB port states the condition as a precondition
(`Closed.preconditionOfC`): a conjunction of conditions, each a path into the item and one test that the
store evaluates, `in`, `type` or `exists`. The precondition reads the stored view of the clause, so
a tag behind an adapter gives the test of its stored literal. The port states the precondition
exactly or refuses: on an item, the precondition holds exactly where the stored view of the clause
admits the attribute at the path of the union (`Closed.preconditionOfC_exact`). A literal, a union
of literals at one base, a base, `opaque`, an older reader (an alternate reader, whose stored view
is `opaque`) and an open object whose slots are each required give a precondition. An entry gives the
precondition of its body. Every other stored view refuses, and so does a clause with no key below
the root. `Closed.narrow_law_precondition` is the narrowing law with the precondition in
place of the admission.
Rotorise states the precondition as data and builds no expression string. An expression library
renders the condition expression.

**The host's path API follows the model.** `at((p) => ...)` on an item codec gives the codec at a
path, with the path as `path()` and as a list of segments. The walk of `at` gives the three answers of
`Rooted.at` at each segment: the frames, no frame where the store refuses the segment, and `never`.
The walk reads a `ref` node as the model reads an entry. The walk compares two terms by structure, so two
declarations of one term are one frame. A path resolves where the frontier holds one term, so the
codec at the path agrees with each frame, which is the premise of `Closed.strong_law`. A frontier of two
terms, or of one term beside `never`, gives a codec that returns a refusal value on use, and the
message names `narrow(...)`. A frontier of `never` alone throws at the call: no codec declares the path.

`narrow(located, pattern)` is `narrowC`. The pattern is a codec, and the clause is its term with
every object open at every depth, as `extract(...)` reads a pattern. Each declared key stays required at
the term of its codec. The precondition of a nested object is `type M` at the object, then the
precondition of each name. The host keeps each option whose stored view the
host's disjointness test does not separate from the stored view of the clause. The call adds no
segment to the path. The path type narrows too, and the path type is coarser where the path type
knows only the decoded types. `preconditions(at(...))` is the conjunction of the preconditions of
each `narrow(...)` on the path, by the rules that `Closed.preconditionOfC` states, or a refusal value that
names the path where no exact precondition exists. A path with no `narrow(...)` has the empty
conjunction. The caller puts the preconditions in the condition expression of the write.

**Two checks put the host's path decisions to the model.** The path vectors walk the grounded pool:
each pool codec under an object, each path of declared names and positions below the codec to a
fixed depth, and each clause of the pool's vocabulary at each option name of a union. Each path
records the decision of the host. One theorem per codec states that `Rooted.at`, after `narrowC` for
a clause, gives the frontier that each decision names, and the kernel decides the theorem. A
recursive union has clause rows as any union has: each option is a closed codec with its own root.
The two-spelling check builds the pool again with each leaf and each tag behind a `ref` that
closes no cycle. The model reads one term in both spellings, so each decision of `at` must be the
same, and a difference is a host reader that stops at a `ref`.

**A path row certifies the meaning of a resolved decision.** The walk of the model's frontier, over
the graph of the print of the root, names the position of each frame (`Closed.frameAt`). Where the
host resolves one codec, the row states each frame of the frontier at the position of the resolved
node, so the row is an equation per frame. A caller's function is a variable of the theorem, so two
frames are equal only where the two hold one function, and equal frames have one meaning
(`pathReadC_resolved_sem`). `leanPath(...)` refuses a resolved row where the model reaches a frame
at no position of the resolved node. `pathKindC` names the decision of each frontier, and each row
reads it. One codec is a frontier of one frame, by `frameSameC`, which compares each datum and
assumes each pair of entries that the two terms reach together while it compares the bodies, and
two declarations hold two frames (`two_frames_of_ambiguousC`).
`frameSameC` reads no function and no fill value, so two refinements by two closures are one codec
to `pathKindC` (`pathKindC_reads_no_closure`). There the host decides by the identity of the closure,
and a row of two declarations has no certificate.

A vector puts the host's preconditions to `Closed.preconditionOfC` at each narrow path of the pool
(`PreRowsC`), the rows of a nested object included.

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
A dissection is a `union` of object members that are pairwise disjoint: two members
differ at a required literal name with disjoint alternatives, or the name intervals they declare
cannot be satisfied at once. `select` admits an object option by attempt, as it admits every other
option. The test certifies both cases: the two bodies are disjoint. A sub-selection of a
certified union stays certified, because the certificate is `Pairwise` and `certAllC_sublist` keeps the certificate on a sublist. The
host decodes a certified union through an index over the literals that its options pin, at the root
or under a key, and attempts the options where no such index exists. The index changes no answer,
because the options are disjoint, and no term carries it.

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

An alternate reader is `Term.legacy`, and its codec is `Codec.extendRead`. `Codec.extendRead` tries
the current reader first and then the alternate reader, and it passes only what the current codec
writes. No structural analysis reads the alternate reader: each row reads `legacy` from its own
codec, as it reads an opaque leaf.

### One codec, stated once for both sides of the pair

A constructor is a prism — `Ctor`, with the laws `out_into` and `into_out` — and those two are the
round-trip and completeness clauses at a constructor, so the prism half of every lawfulness proof
is discharged once.

A ground codec needs no prism: `fiberCodec` is the identity on the data of one member, and every
universe's ground codecs share its one lawfulness proof. `carriedCodec` sits over the prisms: a
payload map at each orientation, carried by one summand (a prism with the member that it stamps),
the shape underneath every product. **The model states a codec once for both sides**: one inverse law of the payload
map, `F o` inverted by `F o.op`, is the lawfulness of every product, and `carried_f` is the
inversion that every product's proof goes through.

**An object is the product of its slots.** A slot reads the lookup of one name, so a slot is a
codec on the presence lift `Option V`: a present value goes through the slot's codec, and absence
takes the slot's behavior at the orientation (`absentOf`). The product runs over the declared names
and the present names (`objP`), and its inverse law is the inverse law of each slot (`objP_inv`).
The payload map `objAt` is that product, for every table. A fill reads an absent name as its
constant and the write sends the constant to a present name, so a fill is not an inverse: the
inverse law holds for a table with no fill (`noFill`).

**A product of two closed objects reads each name through the factor that declares the name.** A
closed object refuses a name that it does not declare. So where two closed objects declare disjoint
names, the payload map of the merged table is the pairing of the two payload maps (`objAt_union`).
The merge is the union of two records (`MapOf.union`), the left value first at a shared name, so the
merge is associative with no premise. A factor is a sum of closed objects, and the product of two
factors (`MapOf.prod`) holds each merge of an option of the first factor with an option of the
second, outer over the first. The product is associative on terms (`Scoped.Term.product_assoc`), so
the two nestings of three factors give one term. The term of a product is the union of the merges,
so the meaning of a product is the join of the meanings of the merges where the merges agree
(`Scoped.Term.product_join`). The host operation is `meet`, as TypeScript reads `A & B`: two closed
objects at disjoint names meet as this product, and at a shared name the host meets the two fields.
Each factor reads open, so two objects meet on the alignment of the names: a name that one factor
declares meets the open block of the other factor, which is `opaque` where that factor is closed,
and the two open blocks meet. The result closes again where both factors are closed. The meet of two
recursive factors is recursive: a pair of nodes that the walk meets again below itself is a
reference to the meet of the pair. The meet is the intersection of the two relations between stored
rows and decoded values, each side read open. The model states the meet of two codecs as the
intersection of the two graphs at each orientation (`Codec.meet`): the greatest lower bound of
`Sub`, and lawful where both sides are lawful. The model holds no codec at the open block of a
closed factor: a codec is a partial map, so no codec lies above two codecs that send one input to
two outputs, and the model's `opaque` is the identity. So the model states the product of two closed
objects as the pairing of two payload maps (`objAt_union`), and not as `Codec.meet`. At a shared
name, a required or a `withLegacyRead(...)` side makes the slot required, because a stand-in and an
absence share no absent row, and `optional` with `undefinable(...)` is `undefinable(...)`. A factor
that lies below the other is the meet, and a union distributes only where neither lies below the
other. Two lists meet on their aligned rows. A refinement meets as the refinement of the meet of its
inner term, except against an adapter, which the meet refuses. A `held` or an older reading meets
only a part that it lies below. The model has no term for the meet at a shared name.

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

Every separation is one appeal to `Closed.Separates`, which takes the write domain and the read
row of each meaning, and asks only that each pair be disjoint. Kinds, members, tags
and admissible sets are ways of building those families rather than four separate conditions.

The meaning of a closed codec holds its own domains: the write domain is where `e` is defined, and
the read row `Closed.AdmA` is where `p` is defined. No Boolean row stands beside the meaning. The
value-side separation predicate `Closed.SepJV` is one clause, and the attribute-side predicate
`Closed.SepJA` is one clause. An alternate reader cannot add a structural exception, because the
read row asks the meaning of the alternate reader's own codec.

**One test decides both.** `select` attempts every option, so option admission *is* the domain of
the meaning of the option, with no premise on the codec and no exception for an object. So the
joint predicate and the admission a discharger consumes are one test, and
`Closed.pairwiseCompat_of_separated` proves that a separated union of lawful options meets its
obligation.

**The direction has a standard name.** It is the abstract interpretation of Cousot and Cousot,
1977: a coarse test that over-approximates a precise one transfers disjointness downward, and a
tighter test does not. The principle is why a certificate may be proved over an approximation at
all. This development spends it once. Each entry of the view at an orientation accepts what the
entry accepts (`view_entries`), so two closed codecs whose views are disjoint accept no common datum
(`views_apart`).

**The outer carrier has a separate read-side fact.** An alternate reader can read an attribute
outside the current term's member. `Closed.extendRead_reads_n` records a string core that reads a numeric
attribute through its alternate reader. The structural classifier has no row for the outer
carrier.

`ScopeOrthogonality.lean` states the discharge on what the resolver consults. `Closed.Separates`
reads the write domain and the read row of each meaning, and `Closed.pairwiseCompat_of_separated`
is the discharger stated on what `select` actually decides by.

### The classifier, and what it is the specification of

The union obligation is compatibility, and the certificate is sufficient for it.
`Closed.viewsDisjoint` certifies a pair where the two closed codecs are orthogonal.

**The certificate is orthogonality.** A term denotes a partial isomorphism. The caller view,
`viewG` at the host, states its domain. The stored view, `viewG` at the dual, states its range. In an inverse semigroup, two elements are
orthogonal where the product of their domain idempotents is zero and the product of their range
idempotents is zero (Lawson, *Primer on inverse semigroups I*, Lemma 2.16). `Closed.viewsDisjoint` asks
the decision `Closed.disjoint` of the two caller views and of the two stored views. The decision
reads a raw `held` as disjoint from the bottom alone, and a view holds no `held`, so a `held` reaches the
certificate through its views. On a term with no `held`, the caller view is the term itself. The
view of a `union` is the union of the views of its options. A reference to an entry stays a
reference, so a `held` below a recursion reaches the certificate too
(`Closed.viewsDisjoint_heldBelowMu`). The argument of that `held` reaches no cycle, because a wall
reaches no cycle.

**The stored view drops a predicate over an adapter.** A view keeps a refinement as it is only
where the inner term reaches no adapter. Elsewhere the view keeps the predicate of its
caller side and puts the truth of the meaning, `Mean.truth`, at its stored side, because the
stored side tests its predicate through the adapter that the view drops. DynamoDB names the truth
alone at the stored side, so the caller view keeps the refinement, and the stored view keeps the
truth there. An entry stays an entry in the view. `Scoped.disjoint` reads through a refinement, so
the predicate that a view keeps changes no verdict.

**The rows of the test are the laws of a product and a sum.** A product admits no value where
one factor admits none. A sum admits no value only where each summand admits none. A required
name and a fixed position are factors: two objects are disjoint at one name where one slot is
required and the two terms are disjoint, and two lists with no spread are disjoint at one
disjoint position. An optional name and a spread are summands, because the absent name and the
empty list inhabit them. So two arrays over disjoint element terms are not disjoint. A union is
disjoint from a partner where each option is.

**The test reads a closure through its inner term.** The admission of a `refine` at a `closure`
is a function. A refinement admits a part of what its inner term admits, so the refinement is
disjoint from each partner that its inner term is disjoint from. A closure refinement beside an
option that writes and reads other slots is disjoint from the option.

**The certificate is one row of the union's decision.** The union's one law is compatibility
(Lawson: `s ∨ t` exists iff `s ∼ t`), and compatibility is two halves of agreement: two writers of
one value write one attribute (`Agree` at the host), and two readers of one attribute read one
value (`Agree` at the dual). `Scoped.compat` decides each half per component: the two terms are
disjoint there, or one codec bounds both there. The bottom agrees with every term. Two terms below
the top are bounded by the top (`belowTop`). The decision over
closed codecs, `Closed.compatPair`, takes no oracle. A `held` whose
half, or the half of the `held` inside it, is disjoint from the partner agrees there.
`Scoped.compat_sound` proves each half, `Scoped.compatPair_sound` proves both halves at every
table, and `Closed.pairwiseCompat_of_compatPair` discharges the union's obligation of two
lawful closed codecs.

**The meaning of a union is the join of its options.** The union sends a value to a result
exactly where some option does (`IsJoin`). The join is defined where the options agree at each
orientation, and the first admitter is how the host computes the join (`altCodec_eq_join`). So
over pairwise agreeing options a permutation of the options denotes the same codec
(`altCodec_perm`), and a value that two options admit has no owner. The law reads no
lawfulness.

**The decision is the specification of the library's declaration-time guard, and a checked one.**
The `union` combinator in `src/` accepts a pair where `agrees(x, y)` holds, which is the model's
`Closed.compatPair`, per half and per component. `Closed.pairwiseCompat_of_compatPair` proves each
accepted pair compatible. The combinator refuses every other pair, because the pair is not shown
compatible.

**Two `held`s of one adapter agree where their inner terms agree.** A `held` carries an adapter
word at one side, and a table gives each word its two functions, so two `held`s of one side and
one word carry one adapter. The row compares the two sides and the two words by equality. The
host's `sameAdapter(x, y)` is the same test: one
library adapter by its name, or one pair of caller functions by identity. So `decimal('1')` beside
`union([decimal('1', '2.5'), string('A')])` is accepted, and two caller adapters over one stored
side are refused.

**The host reads an unknown as a decline.** The read side of an alternate reader is caller code,
and the declaration cannot bound its domain. So the host's test declines where it must read an
alternate reader, and a decline certifies nothing. A container of an alternate reader beside a
term of another shape class is disjoint from it, and reads no reader. An unknown read as
"disjoint" is the permissive direction, and so the unsound one.

**The host reads an unbound `ref` as an unknown term.** At a declaration, a `ref` that names the
union under declaration has no target yet. The model has no free variable, and the emitter refuses
such a term as an open fragment. The decision keeps the bottom apart from every term, and two
operations of different classes apart whatever their positions (`AB.of_cls`). So beside the bottom
the unbound `ref` is disjoint, and beside any other term the host's test declines. A list of such a
`ref` beside a string is disjoint from it.

**The caller view of a `held` is its held side.** The host's `decimal` over literals records the
string literals of its texts there, so its caller view is exact, and the views certify it beside a
string literal it does not write. A caller-built `held` keeps the held side that the caller gave.

**The bridge checks both directions.** The emitter states each emittable option pair of the corpus
and of the pool as a separation row, in one list per form, and `formal/scripts/gate.sh` elaborates
the lists. For a pair the library accepts, the row states that `Closed.compatPair` accepts the
pair, and `accepted_of_rows` lifts the row to `PairwiseCompat` where both terms denote lawful
codecs. For a pair the library refuses at compatibility, the row states that `Closed.compatPair`
refuses the pair (`refused_of_rows`). For a pair the library refuses at the guard, the row states
that the guard refuses an option (`guardRefused_of_rows`). A pair that reads an unbound `ref`
takes the same forms, because the decision holds whatever codec the scope later binds to the name. Each row also
states the guard on the graphs of the two options (`Graph.guarded`).

**The emitter refuses a pair that no form states.** A form states the union decision of the host,
its guard and its compatibility test together. Where the union decision disagrees with the guard or
with the compatibility test, `separationForm(...)` refuses the pair. So a host guard or a host
compatibility test that drifts from the union decision fails the suite that emits the rows, and
passes no row.

**`Closed.viewsDisjoint` is sufficient and not necessary.** A decline by `Closed.viewsDisjoint` is not a refutation of
compatibility. Two restrictions of one adapter are compatible in the model
(`compat_of_common_bound`), and no certificate reaches such a pair where the two overlap. The
decision reaches such a pair through the held row: `decimal('1', '2.5')` beside
`decimal('2.5', '3')` is accepted, because the two `held`s carry one adapter and their inner
terms agree.

`Closed.Separated` is what names the separation guarantee over the option list, with
`Closed.separated_of_certAllC` as the certificate's bridge into it.

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
gate emits the generated vector files again, and runs each vector file, the committed samples
included, through Lean rather than trusting a byte comparison. **Refusal vectors are the other half of the same blind spot**: a
positive vector is an agreement about what the library wrote, so a value the library refuses
produces no vector at all — the half of the pair where the two sides could disagree unobserved.

**A vector file holds data, and the kernel checks one list in one theorem.** The emitter prints
each distinct term of a file as one `def`, and each numeral of the file one time. A caller's
function of a term is a parameter of the `def`. A row is the name of its vector, then the data of
the vector, and a list holds the rows of one form. The theorem of a list states
`failing ok L = []` for the comparator `ok` of the form, and `kernel_rfl%` closes the theorem, so
the kernel decides each row. `ok_of_failing` gives the comparator at each row of the list. The
samples, the read vectors and the guards of the pool state one theorem per vector. The slices state
one theorem per union, and the paths one theorem per codec.

**Each comparator has a law in `Calculus/Bridge`, and the law makes `true` the statement of the
row.** `Vectors.lean` holds `check` and `vcheck`, which compare an attribute by `aeq` and a value by
`veq` under fuel: `aeq_same` makes `.same` equality, and `aeq_differ` makes `.differ` disequality,
with `veq_sound` as the twin at `Value`. `Rows.lean` holds `failing`, `ok_of_failing`, the
comparator of each evaluation form with its law (`writesOk_iff` and the others), the lifts of the
separation forms, and the cover of the meet (`meetCoversOk_sound`, `meetCovers_of_rows`).
`ScopePaths.lean` holds `pathKindC` and `pathReadC`, with `pathReadC_resolved_sem` and
`two_frames_of_ambiguousC`, and `frameSameC` with its proved limit `pathKindC_reads_no_closure`.

**A meet row asserts a cover, not an equation.** A row holds two pool factors, the term that
`meet(...)` returned, a value, and the attribute that one factor writes from the value. The kernel
checks that the model's meet term writes the attribute wherever the model's two factors write it,
and that each check settles. `meetCovers_of_rows` lifts the row to the pair of `Codec.meet` of the
two meanings. A row reads each factor as written, and the host reads each factor open, so the
equation is out of reach. A term with a refinement or with a cycle states no row.

**A read row asserts a decoded value.** A read vector states that the model's `p`, at the
attribute that the library wrote, gives the value that `decode(...)` read back, by `vcheck`. The
read rows of the resolutions and of the legacy read gate state the same by `readsOk`. The read
verdicts compare a decision: `Closed.AdmA` against whether `decode(...)` accepted the attribute. Each
row states one value. A law over every value, such as the retract, is a theorem of the model, and
no row states a law.

**A caller's function is a variable of the theorem.** The emitter prints a caller's predicate and
an older reader as variables, and a caller's adapter as a generator `caller n` of the caller table
`κ`. The theorem quantifies each predicate and each reader, and a verdict that denotes a term
quantifies `κ`. Where a row needs the answer of a caller's function, the emitter pins the function
at the answers that the host recorded. `veq_pin` and `aeq_pin` prove that each function with those
answers equals its own pin, so the row states the former theorem at each such function. An
evaluation vector reads `libTable noCallers`, so the emitter refuses a caller's adapter there: the
vector would have to run the adapter, and the model has no name for a caller's closure. A shipped
predicate over an inner term that writes a value other than a string is refused too, because
JavaScript coerces where the model does not, and the vector would prove the wrong theorem. So a row
holds at every caller function, or at each function with the recorded answers. The laws that a
caller owes stay a written premise on both sides.

**A red bridge check that returns immediately has read nothing.** The bridge shares a build cache,
and a racing run fails at once over an unchanged tree. Judge that check by its duration before
judging it by its exit code.

**The kernel checks the bridge, and evaluation only names a failure.** The one `#eval` of a row
file prints `failing ok L` of each list at one instance of the caller functions, so the file names
each failing row. The gate passes a file that prints nothing. A printed value proves nothing, and
`native_decide` adds an axiom of its own for each proof, which is outside the advertised axiom base.
A row that the kernel refuses only at other caller functions goes unnamed by the `#eval`, and the
theorem of its list still fails. A checked row is a theorem. Each generated file ends with
`#assert_axioms_module`, which checks the axioms of the theorems that the file declares against
`sanctionedAxioms`, and the gate fails a file whose last line is not that check.

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

**The nesting bound.** `Nesting.lean` and `ScopeNesting.lean` state the one place the attribute
algebra is larger in the model than in the store, deliberately. The list and map constructors nest
without limit by construction, so a typed closed codec can write an attribute the store refuses,
and `Closed.not_storable_of_typed` is the witness: a typed closed codec, a value that it writes, an
encoding outside `Attr.Storable`. The model must be able to **state** this, because a target certified
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
the element writes one member of `S`, `N` or `B` is a rule of DynamoDB, `SetElem`, which the
obligations of a closed codec do not carry. `SetElem` is the `elem` field of the DynamoDB set
former `dSet`, and soundness does not read it. The carrier holds no set of `Value`, for two reasons. The kernel rejects a
nested `Finset`, `Multiset` or `Quot` of the datatype being declared. A list carrier needs a
canonical spelling that every set codec enforces by refusal.

**The n-ary literal is a union of singletons.** A literal carries one value, and several
alternatives are a `union` of singleton literals. The route was refused while a literal held a set: the
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
emitter prints a caller's closure as a variable where the statement holds at every function. Where
the statement must run the closure, the emitter refuses the term, rather than emitting a vector
about a codec the model cannot express, and its message says so in the caller's vocabulary. That
refusal is the record, and it is the shape every gap of this kind takes.

**A core union requires its discriminator.** The model selects only an input that carries the
required discriminator. A caller that accepts an old input extends the whole union's codec with
one alternate reader (`Codec.extendRead`). The alternate reader owns that migration after core
selection refuses.
`Closed.spec` contains no migration field.

**A former reads the node that a reference names.** A reference and its target are one node of
the term graph, so each host rule that inspects an argument reads the node at the end of the chain
of references, at run time and in the type. A reference that no scope binds is a free name, and
the scope that declares the name judges its own closed copy. A rule that read the spelling of its
argument gave a reference and its target two verdicts: a refusal escaped through a reference, and a
valid codec was refused through one. A meet and an entry key need the node at the declaration, so
each of these refuses a reference that no scope binds yet.

**One judgment types the built graph.** The judgment reads the node that each child names. It
holds one case per host rule:

- A declared list position at a term that holds no value refuses the list.
- A field that the row always writes, at a term that holds no value, refuses the object.
- A set refuses an element that writes no single member of `S`, `N` and `B`, and an element with a
  read widening.
- A wall refuses an argument that reaches an entry on a cycle.
- A union refuses an option whose spine reaches a recursion that the guard refuses, and a pair of
  options that the declaration cannot show compatible.
- The guard refuses a recursion with no container on its path, and a recursion with an adapter on
  its path.

**A term holds no value where the model gives it an empty held set, and the term decides the
emptiness.** So `never` holds no value, and so does a union whose every option holds no value. A
refinement stays out, because no function decides that a closure admits nothing. A `held` over such
a term holds no value in the model, and the host admits that `held` in a declared position. The
meet reads the same predicate for a factor and returns `never` where one factor holds no value, and `nullable` reads it for the null point.

**The judgment runs where each name that it reads is bound.** Each former builds its codec through
one function, which runs the judgment at the declaration. `union` runs the judgment on its own term.
A judgment that reads a name that no scope binds passes at the declaration. A scope closes a copy
of its entries by lexical scope: each `ref` of the copy binds in the record of the scope, and a
cycle is a recursive binding of that record. A scope runs the guard on each entry of the copy, then
the judgment of each copied node. A fragment stays open and refuses each use, so the result of a
scope depends on its own arguments only. The type of a list reads a free name where the scope
binds the name later, so the run time alone refuses a list position that the scope binds to a term
that holds no value. Agreement reads the meaning of two options, so the run time alone refuses a
pair of options.

**An entry carries the capabilities of the node that its references name.** An entry whose node
writes `S`, `N` or `B` offers `.set()`, in the type and at run time. A reference and a literal carry
no `.set()` of their own, so the scope gives such an entry the set of itself. An entry that names a
dissection keeps the options of the dissection in declared order, so a meet distributes over them.

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

**Test machinery drives the arbitraries; it does not hold them.** An adapter states its own
arbitrary and shrinker where its pair is partial, because how a codec generates is a fact about
that codec rather than about testing, and `held` takes the conversion, the arbitrary and the
shrinker together as data — they go into the term, which is the codec's whole definition. What lives in the testing entry point is the
machinery that *drives* them: the derivers that walk a term to build an arbitrary, the shrinker, and
the law checkers. **The term is the only source.** Where an arbitrary was a projection of the term
that the derivers read before the term was consulted, one fact travelled two paths and could
disagree with itself; now a caller that wants to share an arbitrary names it rather than reading it
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
- New universe → a `Sig`, a `Mean` instance over it, a `Syn` at the host orientation, its
  `TopLaws` where the held-free theory or the soundness of a view must hold, its
  `PrimAdm` where a verdict at a primitive must reduce without the codec,
  its `Leaf` where the decision must compute, and its `Shapes` and `Scoped.Laws` where
  the soundness of the decision must hold. Make the module reachable from `Axioms.lean`.
- New rule → put each term premise in exactly one of `Typed` and `Obligations`.
- New term recursion → a structural recursion on `SFlat`, with no measure.
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
