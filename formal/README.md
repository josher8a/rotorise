# Codec calculus — Lean 4 mechanization

Mechanizes the specification in `docs/blueprint/src/content.tex`. The doc stays normative; this package is the proof
assistant checking it, and every deliberate divergence from the doc is commented at the
definition it touches.

## Layout

| Module | Content |
| --------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Calculus/Alg/Codec.lean` | The generic layer starts here, in the namespace `Calculus.Alg`. The record `Codec` and its laws `Lawful`/`LawfulCore` over carriers `V`, `A` and `M`, with the member of an attribute as a parameter of `Lawful`. The module imports nothing |
| `Calculus/Alg/Combinators.lean` | `restrict`, `through`, `extendRead`, `fiberCodec`, the union by the first admitter (`select`, `altCodec`), the side conditions (`Carrier`, `IsoCancels`, `ReadsCoherently`), and the law of each, over any carriers |
| `Calculus/Alg/Relations.lean` | `Sub` (graph inclusion and the information order), `Codec.Equiv`, `Canon`, `Compat`, the reads below one bound (`readAgree_of_sub`), the laws of the join (`lawful_altCodec`) and the common bound (`compat_of_common_bound`), over any carriers |
| `Calculus/Alg/Lists.lean` | `traverse` and its laws off the pivot `traverse_eq_some`, the `filter` facts, and `carriedCodec` with its instance at a traversal, `entrywise` (`lawful_entrywise`), over any carriers |
| `Calculus/Alg/Positions.lean` | The positional theory: `align`, `slots`, `alignL`, `slotsL`, the zip laws, `tuple_retract` and `list_retract`, over any carriers |
| `Calculus/Alg/Maps.lean` | `funImage` and `setImage` over any key type, `FieldSem` and `RestSem`, and the keyed map `MapOf`, which keeps the namespace `Calculus` so that field notation reaches its extensions |
| `Calculus/Alg/Containers.lean` | `listCodec` and `objectCodec` over the list and keyed-map prisms of a universe, with their laws and carriers |
| `Calculus/Alg/Recursion.lean` | `AgreeLe`, `Contractive`, `muCodec` and `lawful_muCodec` over one depth function of the carrier, and the agreement lemmas of the combinators |
| `Calculus/Lang/Term.lean` | The universe signature: `Syn` (the syntax) and the class `Sem` (the meaning), with the formers `ListA`, `MapA` and `SetF`, the adapter words `Word`, and the tables `TableAt` and `Table` |
| `Calculus/Lang/Scope.lean` | The closed codec over a signature: the term container `TSig`, a scope term `Scoped.Term`, its graph form `Scoped.Graph`, and `Scoped.Closed`, a DAG of scopes. Its meaning `Scoped.Closed.meaning` at a root entry is the solution of the scopes at the root |
| `Calculus/Lang/ScopeSound.lean` | The judgement `Scoped.Typed` of a scope term through the rule `TOp.rule` of each operation, the obligation `TOp.obl` of each operation (the cancellation of a `held`, the compatibility of a union), `Scoped.Closed.Typed` and `Scoped.Closed.Obligations`, and `Scoped.Closed.sound` with `Scoped.Closed.meaning_lawful`, at every signature |
| `Calculus/Lang/ScopeHeldFree.lean` | The held-free closed codecs `Scoped.Closed.HF`, `Scoped.Closed.sub` from the laws of the top (`TopLaws`), and `Scoped.Closed.compat_of_HF`, at every signature |
| `Calculus/Lang/ScopeDisjoint.lean` | The structural decision `Scoped.disjoint` over two closed codecs, and `Scoped.disjoint_sound`: two closed codecs that the decision keeps apart share no datum at the orientation, from the laws `Scoped.Laws` of the universe, the leaves, the shape classes and the laws of the top. The view `viewG` at an orientation replaces each `held` by its term at the caller side, and two closed codecs whose views are disjoint accept no common datum (`views_apart`) |
| `Calculus/Lang/ScopeCompat.lean` | The compatibility decision `Scoped.compatPair` over two closed codecs, with no oracle, and `Scoped.compatPair_sound`: an accepted pair agrees at the host and at the dual, at every signature |
| `Calculus/Lang/ScopePath.lean` | A path into a closed codec: the frame `GFrame`, the frontier `Rooted.at`, the strong law `Closed.strong_law` composed from one law per segment (`GFrame.path_law`), and `narrowC`, which keeps each option whose view the graph decision does not separate from the view of the clause, with `narrowC_law` |
| `Calculus/Lang/Universe.lean` | The facts of a universe that read no term: the primitive rows `PrimAdm`, the leaves `Leaf` and `LeafMeet`, the shape classes `Shapes`, the laws of the top `TopLaws`, and the held sets of the rules |
| `Calculus/Lang/CodecPath.lean` | A path into a store: `Seg`, the write at a path `putPath`, and `path_law`, which composes the law of a write from one law per segment, for any frames |
| `Calculus/Dynamo/Alg/Lists.lean` | The list plumbing at the DynamoDB carriers: the aliases of the generic traversal and `filter` facts, and the keyed clause `traverse_fst`, which reads `Name` |
| `Calculus/Dynamo/Domain.lean` | `Member`, `Attr`, the value language, `Kind` with `Attr.kind` (the ten members collapsing onto eight), and `Numeral.WF` — the numeral grammar of the store, 38 significant digits and magnitude range, as a decidable predicate |
| `Calculus/Dynamo/Alg/Codec.lean` | `Codec`, `Lawful` (a canonical partial bijection) and `LawfulCore` as abbreviations of the generic record and laws at `Value`, `Attr` and `Member`, and the aliases of the generic combinators |
| `Calculus/Dynamo/Alg/Prisms.lean` | The entry point of the certified combinator algebra, opening with `Ctor` — a constructor as a partial iso onto its image, the prism of the specification. Each ground codec is `fiberCodec`, the identity on the fiber of its member, and the bases share its one lawfulness proof. Then `through`/`restrict` (iso/prism) and `extendRead` (alternate reading). `Ctor`, `fiberCodec` and the three wrappers are stated generically in `Alg/Combinators.lean`; this file instantiates them at the DynamoDB carriers |
| `Calculus/Dynamo/Alg/Products.lean` | `carriedCodec` — a payload map carried by one prism, the shape underneath every product: `entrywise` is it at a traversal (`array`, `record`), `tupleCodec` it at `align` + a traversal over `slots`, the codec row a shape assigns to a row of *n* positions, which is what makes alignment depend on length alone. `setCodec` is argued on its own. `carriedCodec` and `entrywise` are stated generically in `Alg/Lists.lean`, and `align` and `slots` in `Alg/Positions.lean`; this file instantiates them at the DynamoDB carriers |
| `Calculus/Dynamo/Alg/Objects.lean` | The field table as a map rather than a row, and the object taken apart through it. `objectCodec` is cashed as an equation by `objectCodecCore_eq` rather than argued on its own |
| `Calculus/Dynamo/Alg/Sums.lean` | `altCodec` (the sum, resolved by the first admitter) |
| `Calculus/Dynamo/Alg/Carriers.lean` | One `Carrier` lemma per combinator, so the judgement's held-set index is the domain of the pair |
| `Calculus/Dynamo/Alg/Lawful.lean` | The lawfulness lemmas this development discharges, one per construction |
| `Calculus/Dynamo/Alg/Frontier.lean` | The lawfulness lemmas that are stated and not yet discharged, and the ones whose discharge is partial |
| `Calculus/Dynamo/Lang/Term.lean` | The DynamoDB signature: `Pred`, `SetElem`, the primitives `Ground` with `groundCodec`, the formers `dList`, `dMap` and `dSet`, `dynSyn` and `dynSem`, the stored table `dynTableA`, and the abbreviations `Table` and `Word` at `dynSyn` |
| `Calculus/Dynamo/Alg/Recursion.lean` | Guarded recursion: `muCodec` budgets each input by its own depth (`Value.depth`/`Attr.depth`); from `Contractive` alone the stages agree past the depth (`muStage_agree`), the limit is a fixed point (`muCodec_fix`), and lawful stages give a lawful limit (`lawful_muCodec`); each container keeps agreement one layer down |
| `Calculus/Dynamo/Lang/Scope.lean` | The closed codec of DynamoDB `Closed`: a DAG of scopes over the term container, and a root entry. Its meaning `Closed.meaning` at a caller table is the solution of the scopes at the root, and the read row `Closed.AdmA` is the domain of the read of the meaning |
| `Calculus/Dynamo/Lang/ScopeSound.lean` | The judgement `Closed.Typed` and the obligations `Closed.Obligations` of a closed codec at the DynamoDB tables, the theorem `Closed.sound`, the carrier bridge `Closed.carrier` (a typed closed codec writes and reads only values of its held set), and `Closed.extendRead_lawfulCore` |
| `Calculus/Dynamo/Lang/Equations.lean` | `union` associativity, which needs none of the conditions that the specification states (`equiv_altCodec_assoc`). The other "Hold" nodes of the specification's equations are the combinator rows of `Codec.Equiv` (the specification's `≡`) in `Alg/Relations.lean` (`held`'s identity `equiv_through_id`, `Codec.extendRead` with its own reader as the alternate reader and `≈` on `Can(c)`, `union` of one and its commutativity) and the term rows of `ScopeEquations.lean`. The null-point node went with the wrapper: the point is a union option, so idempotence is the union's |
| `Calculus/Dynamo/Lang/ScopeEquations.lean` | The rows of `≡` that read a term, over the codec of a scope term: `held`'s composition (`Scoped.equiv_held_comp`; its identity is `equiv_through_id` at the codecs, because a `held` of the empty word has no term), `refine`'s meet and full case (`Scoped.equiv_refine_meet`, `Scoped.equiv_refine_full`), and wrapper member preservation (`Scoped.optional_μ`, `Scoped.held_μ`, `Scoped.refine_μ`) |
| `Calculus/Dynamo/Alg/Opaque.lean` | `opaque` as the identity codec `Alg.idCodec`, with `lawful_opaq` and `carrier_opaq`; the union of everything self-identifying (`opaqUnfoldClosed`) is a theorem in `ScopeUniversal.lean` |
| `Calculus/Dynamo/Lang/ScopeHeldSet.lean` | `T` as an identity: `Closed.typed_T_identity` ((A) at every entry of a typed closed codec, from `TOp.rule_T` at every operation) |
| `Calculus/Dynamo/Alg/Continuity.lean` | `Sub` as the information order that any ccpo must extend, and first-match resolution monotone (`selectF_mono_list`) and continuous (`selectF_continuous_list`) under the obligation that every admitter agrees |
| `Calculus/Dynamo/Witness/Nesting.lean` | **The one place `𝔸` is bigger in the model than in the store.** `Attr.Storable` (`Domain.lean`) is the nesting bound of the store, a parameter, counting `L` and `M` only — a different function from `Attr.depth`, which is a termination measure and charges a wire set a layer. The ground fragment writes nesting `0`, containers add exactly one, and `Closed.not_storable_of_typed` (`ScopeNesting.lean`) exhibits a **typed** closed codec whose encoding the store refuses: the bound is absent from the rules of the judgement rather than a premise someone failed to discharge |
| `Calculus/Dynamo/Lang/Store.lean` | The DynamoDB port: `DynamoDB.maxNesting` instantiates the nesting bound at the store's 32 levels; `decimalCodec` over `Numeral.Stored` and its `SurvivesStore` instance, `not_survivesStore_numberCodec`, the numeral-domain report (`decimal_writes_stored`/`decimal_reads_stored` with worked boundary cases) |
| `Calculus/Dynamo/Lang/Adapters.lean` | `Numeral.Normal`/`Numeral.Stored`, the text adapter `numeralOfStoredText`/`textOfNumeral`, and the table of the library `libTable` |
| `Calculus/Dynamo/Lang/Universe.lean` | DynamoDB as a universe: `dynPrimAdm`, `ground_selfdual`, `dynLeaf`, `dynLeafMeet`, `dynShapes` and `Ω_topLaws`, with the lemmas on literals and sets that they read |
| `Calculus/Dynamo/Lang/Clause.lean` | The data of a clause: `Pin`, `NameSpec`, `AltClause` with `altsSub` and `litSubAt`, and the conditions of a precondition `Cond` with `readPath` |
| `Calculus/Dynamo/Witness/Refutations.lean` | The six "Do not hold" nodes of the specification's equations, all settled: `Closed.not_equiv_union_array`, `Closed.not_equiv_tupleTail_tuple` and `Closed.not_equiv_tupleTail_array`, `Closed.not_equiv_refine_held` and `Closed.not_equiv_union_extend` in `ScopeRefutations.lean`, `legacy_breaks_MP` for an alternate reader, `e_comp_p_ne_id`, plus `optional` nesting, which the syntax rules out, and `set(union(…))`, which the DynamoDB set obligation refuses (`Scoped.setElem_union_refused`) |
| `Calculus/Axioms.lean` | `#assert_axioms`, and the headline theorems run through it — the advertised axiom base (`propext`, `Classical.choice`, `Quot.sound`; **no `sorryAx`**) as a build error rather than a claim in prose |
| `Calculus/Dynamo/Witness/ScopeDischarge.lean` | The host's recursive schema for JSON as a closed codec (`jsonClosed`), lawful through `Closed.sound` (`Closed.lawful_json`), and each shape that the guard refuses as a graph with no form as a DAG of scopes |
| `Calculus/Dynamo/Analysis/ScopePath.lean` | The frontier of a path into a closed codec and narrowing at DynamoDB, as vectors that reduce in the kernel: the store refuses a segment, and an entry that a cycle returns to is one entry. `Closed.narrowC_law` is the narrowing law at DynamoDB |
| `Calculus/Dynamo/Analysis/ScopePrecondition.lean` | The precondition of a closed clause as data for the store: a conjunction of `in`, `type` and `exists` tests at paths into the item. `Closed.preconditionOfC` reads the stored view of the clause and states the precondition exactly or refuses (`Closed.preconditionOfC_exact`), and `Closed.narrow_law_precondition` is the narrowing law with the precondition in place of the admission |
| `Calculus/JSON/Basic.lean` | A second universe on the generic layer, with no DynamoDB import: the carrier `Json`, the ground codecs, the array prism, the signature `jsonSyn`/`jsonSem` with `id_topLaws`, and the kind test as the primitive admission row `jsonPrimAdm` |
| `Calculus/JSON/ScopeBasic.lean` | The union of the string codec and the number codec as a closed codec (`strOrNumClosed`), lawful by `Scoped.Closed.meaning_lawful` (`lawful_strOrNumC`), and exact against the kind rows at every orientation (`exact_strOrNumC`) |
| `Calculus/JSON/Disjoint.lean` | The leaves `jsonLeaf` (two kinds are apart where they are two kinds), `jsonLeafMeet`, and the shape classes `jsonShapes` |
| `Calculus/JSON/ScopeDisjoint.lean` | Disjointness of closed codecs at JSON: the laws `jsonLaws` that the decision reads, and `Scoped.disjoint_sound` at `jsonSyn` (`closed_orthogonal`) |

`Alg/Agree.lean`, `Alg/Converse.lean`, `Alg/Rows.lean`, `JSON/Compat.lean`, `JSON/ScopeCompat.lean`,
`Malleability.lean`, `Separation.lean`, `ScopeSlice.lean`, `Bridge/Vectors.lean`, `Bridge/Verdicts.lean`, `Bridge/Kinds.lean`,
`Bridge/Rows.lean` and `Bridge/ScopePaths.lean` have none, and each opens with a module docstring that says
what it is for.
Read those.

**The mechanization is complete: the project builds with zero `sorry`.** The
soundness theorem of the judgement is machine-checked — `Scoped.Closed.sound` (retract, canon and writes) — by `sound_term` at each
scope, which dispatches each operation to its certified combinator lemma. `opaque` is the identity codec, so it owes no
compatibility.
The judgement carries both of its indices, and both are checked against the
denotation. `Closed.carrier` states the specification's `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T`: a typed
closed codec writes and reads only values of its held set. The held set is an **identity** with
the judgement's own index in both directions, `Closed.typed_T_identity`, so the index describes
the denotation exactly rather than bounding it. The
member index is fuel-free (`μG`, read from the operation of a node, with `μG_sound` tying the
meaning to it).

## Modelling decisions

- **mathlib, for the plumbing only.** The *definitions* still don't need it: wire sets and
  maps are lists (a quotient cannot sit recursively inside an inductive), and set-ness lives
  where the doc puts it — in `ker p`. What mathlib retired is the hand-rolled list and
  option machinery, which had grown to roughly a third of the combinator algebra. The residue —
  facts mathlib genuinely lacks, or states in a shape the use sites cannot consume — is
  `Calculus/Dynamo/Alg/Lists.lean`, and citing a name from there is the signal that a step is plumbing
  rather than content.
- **The axiom base is checked, not asserted.** mathlib proves a great deal classically, so
  a single `by_contra`, or an appeal to a lemma like `List.filter_eq_nil_iff`, silently
  widens the base of everything downstream. `Calculus/Axioms.lean` collects the axioms each
  headline theorem actually depends on and fails the build on anything unsanctioned. Both
  of those leaks happened while the module was being written, which is why it exists — and it
  has caught two more since, one of them entering through a `def` rather than a proof
  (mathlib's `DecidableEq (Finset α)` is classical in this toolchain), where no amount of
  reviewing tactics would have found it.

  **The guard only sees what is loaded**, and `Axioms.lean` imports a hand-maintained list, so
  a module nothing on that list reaches is silently unguarded. That is the same opt-in failure
  this file's own docstring argues against, one level up. `python3 scripts/guard_reach.py`
  closes it: it builds the import graph under `Calculus/` and fails if any module is outside
  the transitive closure of the guard's imports. It checks *reachability*, not that the guard
  is configured correctly. `Axioms.lean` cannot simply `import Calculus` instead — the
  aggregator imports the guard, so that is a cycle, and inverting it would let
  `defaultTargets = ["Calculus"]` build the tree with no guard running at all.
- **There is no fuel.** The meaning of a closed codec is the solution of its scopes
  (`DSys.sol`), and the solution reads each input at the stage that the depth of the input
  names, so no fuel appears in a statement. Neither of the two things that forced fuel still
  does: the model has no thunk, and the solution budgets each input by the input's own depth.
- **Recursion is guarded, and constructed.** A closed codec is a DAG of scopes, and each entry
  of a scope is a body that reads the entries. The guard `Flat.Guarded` puts each entry under a
  `down` and no entry under a `wall`, and a guarded system is contractive
  (`contractive_of_guarded`); `dagGuardB_iff_dsys` decides the form as a DAG of scopes. From
  the guard alone the solution is a fixed point (`solve_fix`), and lawful stages give a lawful
  solution (`lawful_solve`, `System.lean`). `Continuity.lean` proves that first-match
  resolution is monotone (`selectF_mono_list`, the `mono` obligation of a ccpo construction)
  and continuous (`selectF_continuous_list`) under
  the obligation that every admitter agrees, and `optBad_not_confluent` shows the obligation is
  not free. The construction does not need that obligation, because it budgets each input.
- **One construction, one place — and one proof per law.** Each construction's
  definition, its two inversion lemmas, its carrier and its lawfulness sit together.
  Soundness needs only `Lawful`, so a core lemma exists only where a `Lawful` lemma or
  the alternate reader cites it, and the two share their clauses (`tuple_retract`,
  `set_writes`). The shape underneath is `carriedCodec`, a payload map carried by one
  summand; `entrywise` (hence `array`, `record`), `tuple` and
  `object` are all instances, so the two prism halves of a codec are discharged once for all of them.
  `set` is the one product that is not, and the reason is stated where it is argued:
  its attribute side is a choice among three wire sets, not one constructor.
- **A recursive union's compatibility is decided by orthogonality, not argued per option.**
  A string and an array share no value and no attribute whatever the element, and orthogonal
  lawful codecs are compatible (`compat_string_array`). So the two options of `jsonClosed` meet
  their obligation at every lawful element (`obligations_jsonBody`), and the compatibility needs
  nothing from the recursive call.
- **`N` is carried exactly, and no numeric type is axiomatized.** A target language that hands
  its own numeric type to a caller adapts that type to `WFNumeral` in the port. IEEE-754 facts
  are not this calculus's theorems, and nothing here assumes them.
- **Semantic rule premises live beside the carrier**, not in `Typed`: the doc's
  `(held)` side condition lives in `Obligations`. The alternate-reader
  condition is `ReadsCoherently`, which `extendRead_p_union` proves equivalent to order-freedom. Each definition has
  its denotation in scope.
  `Obligations` is **structural, not fuel-indexed**. The null point is not in the list either: the point is a union option,
  so what was the wrapper's honesty premise is now the sum's compatibility.

## Is the model the specification?

Two independent readings, in opposite directions, asked whether every normative element of
the specification has an exact counterpart here and whether a reviewer could check one
in isolation. That reading is finished and its record is in the commits, which is where an
audit's findings belong: an audit is not load bearing.

**One of its findings is still open, and it lives in `docs/defects.md`**: the wrapper rule
demands a total iso where the proof consumes only the domain-restricted one. Two others closed
in the tree rather than on paper. The set carrier's nonemptiness and uniqueness are properties
of its own type, so the omission the reading found is not there to state. And the commutativity
node holds at any permutation of compatible, canonical options, by `altCodec_perm`, which is a stronger claim
than the node asked for: reordering the options yields the same codec rather than an equivalent
one.

## Do the documents still name what exists?

Prose does not typecheck. Deleting a declaration leaves the build green and every citation
of it dangling.
`python3 scripts/name_drift.py` closes that: it reports every backticked Lean name in the
current-state documents — this file, `docs/architecture.md`, `docs/roadmap.md`,
`docs/defects.md`, the blueprint's `content.tex` — and
every module docstring, that no longer occurs in `Calculus/`,
and exits
non-zero if there is one. Deliberate citations live in an `EXPECTED` table with a reason
each, and the check fails if an entry there stops being cited, so the table cannot rot
quietly either.

This is `Axioms.lean`'s principle at the documents: a claim that fails the build rather than
a claim in prose.

## How the proofs are meant to read

The convention is `docs/architecture.md`'s: a definition is unfolded once, in its own
inversion lemma, and every proof downstream cites the lemma. That document carries the naming
scheme, which is normative, and what a docstring is for.

The short version: the *obligation* half of the vocabulary is done (20/22 carriers,
20/22 lawfulness lemmas); the *observation* half — `X_e`/`X_p`, what a construction
writes and reads — is 28 of 44. Seven of every ten remaining hand-unfoldings are `Option`
algebra rather than anything about codecs. Across blocks the spread is narrower than a first
reading of the table suggests, and `ground` sits mid-table with no inversion at all — because
`fiberCodec` gives the ground codecs one shared proof, which argues *for* the
convention rather than against it: shared construction, fewer sites.

## What remains (sharpenings, not gaps)

The theorem is proved; these tighten the model's fidelity to the doc, none affect
soundness. `union`'s commutativity is proved for the adjacent transposition, which
generates every permutation, and lifting it to `List.Perm` is the obvious next step.
A numeric literal's read side names its set: `N` is carried exactly, so the `.number` row of `inL`
reads by equality, as the `.string` row does. Each primitive is self-dual, so `inL` is
the row at both orientations, and it is `dom(p)` exactly, which is what separates two disjoint
numeric literals from each other.
The store observation lives in the DynamoDB port. `10²¹` is written `1e+21` and handed back
normalised, and `not_survivesStore_numberCodec` shows that `number` does not survive the
normalisation. `Lawful.retract_through_store` is (R) asked through any transformation the store
may apply, and `survivesStore_decimalCodec` discharges its premise for `decimal`.

## Building

Open the repository in the devcontainer and run this from `formal/`:

```sh
lake build
```

First build downloads the pinned toolchain (`lean-toolchain`) and, on a cold cache, builds
mathlib. The build is `sorry`-free. An error is a regression, and so is an `#assert_axioms` failure in
`Calculus/Axioms.lean`.
