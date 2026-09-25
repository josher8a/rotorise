# Codec calculus — Lean 4 mechanization

Mechanizes the specification in `docs/blueprint/src/content.tex`. The doc stays normative; this package is the proof
assistant checking it, and every deliberate divergence from the doc is commented at the
definition it touches.

## Layout

| Module                      | Doc section | Content                                                                                                                                                                                                                                                               |
| --------------------------- | ----------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Calculus/Lists.lean`       | —           | The list plumbing: `traverse` and its laws off the pivot `traverse_eq_some` (a successful traversal *is* `List.Forall₂ (f · = some ·)`), the keyed clause `traverse_fst`, and the `filter` facts mathlib states in the wrong shape — everything with no codec in it, kept apart so `Prisms.lean` reads as codec vocabulary |
| `Calculus/Domain.lean`      | §1          | `Member`, `Attr`, the value language, `Kind` with `Value.kind`/`Attr.kind` (the ten members collapsing onto eight), and `Numeral.WF` — §1's numeral grammar, 38 significant digits and magnitude range, as a decidable predicate                                                                                            |
| `Calculus/Codec.lean`       | §2, §5      | `Codec`, `Lawful` (a canonical partial bijection)/`LawfulCore`, corollaries (Q, read-side W), injectivity lemma — **proved**                                                                                                                                                           |
| `Calculus/Prisms.lean`      | §3          | The entry point of the certified combinator algebra, opening with `Ctor` — a constructor as a partial iso onto its image, the prism §7 names. The point ground codecs (`string`, `boolean`, `binary`, `null`) are `pointCodec` at four pairs of prisms and share one lawfulness proof; the wire-set payload projections are the same shape again. Then `through`/`restrict` (iso/prism) and `extendRead` (alternate reading) |
| `Calculus/Products.lean`    | §3          | `carriedCodec` — a payload pair carried between two prisms, the shape underneath every product: `entrywise` is it at a traversal (`array`, `record`), `tupleCodec` it at `align` + a traversal over `slots`, the codec row a shape assigns to a row of *n* positions, which is what makes alignment depend on length alone. `setCodec` is argued on its own |
| `Calculus/Objects.lean`     | §4          | The field table as a map rather than a row, and the object taken apart through it. `objectCodec` is cashed as an equation by `objectCodecCore_eq` rather than argued on its own |
| `Calculus/Sums.lean`        | §5, §3      | `altCodec` (the sum, resolved by the first admitter), and `opaqStep`, one layer of everything self-identifying |
| `Calculus/Carriers.lean`    | §3          | One `Carrier` lemma per combinator, so the judgement's held-set index is the domain of the pair |
| `Calculus/Lawful.lean`      | §3–§5       | The lawfulness lemmas this development discharges, one per construction |
| `Calculus/Frontier.lean`    | §3–§5       | The lawfulness lemmas that are stated and not yet discharged, and the ones whose discharge is partial |
| `Calculus/Term.lean`        | §3–§4       | Current-schema terms, object slots, and object rest policies                                                                                                                                                                                                                                        |
| `Calculus/Recursion.lean`   | §3          | Guarded recursion: `muCodec` budgets each input by its own depth (`Value.depth`/`Attr.depth`); from `Contractive` alone the stages agree past the depth (`muStage_agree`), the limit is a fixed point (`muCodec_e_fix`/`muCodec_p_fix`), and lawful stages give a lawful limit (`lawful_muCodec`); each container keeps agreement one layer down |
| `Calculus/Guarded.lean`     | §3          | The guard of a binder makes its body contractive: `denote_agree`, one congruence over the term family, and `contractive_body` |
| `Calculus/Denote.lean`      | —           | `denote`, structural, pure dispatch into the combinators, over an environment for the bound variables; `mu` is `muCodec` of its body                                                                                                                                                                                                     |
| `Calculus/Typing.lean`      | §3–§5       | The judgement `⊢ c : T ⇝ μ`, both indices, with the held-set formers (`HSet`, `HStar`, `HProd`, `HMap`, `HObject`, `HUnion`, `HOpaque`); syntactic premises only                                                                                             |
| `Calculus/Soundness.lean`   | §5          | `Obligations` (semantic premises, structural), `PairwiseCompat`, theorem statements, and the held-set bridge `carrier_denote`/`typed_TSub`/`typed_e_mem`/`typed_p_mem`                                                    |
| `Calculus/Equations.lean`   | §6          | `Codec.Equiv` (§6's `≡`), `Can`, and all ten of §6's "Hold" nodes this development still states — `held`'s identity and composition, `refine`'s meet and full case, `Codec.extendRead` with its own reader as the alternate reader and `≈` on `Can(c)`, `union` of one, its commutativity and its associativity (which needs none of §6's stated conditions), wrapper member preservation. §6's null-point node went with the wrapper: the point is a union option, so idempotence is the union's |
| `Calculus/Opaque.lean`      | §3, §7      | `opaque` as `muCodec opaqStep`: the kind-disjoint unfoldings — one per constructor each side, counted in that file's own header — `contractive_opaqStep`, `lawful_opaq`/`carrier_opaq` from the general theorems, and the fixed point at each container (`Ωe_fix`, `Ωe_arr` and the rest) |
| `Calculus/HeldSet.lean`     | §1, §3, §6  | `T` as an identity: `opaq_T_identity` (`HOpaque` *is* `opaque`'s held set) and `typed_T_identity` ((A) at every rule); `typed_T_adm` in `Laminar.lean` proves (B) at every derivable term |
| `Calculus/Continuity.lean`  | §5, §7      | `Codec.Approx` (the information order any ccpo must extend), and first-match resolution monotone (`selectF_mono_list`) and continuous (`selectF_continuous_list`) under the obligation that every admitter agrees |
| `Calculus/Nesting.lean`     | §1          | **The one place `𝔸` is bigger in the model than in the store.** `Attr.Storable` (`Domain.lean`) is §1's nesting bound, a parameter, counting `L` and `M` only — a different function from `Attr.depth`, which is a termination measure and charges a wire set a layer. The ground fragment writes nesting `0`, containers add exactly one, and `not_storable_of_typed` exhibits a **derivable** term whose encoding the store refuses: the bound is absent from §3's rules rather than a premise someone failed to discharge |
| `Calculus/DynamoDB.lean`    | §1          | The DynamoDB port: `DynamoDB.maxNesting` instantiates the nesting bound at the store's 32 levels; `Numeral.Normal`/`Numeral.Stored`, `decimalCodec` and its `SurvivesStore` instance, `not_survivesStore_numberCodec`, the numeral-domain report (`decimal_writes_stored`/`decimal_reads_stored` with worked boundary cases), and the text adapter `numeralOfStoredText`/`textOfNumeral` |
| `Calculus/Refutations.lean` | §6          | §6's six "Do not hold" nodes, all settled, over seven declarations: `not_equiv_union_array`, `not_equiv_tupleTail_tuple` and `not_equiv_tupleTail_array`, `not_equiv_refine_held`, `not_equiv_union_extend`, `legacy_breaks_MP` for an alternate reader, `e_comp_p_ne_id` — plus `optional` nesting and `set(union(…))`, both of which the syntax rules out |
| `Calculus/Axioms.lean`      | §3          | `#assert_axioms`, and the headline theorems run through it — the advertised axiom base (`propext`, `Classical.choice`, `Quot.sound`; **no `sorryAx`**) as a build error rather than a claim in prose |
| `Calculus/Discharge.lean`   | §5          | `refine`'s read-side gate, which `AdmA` reads, and a premise checked at two options |

This table has a row of its own for twenty-two of the modules under `Calculus/`.
`ExactV.lean`, `ExactA.lean`, `Separation.lean`, `Orthogonality.lean`,
`Malleability.lean`, `LiteralArity1.lean` and `Vectors.lean` have none, and each opens with a module docstring that says what it is for.
Read those.

**The mechanization is complete: the project builds with zero `sorry`.** §5's
soundness theorem is machine-checked — `soundness` (retract, canon and writes) — by induction on the judgement, dispatching
each case to its certified combinator lemma, with `opaque`'s compatibility discharged by
`compat_opaque`.
The judgement carries both of §3's indices, and both are checked against the
denotation. `typed_e_mem` and `typed_p_mem` are §3's `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T` at the
judgement's own index — a derivable term writes and reads only values of the held set it
names — factored through `Carrier` (per combinator) and `typed_TSub` (the denotation's
held set is inside the judgement's) — and the containment is an **identity** in both
directions, `typed_T_identity`, so the index describes the denotation exactly rather than
bounding it. The
member index is fuel-free (`μSyn`, with `denote_μ` and `typed_μSyn` tying the denotation
and the judgement to it).

## Modelling decisions

- **mathlib, for the plumbing only.** The *definitions* still don't need it: wire sets and
  maps are lists (a quotient cannot sit recursively inside an inductive), and set-ness lives
  where the doc puts it — in `ker p`. What mathlib retired is the hand-rolled list and
  option machinery, which had grown to roughly a third of the combinator algebra. The residue —
  facts mathlib genuinely lacks, or states in a shape the use sites cannot consume — is
  `Calculus/Lists.lean`, and citing a name from there is the signal that a step is plumbing
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
- **There is no fuel.** `denote` is structural on the term. What the proofs recurse on
  instead is `Term.depth`, a measure derived from the term, so it appears in no statement.
  Neither of the two things that forced fuel still does: the model has no thunk, and `opaq`
  and `mu` denote `muCodec`, which budgets each input by the input's own depth.
- **Recursion is guarded, and constructed.** `mu b` denotes `muCodec` of its body, and each
  input reads the stage of the body that its own depth names. `Term.guarded` refuses a variable
  that reads its binder's input itself, and a variable under a `held`. From the guard alone the
  stages agree past the depth of the input, the limit is a fixed point, and lawful stages give a
  lawful limit (`Recursion.lean`, `Guarded.lean`). `Continuity.lean` proves that first-match
  resolution is monotone (`selectF_mono_list`, the `mono` obligation of a ccpo construction)
  and continuous (`selectF_continuous_list`) under
  the obligation that every admitter agrees, and `optBad_not_confluent` shows the obligation is
  not free. The construction does not need that obligation, because it budgets each input.
- **One construction, one place — and one proof per law.** Each construction's
  definition, its two inversion lemmas, its carrier and its lawfulness sit together.
  Soundness needs only `Lawful`, so a core lemma exists only where a `Lawful` lemma or
  the alternate reader cites it, and the two share their clauses (`tuple_retract`,
  `object_retract`, `set_retract`/`set_writes`). The shape underneath is `carriedCodec`, a payload pair
  between two prisms; `pointCodec`, `entrywise` (hence `array`, `record`), `tuple` and
  `object` are all instances, so §2's prism halves are discharged once for all of them.
  `set` is the one product that is not, and the reason is stated where it is argued:
  its attribute side is a choice among three wire sets, not one constructor.
- **`opaque`'s compatibility is computed from kinds, not argued per option.** `Kind` is §1
  vocabulary now (`Domain.lean`), on both sides of the pair — `Value.kind` and
  `Attr.kind`, the ten members collapsing onto eight. An option is *pinned to a kind*
  when it admits only values and attributes of that kind (`Codec.OnKind`), and
  `compat_opaque` turns pinned options with distinct kinds into compatibility. Each of
  `opaque`'s eight is pinned in one line, and `onKind_set`/`onKind_array`/`onKind_record`
  hold for *any* element codec — which is why the fixpoint's compatibility needs
  nothing from the recursive call, and why `opaque` is not a special construction.
- **`N` is carried exactly, and no numeric type is axiomatized.** A target language that hands
  its own numeric type to a caller adapts that type to `WFNumeral` in the port. IEEE-754 facts
  are not this calculus's theorems, and nothing here assumes them.
- **Semantic rule premises live beside the carrier**, not in `Typed`: the doc's
  `(held)` side condition lives in `Obligations`. The alternate-reader
  condition is `ReadsCoherently`, which `extendRead_lawfulCore` consumes. Each definition has
  its denotation in scope.
  `Obligations` is **structural, not fuel-indexed** —
  this bullet said `Obligations fuel t` and "same premises, fueled form" long after `denote`
  became structural. §3's null point is not in the list either: the point is a union option,
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
`pointCodec` gives four of the ground codecs one shared proof, which argues *for* the
convention rather than against it: shared construction, fewer sites.

## What remains (sharpenings, not gaps)

The theorem is proved; these tighten the model's fidelity to the doc, none affect
soundness. `union`'s commutativity is proved for the adjacent transposition, which
generates every permutation, and lifting it to `List.Perm` is the obvious next step.
A numeric literal's read side names its set: `N` is carried exactly, so `AdmALit`'s `.number`
row reads by equality, as the `.string` row does. `AdmA`'s `number` row and `AdmALit`'s `.number`
row are `dom(p)` exactly, which is what separates two disjoint numeric literals from each other.
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
mathlib. The build is `sorry`-free and **warning-free**; any warning or error is a
regression, and so is an `#assert_axioms` failure in `Calculus/Axioms.lean`.
