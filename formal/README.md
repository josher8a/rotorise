# Codec calculus — Lean 4 mechanization

Mechanizes `docs/codec-calculus.md`. The doc stays normative; this package is the proof
assistant checking it, and every deliberate divergence from the doc is commented at the
definition it touches.

## Layout

| Module                      | Doc section | Content                                                                                                                                                                                                                                                               |
| --------------------------- | ----------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Calculus/Lists.lean`       | —           | The list plumbing: `traverse` and its laws off the pivot `traverse_eq_some` (a successful traversal *is* `List.Forall₂ (f · = some ·)`), `List.lookup` on association lists, and the `filter`/`zip` facts mathlib states in the wrong shape — everything with no codec in it, kept apart so `Combinators.lean` reads as codec vocabulary |
| `Calculus/Domain.lean`      | §1          | `Member`, `Attr`, `Item`, the value language, `Double` axioms, and `Numeral.WF` — §1's numeral grammar, 38 significant digits and magnitude range, as a decidable predicate                                                                                            |
| `Calculus/Codec.lean`       | §2, §5      | `Codec`, `Agree` (`≼`), `Lawful`/`LawfulCore`, corollaries (Q, read-side W), injectivity lemma — **proved**                                                                                                                                                           |
| `Calculus/Combinators.lean` | §3–§5       | The certified combinator algebra, opening with `Ctor` — a constructor as a partial iso onto its image, the prism §7 names. The point ground codecs (`string`, `boolean`, `binary`, `null`) are `pointCodec` at four pairs of prisms and share one lawfulness proof; the wire-set payload projections are the same shape again. Then `through`/`restrict` (iso/prism), `extendRead` (legacy), `orNull` (nullable), `carriedCodec` — a payload pair carried between two prisms, the shape underneath every product: `entrywise` is it at a traversal (`array`, `record`, left with only the shape of `≼` at their attribute constructor), `tupleCodec` it at `align` + a traversal, over `slots` — the codec row a shape assigns to a row of *n* positions, which is what makes alignment depend on length alone; the remaining products, `altCodec`+`UniqueAdmission` and `dunionCodec` (sums), `opaqCodec` — with one lawfulness lemma each |
| `Calculus/Term.lean`        | §3–§4       | Deep-embedded terms, fields, rest policies                                                                                                                                                                                                                            |
| `Calculus/Denote.lean`      | —           | `denote : Nat → Term → Codec`, pure dispatch into the combinators                                                                                                                                                                                                     |
| `Calculus/Typing.lean`      | §3–§5       | The judgement `⊢ c : T ⇝ μ`, both indices, with the held-set formers (`HSet`, `HStar`, `HProd`, `HMap`, `HNull`, `HObject`, `HUnion`, `HOpaque`); syntactic premises only                                                                                             |
| `Calculus/Soundness.lean`   | §5          | `Obligations` (semantic premises, fueled), `UAtCan := UniqueAdmission ∘ semsOf`, `MPOk` (legacy exemption), theorem statements, and the held-set bridge `carrier_denote`/`typed_TSub`/`typed_e_mem`/`typed_p_mem`                                                    |
| `Calculus/Equations.lean`   | §6          | `Codec.Equiv` (§6's `≡`), `Can`, and all eleven of §6's "Hold" rows — `held`'s identity and composition, `refine`'s meet and full case, `legacy` with its own reading and `≈` on `Can(c)`, `union` of one, its commutativity and its associativity (which needs none of §6's stated conditions), `nullable`'s idempotence, wrapper member preservation |
| `Calculus/Opaque.lean`      | §3, §7      | `opaque` without fuel: `Value.depth`/`Attr.depth`, the ten kind-disjoint unfoldings, `opaq_e_agree`/`opaq_p_agree` (stabilization), `opaq_e_depth`/`opaq_p_depth` (depth preservation), and `opaqCodecω` with `lawful_opaqCodecω`/`carrier_opaqCodecω` |
| `Calculus/Denoteω.lean`     | —           | `denoteω : Term → Codec` — structural, no fuel — with `termDepth` and `denoteω_eq : termDepth t ≤ n → denoteω t = denote n t` |
| `Calculus/Soundnessω.lean`  | §5          | §5 restated fuel-free: `soundnessω`, `soundness_coreω`, `carrier_denoteω`, `typed_e_memω`, `typed_p_memω`, `typed_μSynω` — transports, not reproofs |
| `Calculus/HeldSet.lean`     | §1, §3, §6  | `T` as an identity: `opaq_T_identity` (`Uν` *is* `opaque`'s held set), `set_nil_outside_opaque` (the witness for the non-emptiness premise `HOpaque` was missing), and the numeral-domain report — `decimal_writes_wf`/`decimal_reads_wf` with worked boundary cases |
| `Calculus/Continuity.lean`  | §5, §7      | Why fuel is not removable by a fixpoint: `Codec.Approx` (the information order any ccpo must extend), `altCodec_not_monotone` (unique admission is anti-monotone in the options) and `denote_not_fuel_monotone` (the fuel stages are not a chain) |
| `Calculus/Refutations.lean` | §6          | §6's "Do not hold" table, all nine settled: `not_equiv_lazy` (the row where `≡`'s member index matters), `not_equiv_union_array`, `not_equiv_union_extend`, the two `tuple`-tail rows, `not_equiv_refine_held`, `legacy_breaks_MP`, `e_comp_p_ne_id`, `not_typed_set_union` — plus `optional` nesting, which the syntax rules out |
| `Calculus/Axioms.lean`      | §3          | `#assert_axioms`, and the headline theorems run through it — the advertised axiom base (`propext`, `Quot.sound`, the `Double` axioms; **no `Classical.choice`**) as a build error rather than a claim in prose |
| `Calculus/Discharge.lean`   | §5          | The machinery of (K): `Kind`, `κ`, `ident`, `adm`/`admA` as structural recursions, `κ_sound`/`adm_sound`/`admA_sound`, and `uAtCan_of_separated` — the dischargers of (U), proved, with witnesses and the two counterexamples that repaired (K)                       |

**The mechanization is complete: the project builds with zero `sorry`.** Both halves
of §5's soundness theorem are machine-checked — `soundness` (all four laws, (MP) with
the legacy exemption as the `MPOk` hypothesis) and `soundness_core` ((R), (C), (W)
through `legacy`-containing derivations) — by induction on the judgement, dispatching
each case to its certified combinator lemma, with the `(dunion)` stamps derived from
typing and (U) discharged by `uniqueAdmission_byTag`, and `opaque`'s inside `lawful_opaqCodec`.
The judgement carries both of §3's indices, and both are checked against the
denotation. `typed_e_mem` and `typed_p_mem` are §3's `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T` at the
judgement's own index — a derivable term writes and reads only values of the held set it
names — factored through `Carrier` (per combinator) and `typed_TSub` (the denotation's
held set is inside the judgement's). The
member index is fuel-free (`μSyn`, with `denote_μ` and `typed_μSyn` tying the denotation
and the judgement to it), and `lazy` concludes `⊤` in the model exactly as the doc's
`(lazy)` rule demands.

## Modelling decisions

- **mathlib, for the plumbing only.** The *definitions* still don't need it: wire sets and
  maps are lists (a quotient cannot sit recursively inside an inductive), and set-ness lives
  where the doc puts it — in `ker p`. What mathlib retired is the hand-rolled list and
  option machinery, which had grown to roughly a third of `Combinators.lean`. The residue —
  facts mathlib genuinely lacks, or states in a shape the use sites cannot consume — is
  `Calculus/Lists.lean`, and citing a name from there is the signal that a step is plumbing
  rather than content.
- **The axiom base is checked, not asserted.** mathlib proves a great deal classically, so
  a single `by_contra`, or an appeal to a lemma like `List.filter_eq_nil_iff`, silently
  widens the base of everything downstream. `Calculus/Axioms.lean` collects the axioms each
  headline theorem actually depends on and fails the build on anything unsanctioned. Both
  of those leaks happened while the module was being written, which is why it exists.
- **Fuel-primary denotation, now with a fuel-free twin.** `denote` still takes fuel and
  every proof about it is unchanged; `denoteω` (Denoteω.lean) is structural and takes
  none. `denoteω_eq` makes them *equal* at `termDepth t`, so the §5 statements transport
  to the fuel-free form (Soundnessω.lean) without reproving anything. Fuel 0 still
  denotes `Codec.empty` (laws vacuous). Both blockers that forced fuel are gone: `lazy`
  carries a `Term`, and `opaq` denotes `opaqCodecω`.
- **Fuel is not removable by a fixpoint, and that is a fact about (U), not about Lean.**
  `Continuity.lean` proves it: `altCodec` resolves a union by *unique* admission, and
  `OptionSem.byAttempt` derives admission from `(c.e v).isSome`, so growing the recursive
  result grows admission, grows the filtered list from `[o]` to `[o, o']`, and collapses
  the union's answer from `some` to `none`. Unique admission quantifies over the *other*
  options — a negative condition, anti-monotone in exactly the argument a fixpoint must
  grow. `altCodec_not_monotone` is the `mono` obligation any ccpo construction
  (Isabelle's `partial_function`, HOLCF, a hand-rolled `⨆`) would have to discharge and
  cannot; `denote_not_fuel_monotone` shows the fuel stages themselves are not a chain,
  on `union(literal("A"), lazy(string))` — §5's own counterexample pair, staggered.
  Note the direction: the low-fuel answer is *over*-defined, not under-defined.
  What fuel actually stands in for is the finiteness of `Term` — `lazy` carries
  `Unit → Term`, which defeats the termination checker without adding a single
  constructible term. The repair is therefore in the model, not in the tool: see the
  three steps in `docs/codec-formalization.md` §7.
- **`Double` is axiomatized** with exactly the shortest-text round trip §3's `(number)`
  consumes. IEEE-754 facts are not this calculus's theorems.
- **Semantic rule premises live in `Obligations fuel t`**, not in `Typed`: the doc's
  `(legacy)`/`(nullable)`/`(fallback)`/`(custom)` side conditions mention `e`/`p`, which
  are fuel-indexed here, so the premises are too. Same premises, fueled form.
- **(U) is a premise, not a conclusion** (`UAtCan`), matching the doc's theorem residue.
  Its disjointness dischargers are proved (`Calculus/Discharge.lean`): pairwise-disjoint
  `κ` settles the value side, pairwise-distinct named members the attribute side.
  `uAtCan_string_boolean` witnesses that the six premises are jointly satisfiable.
- **§5's (D) is not a discharger of (U), and the doc is fixed.** (D) is a condition on
  held sets — sets of *values* — while (U)'s readable side quantifies over *attributes*,
  and `held`'s adapter relabels between them. `not_uAtCan_literal_held` exhibits
  `union(literal("A"), held(literal("A"), f, g))`: held sets `{"A"}` and `{"B"}`,
  disjoint on the nose, both options reading `S "A"`. §5 used to say that stating (D) as
  disjointness "would be sound"; it now says (D) is well-formedness on the `T` index, and
  the readable side is decided on stored attributes (distinct `μ`, or disjoint `adm`).
- **§5's `ident` half of (K) was unsound as stated; the mechanization found it and the
  doc is fixed.** §5 used to write (K) as `κ(cᵢ) ∩ κ(cⱼ) = ∅ ∨ ident(cᵢ) ∨ ident(cⱼ)`
  and call it sufficient for (U). Neither disjunct carries it, and both counterexamples
  are proved in `Discharge.lean`: `not_uAtCan_literal_string` (one-sided `ident` —
  `union(literal("A"), string)` passed (K), and both options admit `"A"`) and
  `not_uAtCan_array_literals` (two-sided `ident` — `ident` propagates through `array`,
  but disjointness of the admissible sets does not, and both options admit `[]`). §5 now
  states (K) with `adm`, the set an `ident` term checks against, disjoint on both sides;
  `adm`/`admA` and the combined `uAtCan_of_separated` mechanize it, with
  `uAtCan_of_disjoint` its kind/member half and `uAtCan_literal_literal` discharging
  §5's own worked example — a pair that shares both `κ` and `⇝`, so only `adm` reaches
  it.

## What remains (sharpenings, not gaps)

The theorem is proved; these tighten the model's fidelity to the doc, none affect
soundness: the remaining eighteen rows of §6 (`≡` is defined and the two rows other
sections rely on — `nullable`'s idempotence, `union`'s commutativity — are proved;
`union`'s commutativity is proved for the adjacent transposition, which generates every
permutation, and lifting it to `List.Perm` is the obvious next step); widening `admA` past `literalS`/`dunion` (a numeric literal's read side
goes through the axiomatized `Double.ofDec`, so no syntactic set bounds it, and those
pairs still fall to (U) per input); a soundness lemma tying the judgement's `T` to the
denotation (`e`'s domain and `p`'s range land in `T`), which the `T` index now makes
statable; every `LawfulCore` composite now shares its clauses with the full-law counterpart, `set`
included — what differs there is (C), and only (C).

## Building

Open the repo in the **Lean 4 — codec calculus** devcontainer
(`.devcontainer/lean/devcontainer.json`) and run:

```sh
lake build
```

First build downloads the pinned toolchain (`lean-toolchain`) and, on a cold cache, builds
mathlib. The build is `sorry`-free and **warning-free**; any warning or error is a
regression, and so is an `#assert_axioms` failure in `Calculus/Axioms.lean`.
