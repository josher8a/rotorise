# Codec calculus — Lean 4 mechanization

Mechanizes `docs/codec-calculus.md`. The doc stays normative; this package is the proof
assistant checking it, and every deliberate divergence from the doc is commented at the
definition it touches.

## Layout

| Module                      | Doc section | Content                                                                                                                                                                                                                                                               |
| --------------------------- | ----------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Calculus/Lists.lean`       | —           | The list plumbing: `traverse` and its laws off the pivot `traverse_eq_some` (a successful traversal *is* `List.Forall₂ (f · = some ·)`), `List.lookup` on association lists, and the `filter`/`zip` facts mathlib states in the wrong shape — everything with no codec in it, kept apart so `Combinators.lean` reads as codec vocabulary |
| `Calculus/Domain.lean`      | §1          | `Member`, `Attr`, `Item`, the value language, `Kind` with `Value.kind`/`Attr.kind` (the ten members collapsing onto eight), `Double` axioms, and `Numeral.WF` — §1's numeral grammar, 38 significant digits and magnitude range, as a decidable predicate                                                                                            |
| `Calculus/Codec.lean`       | §2, §5      | `Codec`, `Agree` (`≼`), `Lawful`/`LawfulCore`, corollaries (Q, read-side W), injectivity lemma — **proved**                                                                                                                                                           |
| `Calculus/Combinators.lean` | §3–§5       | The certified combinator algebra, opening with `Ctor` — a constructor as a partial iso onto its image, the prism §7 names. The point ground codecs (`string`, `boolean`, `binary`, `null`) are `pointCodec` at four pairs of prisms and share one lawfulness proof; the wire-set payload projections are the same shape again. Then `through`/`restrict` (iso/prism), `extendRead` (legacy), `orNull` (nullable), `carriedCodec` — a payload pair carried between two prisms, the shape underneath every product: `entrywise` is it at a traversal (`array`, `record`, left with only the shape of `≼` at their attribute constructor), `tupleCodec` it at `align` + a traversal, over `slots` — the codec row a shape assigns to a row of *n* positions, which is what makes alignment depend on length alone; the remaining products, `altCodec`+`UniqueAdmission` and `dunionCodec` (sums), `opaqCodec` — with one lawfulness lemma each |
| `Calculus/Term.lean`        | §3–§4       | Deep-embedded terms (including §3's `null` point), fields, rest policies                                                                                                                                                                                                                            |
| `Calculus/Denote.lean`      | —           | `denote : Nat → Term → Codec`, pure dispatch into the combinators                                                                                                                                                                                                     |
| `Calculus/Typing.lean`      | §3–§5       | The judgement `⊢ c : T ⇝ μ`, both indices, with the held-set formers (`HSet`, `HStar`, `HProd`, `HMap`, `HNull`, `HObject`, `HUnion`, `HOpaque`); syntactic premises only                                                                                             |
| `Calculus/Soundness.lean`   | §5          | `Obligations` (semantic premises, fueled), `UAtCan := UniqueAdmission ∘ semsOf`, `MPOk` (legacy exemption), theorem statements, and the held-set bridge `carrier_denote`/`typed_TSub`/`typed_e_mem`/`typed_p_mem`                                                    |
| `Calculus/Equations.lean`   | §6          | `Codec.Equiv` (§6's `≡`), `Can`, and all eleven of §6's "Hold" rows — `held`'s identity and composition, `refine`'s meet and full case, `legacy` with its own reading and `≈` on `Can(c)`, `union` of one, its commutativity and its associativity (which needs none of §6's stated conditions), `nullable`'s idempotence, wrapper member preservation |
| `Calculus/Opaque.lean`      | §3, §7      | `opaque` without fuel: `Value.depth`/`Attr.depth`, the eighteen kind-disjoint unfoldings (one `simp` set for the section, one line each), `opaq_e_agree`/`opaq_p_agree` (stabilization), `opaq_e_depth`/`opaq_p_depth` (depth preservation), and `opaqCodecω` with `lawful_opaqCodecω`/`carrier_opaqCodecω` |
| `Calculus/HeldSet.lean`     | §1, §3, §6  | `T` as an identity: `opaq_T_identity` (`Uν` *is* `opaque`'s held set), `not_TIsDomE_unionLiteralString` (§6's row is two identities and `union` has only the weaker one), and the numeral-domain report — `decimal_writes_stored`/`decimal_reads_stored` with worked boundary cases |
| `Calculus/Continuity.lean`  | §5, §7      | Why `union` admits no fixpoint semantics: `Codec.Approx` (the information order any ccpo must extend), `altCodec_not_monotone` (unique admission is anti-monotone in the options) and `stage_not_monotone` — the same collapse over a staging defined locally, since `denote` is structural and no longer stages |
| `Calculus/Nesting.lean`     | §1          | **The one place `𝔸` is bigger in the model than in the store.** `Attr.Storable` (`Domain.lean`) is §1's 32-level bound, counting `L` and `M` only — a different function from `Attr.depth`, which is a termination measure and charges a wire set a layer. The ground fragment writes nesting `0`, containers add exactly one, and `not_storable_of_typed` exhibits a **derivable** term whose encoding the store refuses: the bound is absent from §3's rules rather than a premise someone failed to discharge |
| `Calculus/Refutations.lean` | §6          | §6's "Do not hold" table, all nine settled: `not_equiv_lazy` (the row where `≡`'s member index matters), `not_equiv_union_array`, `not_equiv_union_extend`, the two `tuple`-tail rows, `not_equiv_refine_held`, `legacy_breaks_MP`, `e_comp_p_ne_id`, `not_typed_set_union` — plus `optional` nesting, which the syntax rules out |
| `Calculus/Axioms.lean`      | §3          | `#assert_axioms`, and the headline theorems run through it — the advertised axiom base (`propext`, `Quot.sound`, the `Double` axioms; **no `Classical.choice`**) as a build error rather than a claim in prose |
| `Calculus/Discharge.lean`   | §5          | The machinery of (K): `κ`, `ident`, `adm`/`admA` as structural recursions (`Kind` itself is §1, and lives in `Domain.lean` on both sides of the pair), `κ_sound`/`adm_sound`/`admA_sound`, and `uAtCan_of_separated` — the dischargers of (U), proved, with witnesses and the two counterexamples that repaired (K)                       |

**The mechanization is complete: the project builds with zero `sorry`.** Both halves
of §5's soundness theorem are machine-checked — `soundness` (all four laws, (MP) with
the legacy exemption as the `MPOk` hypothesis) and `soundness_core` ((R), (C), (W)
through `legacy`-containing derivations) — by induction on the judgement, dispatching
each case to its certified combinator lemma, with the `(dunion)` stamps derived from
typing and (U) discharged by `uniqueAdmission_byTag`, and `opaque`'s by
`uniqueAdmission_of_kinds`.
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
- **Fuel-primary denotation, now with a fuel-free twin.** `denote` still takes fuel and
  **there is no fuel.** `denote : Term → Codec` is structural, and the two files that used
  to hold a second fuel-free denotation and the transport to it — `Denoteω.lean`,
  `Soundnessω.lean` — are deleted: `denoteω` was a name for `denote`, companion for
  companion. What the proofs recurse on instead is `Term.depth`, a measure derived from the
  term, so it appears in no statement. Fuel 0 still
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
  cannot; `stage_not_monotone` shows the same collapse between two adjacent stages, on
  `union(literal("A"), lazy(string))` — §5's own counterexample pair, staggered.
  Note the direction: the low-stage answer is *over*-defined, not under-defined.
  The staging is defined in `Continuity.lean` itself, as a witness rather than a
  semantics: `denote` is structural and does not stage, and the reason it need not is
  the refutation above — `Term.lazy` carries a plain `Term` rather than a thunk, so
  there is no recursion to approximate. See `docs/codec-formalization.md` §7.
- **One construction, one place — and one proof per law.** Each construction's
  definition, its two inversion lemmas, its carrier and both strengths of its
  lawfulness now sit together, and the core lemma is no longer a second copy of the
  full one: they share their clauses (`tuple_retract`/`tuple_canon`,
  `object_retract`/`object_canon`, `set_retract`/`set_writes`), differing only where
  the content differs — `set`'s (C), where (MP)'s member-uniformity is replaced by the
  `(set)` rule's own premise. The shape underneath is `carriedCodec`, a payload pair
  between two prisms; `pointCodec`, `entrywise` (hence `array`, `record`), `tuple` and
  `object` are all instances, so §2's prism halves are discharged once for all of them.
  `set` is the one product that is not, and the reason is stated where it is argued:
  its attribute side is a choice among three wire sets, not one constructor.
- **`opaque`'s (U) is computed from kinds, not argued per option.** `Kind` is §1
  vocabulary now (`Domain.lean`), on both sides of the pair — `Value.kind` and
  `Attr.kind`, the ten members collapsing onto eight. An option is *pinned to a kind*
  when it admits only values and attributes of that kind (`OptionSem.OnKind`), and
  `uniqueAdmission_of_kinds` turns pinned options with distinct kinds into (U). Each of
  `opaque`'s eight is pinned in one line, and `onKind_set`/`onKind_array`/`onKind_record`
  hold for *any* element codec — which is why the fixpoint's unique admission needs
  nothing from the recursive call, and why `opaque` is not a special construction.
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

## Is the model the specification?

[`FIDELITY.md`](./FIDELITY.md) is the representation audit — two independent readings, in
opposite directions, of whether every normative element of `docs/codec-calculus.md` has an
exact counterpart here and whether a reviewer could check one in isolation. It records
seven specification defects (three found by both readings independently), five claims that
are true but unlocatable, two corrections to this package's own artifacts, and a measured
review surface. Regenerate the measurements with `python3 scripts/fidelity_audit.py`.

The headline: the guard puts 63 constants through `#assert_axioms` while the documents
cite 133 as results, §-tag coverage is 24%, and **60% of theorem statements name a
definition that is documented nowhere** — a statement a reviewer cannot read against the
specification without a detour. (The guard's count was 17 when the audit was written;
items 1–5, 8 and 9 of its plan closed the gap it measured, and its §5 records which.)

## Do the documents still name what exists?

Prose does not typecheck. Deleting a declaration leaves the build green and every citation
of it dangling, and both drift findings before the residue sweep were caught by luck.
`python3 scripts/name_drift.py` closes that: it reports every backticked Lean name in the
current-state documents — this file, `FIDELITY.md`, `VOCABULARY.md`, `docs/codec-calculus.md`,
`docs/structural-discipline.md` — that no longer occurs anywhere in `Calculus/`, and exits
non-zero if there is one. Deliberate citations live in an `EXPECTED` table with a reason
each, and the check fails if an entry there stops being cited, so the table cannot rot
quietly either. `--all` also scans `docs/codec-formalization.md`, which is the change log
and is *expected* to name things that have since been deleted.

This is `Axioms.lean`'s principle at the documents: a claim that fails the build rather than
a claim in prose.

## How the proofs are meant to read

[`VOCABULARY.md`](./VOCABULARY.md) is the convention — a definition is unfolded once, in
its own inversion lemma, and every proof downstream cites the lemma — together with the
naming scheme, a measured audit of where the vocabulary is still incomplete, and the
ranked plan for closing it. The numbers regenerate: `python3 scripts/vocab_audit.py`.

The short version: the *obligation* half of the vocabulary is done (22/23 carriers,
21/23 lawfulness lemmas); the *observation* half — `X_e`/`X_p`, what a construction
writes and reads — is 25 of 48. Six of every ten remaining hand-unfoldings are `Option`
algebra rather than anything about codecs. The controlled comparison is the four blocks
that *gained* inversion during the arc, same content before and after: 7.2 → 5.0 and
8.9 → 1.5 sites per hundred lines, with `array + record` at 0.0 and `tuple` at 3.0.
Across all blocks the spread is now 0.0–5.1, so the separation is real but narrower than
a first reading of the table suggests — `ground` sits at 3.5 with no inversion at all,
because `pointCodec` gives four of the ground codecs one shared proof.

## What remains (sharpenings, not gaps)

The theorem is proved; these tighten the model's fidelity to the doc, none affect
soundness. `union`'s commutativity is proved for the adjacent transposition, which
generates every permutation, and lifting it to `List.Perm` is the obvious next step.
An entry that used to sit here said `admA` stops at `literalS`/`dunion` — that a numeric
literal's read side goes through the axiomatized `Double.ofDec`, so no *syntactic* set
bounds it, and those pairs fall to (U) per input. The premise holds and the conclusion did
not: the row does not have to name its set, it can ask its codec, and `ofDec` being a
function is enough to make the answer unique. `admA number` and `admA literalN` are now
`dom(p)` exactly (`sepA_number_opaque`, `sepA_literalN_disjoint`). What the observation
about the store was really about survives on the other side of the pair: a literal's stored
texts are known at the declaration, but `10²¹` is written `1e+21` and handed back
normalised, so a row that tested the *text* would refuse a row the codec itself wrote —
which is why the row tests the codec instead. Three entries that used to sit here are done — §6's rows are all proved
(see `FIDELITY.md` for what "all" is worth on the commutativity row), and `typed_TSub`
ties the judgement's `T` to the denotation, `typed_e_mem` and `typed_p_mem` being the
statements a reviewer wants.

## Building

Open the repo in the **Lean 4 — codec calculus** devcontainer
(`.devcontainer/lean/devcontainer.json`) and run:

```sh
lake build
```

First build downloads the pinned toolchain (`lean-toolchain`) and, on a cold cache, builds
mathlib. The build is `sorry`-free and **warning-free**; any warning or error is a
regression, and so is an `#assert_axioms` failure in `Calculus/Axioms.lean`.
