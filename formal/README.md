# Codec calculus — Lean 4 mechanization

Mechanizes `docs/codec-calculus.md`. The doc stays normative; this package is the proof
assistant checking it, and every deliberate divergence from the doc is commented at the
definition it touches.

## Layout

| Module                      | Doc section | Content                                                                                                                                                                                                                                                               |
| --------------------------- | ----------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Calculus/Domain.lean`      | §1          | `Member`, `Attr`, `Item`, the value language, `Double` axioms                                                                                                                                                                                                         |
| `Calculus/Codec.lean`       | §2, §5      | `Codec`, `Agree` (`≼`), `Lawful`/`LawfulCore`, corollaries (Q, read-side W), injectivity lemma — **proved**                                                                                                                                                           |
| `Calculus/Combinators.lean` | §3–§5       | The certified combinator algebra: ground codecs, `through`/`restrict` (iso/prism), `extendRead` (legacy), `orNull` (nullable), `seq`/`keyed`/quotiented products, `altCodec`+`UniqueAdmission` and `dunionCodec` (sums), `opaqCodec` — with one lawfulness lemma each |
| `Calculus/Term.lean`        | §3–§4       | Deep-embedded terms, fields, rest policies                                                                                                                                                                                                                            |
| `Calculus/Denote.lean`      | —           | `denote : Nat → Term → Codec`, pure dispatch into the combinators                                                                                                                                                                                                     |
| `Calculus/Typing.lean`      | §3–§5       | The judgement `⊢ c : T ⇝ μ`, both indices, with the held-set formers (`HSet`, `HStar`, `HProd`, `HMap`, `HNull`, `HObject`, `HUnion`, `HOpaque`); syntactic premises only                                                                                             |
| `Calculus/Soundness.lean`   | §5          | `Obligations` (semantic premises, fueled), `UAtCan := UniqueAdmission ∘ semsOf`, `MPOk` (legacy exemption), theorem statements                                                                                                                                        |
| `Calculus/Discharge.lean`   | §5          | The machinery of (K): `Kind`, `κ`, `ident`, `adm`/`admA` as structural recursions, `κ_sound`/`adm_sound`/`admA_sound`, and `uAtCan_of_separated` — the dischargers of (U), proved, with witnesses and the two counterexamples that repaired (K)                       |

**The mechanization is complete: the project builds with zero `sorry`.** Both halves
of §5's soundness theorem are machine-checked — `soundness` (all four laws, (MP) with
the legacy exemption as the `MPOk` hypothesis) and `soundness_core` ((R), (C), (W)
through `legacy`-containing derivations) — by induction on the judgement, dispatching
each case to its certified combinator lemma, with the `(dunion)` stamps derived from
typing and (U) discharged by `uniqueAdmission_byTag` / `uniqueAdmission_of_disjoint`.
The judgement carries both of §3's indices — the held set `T` and the member `μ`. The
member index is fuel-free (`μSyn`, with `denote_μ` and `typed_μSyn` tying the denotation
and the judgement to it), and `lazy` concludes `⊤` in the model exactly as the doc's
`(lazy)` rule demands.

## Modelling decisions

- **No mathlib yet.** The definitions don't need it; wire sets/maps are lists (a quotient
  cannot sit recursively inside an inductive), and set-ness lives where the doc puts it —
  in `ker p`. Revisit when attacking `lawful_objectCodec` (roadmap item 6).
- **Fuel-primary denotation.** Every recursive call decrements fuel; `lazy` is free and
  termination is structural on `Nat`. Fuel 0 denotes `Codec.empty` (laws vacuous) — the
  doc's "partiality is doing the termination argument's work", literally. Laws are
  stated `∀ fuel`.
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
soundness: widening `admA` past `literalS`/`dunion` (a numeric literal's read side
goes through the axiomatized `Double.ofDec`, so no syntactic set bounds it, and those
pairs still fall to (U) per input); a soundness lemma tying the judgement's `T` to the
denotation (`e`'s domain and `p`'s range land in `T`), which the `T` index now makes
statable; deriving the remaining `LawfulCore` composites (`tuple`, `set`, `object`) and their full-law
counterparts from one another, as the wrappers and uniform products now are.

## Building

Open the repo in the **Lean 4 — codec calculus** devcontainer
(`.devcontainer/lean/devcontainer.json`) and run:

```sh
lake build
```

First build downloads the pinned toolchain (`lean-toolchain`). The build is
`sorry`-free; any warning or error is a regression.
