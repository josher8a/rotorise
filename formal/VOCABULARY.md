# The codec vocabulary — the convention, and where it is incomplete

`README.md` says what the package proves. This one says how its proofs are meant to
*read*, why, and — measured rather than asserted — where they do not yet.

The premise: a proof about a codec should be written in the vocabulary of §2–§5, not in
the vocabulary of `Option`. Where it is not, that is **accidental complexity**, and it is
visible as a specific tic. Everything below follows from taking that seriously.

---

## §1 The rule

> **A definition is unfolded once, in its own inversion lemma. Every proof downstream
> cites the lemma.**

Each construction gets two:

```lean
theorem X_e : (X …).e v = some a ↔ ⟨what X writes⟩
theorem X_p : (X …).p a = some v ↔ ⟨what X reads⟩
```

proved in one step — `simp [X, Option.bind_eq_some, Option.map_eq_some']` — and that step
is the *only* place the construction's `Option` chain is ever taken apart. Downstream,
`obtain ⟨…⟩ := X_e.mp he` opens a proof in one line and `X_e.mpr ⟨…⟩` closes it in one.

The tic this replaces is the eight-line hand unfolding:

```lean
replace he : (traverse c.e vs).map Attr.l = some a := he      -- retype by defeq
cases htr : traverse c.e vs with                              -- split the chain
| none => rw [htr] at he; exact nomatch he                    -- refute the dead branch
| some as =>
  rw [htr] at he
  replace he : some (Attr.l as) = some a := he                -- retype again
  cases he                                                    -- Option.some.inj by hand
```

It says nothing about codecs. It was written a few hundred times.

**The signal.** `replace h : … := h`, `show …` and `cases h… :` are the three ways a
proof takes a definition apart by hand. Their count is the trend to watch — not a
verdict (a few are irreducible), but a reliable one: it fell 437 → 186 across the three
passes that introduced the vocabulary below.

A companion rule already stated in `Calculus/Lists.lean` and worth repeating: **citing a
name from `Lists.lean` is the signal that a step is plumbing rather than content.**
Anything about `Option`, `List`, `traverse` or `lookup` belongs there, so that a step
which is *not* about codecs is visibly not about codecs.

## §2 The naming scheme

Consistent today; normative from here, so the next proof inherits it.

| form | means |
| --- | --- |
| `X_e` / `X_p` | inversion — what `X` writes, what `X` reads |
| `X_eq` | `X` **is** an instance of a named construction, on the nose |
| `lawfulCore_X` / `lawful_X` / `carrier_X` | the three obligations, in that order |
| `f_sound` | a syntactic function agrees with the denotation (`κ_sound`, `adm_sound`) |
| `equiv_X` | a §6 row |
| `not_X` | a refutation — a "Do not hold" row, or a repaired discharger |
| `onKind_X` | `X` is pinned to a kind (§3's "self-identifying") |

Two further conventions the passes settled on, both load-bearing:

- **The core lemma is not a second proof.** `lawfulCore_X` and `lawful_X` share their
  clauses (`tuple_retract`/`tuple_canon`, `object_retract`/`object_canon`,
  `set_retract`/`set_writes`) and differ only where the content differs. Today that is
  one place: `set`'s (C), where (MP)'s member-uniformity is replaced by the `(set)`
  rule's own premise.
- **An identity stated in prose gets cashed as an equation.** `arrayCodec_eq`,
  `recordCodec_eq`, `tupleCodec_eq`, `objectCodecCore_eq` each say "this construction
  *is* that one", and carry every lemma across by `▸`. §4 below lists the three
  identities still stranded in prose.

## §3 The audit

Measured at `fa2a561` (2026-08-29), 8768 lines across `Calculus/`. Regenerate with:

```sh
python3 scripts/vocab_audit.py          # add --sites to list them for triage
```

### The completeness matrix

| slot | filled | |
| --- | --- | --- |
| `carrier_X` — §3's `e : T ⇀ 𝔸`, `p : 𝔸 ⇀ T` | **23 / 24** | |
| `lawfulCore_X` / `lawful_X` — §2's laws | **22 / 24** | `extendRead` exempt: (MP) is the sanctioned breach |
| `X_e` / `X_p` — **what it writes, what it reads** | **6 / 48** | |

The obligation half of the vocabulary is done. **The observation half is 12% done.**
`carriedCodec` and `entrywise` have both; `setCodec` and `objectCodecCore` have `_e`
only; the ten ground codecs, all four wrappers, `altCodec`, `dunionCodec` and
`opaqCodec` have neither.

### What the remaining hand-unfolding is actually about

| what is being unfolded | sites | concentrated in |
| --- | --- | --- |
| **raw `Option` algebra** | **219** | Combinators 99, Discharge 47, Soundness 30 |
| `traverse` / list base cases | 41 | Opaque 27 |
| union resolution (`altCodec`'s filter) | 34 | Equations 16, Combinators 12 |
| a named codec's `e`/`p` | 28 | Opaque 19 |
| judgement premises (`Obligations`/`MPOk`) | 26 | Soundness 26 |
| association-list `lookup` | 21 | Discharge 8 |

**Six sites in ten are not about codecs at all.** That is the finding, and it reframes
the gap: what is missing is not a *concept* but the place where each construction's
`Option` chain is discharged once — which is exactly what an inversion lemma is.

### Does inversion actually trivialize the proofs?

Density per block, against how complete that block's inversion vocabulary is:

| block | inversion | lines | sites | **per 100 lines** |
| --- | --- | ---: | ---: | ---: |
| array + record | complete | 249 | 0 | **0.0** |
| tuple | complete | 331 | 10 | **3.0** |
| set | `_e` only | 581 | 29 | 5.0 |
| object | `_e` only | 736 | 48 | 6.5 |
| opaque | none | 952 | 57 | 6.0 |
| union | none | 680 | 49 | **7.2** |
| wrappers | none | 481 | 43 | **8.9** |
| ground | none | 453 | 16 | 3.5 |

Monotone with one honest outlier. **`ground` is 3.5 with no inversion** — because
`pointCodec` already gives four of the ground codecs one shared proof. That argues *for*
the thesis rather than against it: shared construction, fewer sites. And the top of the
table is a controlled comparison — `array + record` and `tuple` are the blocks that
gained inversion during the passes, same content before and after, and their sites went
to zero and three.

## §4 What the evidence does *not* say

**No new codec-level abstraction is warranted.** The construction set is right: §7 of the
specification claims products and coproducts are the irreducible structure and everything
else wraps one subterm, and `carriedCodec` absorbing four of the six products is that
claim cashed. Another layer on top of `carriedCodec` would be a second storey on a house
with no windows.

What the evidence *does* point at is three identities the development already states in
prose and never cashes:

- *"`pointCodec` is the degenerate case, where the payload passes through untouched."*
  → `pointCodec_eq : pointCodec V A μ₀ = carriedCodec V A μ₀ _ some some`, which would
  hand inversion to all ten ground codecs at once.
- *"`orNull` — `nullable`, whose honesty premises are (U) for a two-option sum,
  specialised."* → `orNull_eq`, after which the densest block in the table inherits the
  union's vocabulary.
- `dunionCodec` is already *defined* as `altCodec`, so it comes free once the union has
  an iff.

Prose that names an identity but does not cash it is the same residue this convention
exists to remove.

## §5 The one item with the highest payoff

`altCodec_e` / `altCodec_p`, **as an iff**:

```lean
theorem altCodec_e {os μA v a} :
    (altCodec os μA).e v = some a ↔ ∃ o, os.filter (·.admitV v) = [o] ∧ o.c.e v = some a
```

`altCodec_e_admits` exists but is one-directional and lossy — it drops the uniqueness and
has no `.mpr`, so it can *open* a union proof and never *close* one. Three pieces of
evidence that this is the gap:

1. It is cited 9 times; the other 49 union sites hand-roll the filter case split.
2. `Equations.lean` invented six bespoke replacements — `altCodec_pair_e`/`_p`,
   `altCodec_triple_e`/`_p`, `altCodec_nest_e`/`_p`, plus `nest_flat_resolve`.
   Special-casing the **arity** is the classic symptom of a missing general lemma.
3. `filter_swap_singleton` is already sitting in `Equations.lean`, waiting for the iff
   that would let `union`'s commutativity cite it directly.

It is also the one item where readability and *content* payoff coincide: §6's remaining
rows are largely union rows, and with the iff a union theorem becomes a statement about
`List.filter` — plumbing, which `Lists.lean` can own.

## §6 The plan, ranked

| # | item | payoff |
| --- | --- | --- |
| 1 | `altCodec_e`/`_p` as an iff; retire the six arity lemmas | 49 sites; unblocks §6's open rows |
| 2 | Wrapper inversion (`through`, `restrict`, `extendRead`, `orNull`) | 43 sites — the densest block, and four one-line definitions |
| 3 | Cash the three identities of §4 | ground and `nullable` inherit everything |
| 4 | `setCodec_p`, `objRead` inversion — complete the two partials | 77 sites |
| 5 | `Obligations`/`MPOk` per-rule inversion | 26 sites, all in `Soundness.lean` |

## §7 Making it mechanical

`Calculus/Axioms.lean` is the precedent: it turned "the axiom base is `propext`,
`Quot.sound` and the `Double` axioms" from a claim in prose into a build error, and it
caught two real leaks while it was being written. Two more checks are available on the
same principle, and neither is expensive:

- **Ratchet the site count.** `scripts/vocab_audit.py` already reports it. Failing the
  build when it *rises* makes the convention of §1 enforceable rather than aspirational.
- **Docstring coverage on public theorems** — 203 of 425 are undocumented today, and
  `Opaque.lean` is 51 of 55. The bar is not "every lemma": it is that a reader who knows
  the specification can tell what a theorem says from its name and one line.

## §8 What is deliberately long

Two proofs are near the top of the length table and should stay there.
`soundness_both` (153 lines) and `carrier_denote` (132) are one line per typing rule —
a table of which two combinator lemmas each rule cites. That is the right shape for a
theorem whose content *is* the rule-by-rule dispatch, and compressing it further would
cost the reader the correspondence with §3–§5. Length is not the metric; **sites are.**
