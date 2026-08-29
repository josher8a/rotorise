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
verdict, but a reliable one: it fell 437 → 154 across the passes that introduced the
vocabulary below.

Two known failure modes, both seen in practice. It **under-counts** boilerplate that is
not one of the three forms — `Opaque.lean` shed 113 lines of `cases n with | zero => …`
openings without the count moving, so the *density* column got worse while the file got
better. And it **over-counts** the irreducible: the two `altCodec` inversion proofs are
sites by construction, because unfolding the definition once is exactly their job. Read
it as a trend on a block, never as a score.

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

Measured at `HEAD` (2026-08-29), 8644 lines across `Calculus/`. Regenerate with:

```sh
python3 scripts/vocab_audit.py          # add --sites to list them for triage
```

### The completeness matrix

| slot | filled | |
| --- | --- | --- |
| `carrier_X` — §3's `e : T ⇀ 𝔸`, `p : 𝔸 ⇀ T` | **23 / 24** | |
| `lawfulCore_X` / `lawful_X` — §2's laws | **22 / 24** | `extendRead` exempt: (MP) is the sanctioned breach |
| `X_e` / `X_p` — **what it writes, what it reads** | **21 / 48** | counting an `X_eq` that carries inversion across |

The obligation half of the vocabulary is done. **The observation half is 12% done.**
Every product, the union and all four wrappers now have both. The ten ground codecs,
`dunionCodec` and `opaqCodec` have neither — and of those, only `opaqCodec` carries a
measurable residue.

### What the remaining hand-unfolding is actually about

| what is being unfolded | sites | concentrated in |
| --- | --- | --- |
| **raw `Option` algebra** | **140** | **Combinators 52**, Discharge 36, Soundness 30 |
| `traverse` / list base cases | 29 | Opaque 19 |
| a named codec's `e`/`p` | 27 | Opaque 15 |
| association-list `lookup` | 19 | Combinators 7, Discharge 6 |
| union resolution (`altCodec`'s filter) | 16 | Equations 8, Combinators 4 |
| judgement premises (`Obligations`/`MPOk`) | 3 | Soundness 3 |

**Six sites in ten are not about codecs at all.** That is the finding, and it reframes
the gap: what is missing is not a *concept* but the place where each construction's
`Option` chain is discharged once — which is exactly what an inversion lemma is.

### Does inversion actually trivialize the proofs?

Density per block, against how complete that block's inversion vocabulary is:

| block | inversion | lines | sites | **per 100 lines** |
| --- | --- | ---: | ---: | ---: |
| array + record | complete | 249 | 0 | **0.0** |
| tuple | complete | 331 | 10 | **3.0** |
| wrappers | complete | 404 | 6 | **1.5** |
| set | complete | 569 | 23 | 4.0 |
| object | complete | 652 | 26 | 4.0 |
| union | complete | 700 | 31 | 4.4 |
| opaque | none | 839 | 41 | 4.9 |
| ground | none | 454 | 16 | 3.5 |

Monotone with one honest outlier. **`ground` is 3.5 with no inversion** — because
`pointCodec` already gives four of the ground codecs one shared proof. That argues *for*
the thesis rather than against it: shared construction, fewer sites. And the top of the
table is a controlled comparison — `array + record`, `tuple`, `union` and `wrappers` are
the blocks that gained inversion, same content before and after: 0.0, 3.0, 7.2 → 5.0,
and 8.9 → **1.6**. Where the whole block goes through its inversion lemmas the residue
is nearly nothing; where only half of it does (`set`, `object`, `_e` but no `_p`) it
sits at 5–6.5.

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
- ~~*"`orNull` — `nullable`, whose honesty premises are (U) for a two-option sum,
  specialised."*~~ — **cashed, and it corrected the specification.** `nullable(c)` and
  `union(c, ⟨NULL⟩-point)` are `≡` with *no* premise (`equiv_orNull_altCodec`), and the
  same codec only when the base does not touch the null point (`orNull_eq_altCodec`) —
  strictly stronger than honesty, which §3 had claimed was enough. The witness is
  `nullable(nullable(c))`. See `docs/codec-formalization.md` §4.
- `dunionCodec` is already *defined* as `altCodec`, so it comes free once the union has
  an iff.

Prose that names an identity but does not cash it is the same residue this convention
exists to remove.

## §5 The union, done — and one claim that did not survive

`altCodec_e` / `altCodec_p` are now stated as **iffs**, and they are the only place
`altCodec`'s definition is unfolded:

```lean
theorem altCodec_e {os μA v a} :
    (altCodec os μA).e v = some a ↔ ∃ o, os.filter (·.admitV v) = [o] ∧ o.c.e v = some a
```

Nine and ten lines respectively; `altCodec_e_admits`/`_p_admits` survive as the weaker,
one-directional corollaries for the places that do not need the uniqueness. What it
bought:

| | before | after |
| --- | ---: | ---: |
| `lawfulCore_altCodec` | 55 | **21** |
| `lawful_altCodec` | 25 | **20** |
| `equiv_altCodec_swap` | 45 | **31** |
| union block, sites per 100 lines | 7.2 | **5.0** |
| union block, sites | 49 | **18** |

**The claim that did not survive.** This section previously argued that
`Equations.lean`'s six arity lemmas — `altCodec_pair_e`/`_p`, `altCodec_triple_e`/`_p`,
`altCodec_nest_e`/`_p` — were "special-casing the arity, the classic symptom of a
missing general lemma", and predicted the iff would retire them. **It does not, and they
should stay.** Two reasons, both visible only on attempting it:

1. The iff characterises `= some a`. The arity lemmas are *equations*, covering the
   `none` case too, which is what the associativity argument needs — it reasons about
   where each side is *undefined*, not only where they agree.
2. They are not a workaround; they are a deliberate normal form. `resolve₂`,
   `resolve₃` and `resolveNested` turn a question about codecs into a question about
   booleans, which is what lets `nest_flat_resolve` do the case algebra once and lets
   §6's associativity be stated about *resolution* rather than about `Codec`.

Recorded here rather than quietly deleted, because the audit is only worth keeping if it
says what the attempt showed. The generalisable lesson: **arity-specific lemmas are a
smell only when they duplicate an argument, not when they name a normal form.**

Of the 18 union sites left, all are legitimate: 4 are the two iff proofs themselves —
the one place the definition is unfolded, by design — 8 are the arity lemmas computing
the filter at literal lists, and 6 are in `Discharge.lean` at the *admission* level
(`optionSemOf … .admitA`), below where the iff reaches.

What remains untested is the other half of the prediction: whether the iff makes §6's
open rows fall out. `equiv_altCodec_swap` and `equiv_altCodec_single` are now stated
through it; the rows that need `List.Perm` are the next probe.

## §6 The plan, ranked

| # | item | payoff |
| --- | --- | --- |
| ~~1~~ | ~~`altCodec_e`/`_p` as an iff~~ — **done**; the arity lemmas stayed, see §5 | 31 sites; 7.2 → 5.0 per 100 lines |
| ~~2~~ | ~~Wrapper inversion~~ — **done**; §6's wrapper rows now go through it too | 43 → 6 sites; 8.9 → 1.5 per 100 lines |
| ~~4~~ | ~~Complete the two partials~~ — **done**: `setCodec_p_eq`, and `fbDefaults` as the `filterMap` it is | set 5.0 → 4.0, object 6.5 → 4.0; four hand-rolled recursions and one duplicate retired |
| 3 | Cash the last identity: `pointCodec = carriedCodec` | the ten ground codecs inherit inversion (`nullable`'s was cashed and became a dichotomy — §4) |
| ~~7~~ | ~~`Discharge.lean`~~ — **done**: tag admission named on both sides, and the `refine`/`legacy` cases cite item 2's wrapper inversion | 50 → 36 sites; `adm_sound` 61 → 24 lines, `admA_sound` 51 → 20 |
| ~~5~~ | ~~`Obligations` per-rule~~ — **done**: §3's three side conditions named (`IsoCancels`, `ReadsCoherently`, `NullHonest`), and one accessor per rule | 26 → 3 sites |
| ~~6~~ | ~~`opaque`~~ — **done**, and not by inversion: `maxOf` names the four depth measures as one fold, and the budget-is-a-successor opening collapses to one clause | 952 → 839 lines, 57 → 41 sites |

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
