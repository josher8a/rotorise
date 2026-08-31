# Audit: what the five representation repairs left behind

*Opened 2026-08-31, branch `wip/map-types`. All eight scans reported. Items are struck
through as they land in the tree.*

~~**The single most consequential finding is §9: five live bugs in the shipped TypeScript,
four of them C1 violations concentrated in one file, including two that §4 records as
already fixed.**~~ **Landed.** All five are closed in the tree — the four C1 violations by
gating both halves of `native`'s `N` and refusing an empty stored set, the fifth by making
`literal()` a construction-time refusal. `Carries('N')` moved out of `codec.ts` and into
`attribute.ts` on the way, which is why one file could close four bugs in another: the
predicate is a property of the carrier, and there is now one of it. See §9.7.
Everything else in this file is hygiene by comparison.

## Why this exists

Five representations were retyped in one arc: `M`'s payload, the object field table,
`℘⁺fin`, a literal's alternatives, and `Carries(N)`. Each replaced a *gate* — a `Bool` side
condition or a rule premise — with a *type* that makes the condition structural. Each also
left residue: machinery that existed only to repair the old representation, and prose
written when the old representation was current.

A green build hides both. Dead code compiles, and **prose does not typecheck** — the two
drift findings before this audit were caught by luck. Hence parallel read-only scans, each
timeboxed. This file is their output and the disposition of each item.

## 1. Actionable queue

| # | site | problem | deletes | radius |
| --- | --- | --- | --- | --- |
| 1 | `Domain.lean:9-13` | File header **inverted on four clauses**: wire sets and maps "are lists", the numeral carrier "stays unrestricted on purpose", set-ness lives in `ker p` "not in the carrier". Self-contradicted 290 lines later in the same file. | — | trivial |
| 2 | `codec-formalization.md:2108`, `:2111` | Two §6 summary rows. `:2108` still says the carrier is unrestricted. `:2111` is **my own edit** and is wrong three ways: types are `NEFinset` not `Finset`, `encSet`'s card check is gone, non-emptiness is not gated at all. §6 is a summary a reader trusts — not covered by §4's supersession rule. | — | trivial |
| 3 | `codec-calculus.md:87-88`, `:167-172`, `:559-560` | The **specification's** justification for the `ker p` quotient still lists *three* reasons, the first being set orderings. False in §1's own terms now the carriers are `℘⁺fin`. Should be two: `η` normalising `N`, `drop` discarding names. | a bullet + follow-on | small |
| 4 | `WireOrder.lean` | **17 of 19 declarations dead** (independently found by two scans); header argues for a design the code abandoned. Only `Axioms.lean` imports it, for the axiom scan. The `Classical.choice` warning about `LinearOrder String` is a real hazard and must be relocated, not lost. | ~247 lines | small |
| 5 | `Domain.lean:344` | `Item := List (Name × Attr)`, docstring calls it "an `M` without its wrapper" — the exact shape five sites removed, beside the repaired `Attr.m`. **Dead**: grep finds only the declaration. | the declaration | none |
| 6 | `Typing.lean:165-167` | `literalOK` does two jobs: `Numeral.WF` on `.num` (content, stays) and `\| _ => false` for containers, which is just *"this value has a ground base"* — a claim about the field's carrier. `Term.literal (v : GroundValue)` makes `literalMember` total. | **all of `hμ`**, the container half of `hok`, the `hok` arg of two laws, a case in `Exactness` | small (11 sites) |
| 7 | `Combinators.lean:3324, 3375, 3406` +2 | `objectCodecCore` takes `kn : Name → Bool` free; the only instantiation is `keepB rest sems`. Three hypotheses across five signatures all say *the filter never discards a declared name*. | 3 hypotheses × 5 signatures, plus `keepB_of_encEntry` and `keepB_of_declared` | medium (43 sites) |
| 8 | ~61 declarations | Transitively dead plumbing, listed in §4.1. | ~61 decls | small, mechanical |
| 9 | `codec-calculus.md:249-251`, `:301-302`, `:938-944`, `:1034` | §3 still presents both number rules as `refine` over an **ungated base** (those bases cannot exist); §5's traversal Lemma still has a "keyed lists … first occurrence first" clause (keys are unique by type, so it names nothing); `:1034` calls a wire set "the lifted list". | one clause | small |
| 10 | `Lists.lean:13-22` | Header advertises "three groups" incl. `List.lookup` on association lists, "the pivot is `lookup_cons`". Group deleted; `lookup_cons` exists nowhere. The file contradicts itself at `:81`. | — | trivial |
| 11 | `Discharge.lean:529` | The one `set_option maxHeartbeats` of three with **no justifying comment**. Re-measure — it may not be needed after the representation changes. | possibly the option | trivial |
| 12 | `Combinators.lean:3507` | `keepB_of_encEntry` still carries the name of a deleted definition. Rename. | — | trivial |
| 13 | `Refutations.lean:443` | `abbrev decimalWF : Codec := wfDecimalCodec` — the leftover half of a unification I did; its two `rfl` lemmas are free either way. | alias + 2 lemmas | trivial |
| 14 | `Exactness.lean:980`; `codec-formalization.md:673`; `codec-calculus.md:1129` | Low: "`Numeral` is `String`" no longer explains why the numeric witness is free; a dangling `rawNumberCodec` inside a superseded §4 entry; §7 labelling `set` "quotiented", still true of `p`'s non-injectivity but reads as the withdrawn ordering quotient. | — | trivial |

## 2. Closed questions — verified impossible, do not re-test

### 2.1 `union` / `dunion` option lists: the defect is real and unfixable

Four theorems compiled to settle it:

```lean
altCodec_e_swap, altCodec_p_swap   -- order unobservable, extensionally
select_dup_none                    -- multiplicity IS observable
dincomp_dup                        -- DIncomp is irreflexive
```

**Order is unobservable at full extensional strength**, not merely up to `≡`. That matters:
`Codec.Equiv` is deliberately weak (`e`/`p` agree only where both are defined, and it is not
transitive), so `equiv_altCodec_swap` alone could not have settled it. But `select` reads the
list only through `filter … = [o]`, and a singleton is permutation-stable, so the `e` and `p`
*functions* are literally equal under a swap; `T` and `unanimous` are permutation-invariant;
adjacent swaps generate every permutation.

**Multiplicity is observable** — `select_dup_none` is the mechanism behind `not_ExactV_union`,
so dedup would change behaviour and `Finset` is semantically wrong even where constructible.

Together: `List` admits *n!* terms per denotation, so the shape **is** wrong; but the fitting
type is `Multiset Term`, barred by the quotient-under-an-inductive rule `Domain.lean`'s header
already cites, and `Finset Term` is barred twice (element type under declaration, *and* no
`DecidableEq Term` — `held`'s `f`/`g`, `custom`'s pair, `refine`'s `q`, `legacy`'s `r`). No
concrete key type, so the key-set-plus-function factoring does not apply.

Four hats: `Term.union`, `Term.dunion`, `List OptionSem`, `dunionCodec`'s list. Two notes:

- `dunion` is the **cleanest instance**: `htags` + `hdisj` make duplicates unreachable, so its
  list is a true set with no compensating observable at all.
- `DIncomp` is irreflexive, so `union [.string, .string]` is **not even `Typed`**. (D) is the
  only thing between the judgement and the duplicate-option defect — load-bearing in the real
  sense, not a candidate for weakening.

**Disposition:** a header note at `Term.lean`, analogous to the old `Value.set` remark.

### 2.2 Gates that are content and must stay

| gate | site | why |
| --- | --- | --- |
| `hD : ∀ d ∈ ℓ, Numeral.WF d.toDec` | `Typing.lean:176` | Typing it needs `NEFinset {d // WF d.toDec}`, which changes what `ℓ` *is* and **silently deletes** the (B) defect `literalN_holds_what_it_cannot_write` exhibits rather than proving it absent. |
| `hsm : setMember μ₀ = some μS` | `Typing.lean:179` | Says the element's member is `S`/`N`/`B`, which selects `encSet`'s branch. `Term.set` holds a `Term` — no carrier to subtype. |
| `hfb` (six signatures) | `Combinators.lean:3323` +5 | `FieldSem.fb (c) (v : {v // (c.e v).isSome})` *is* admissible and strikes all six — but cannot reach the syntax, since `Field.fallback` has no `denote` and no fuel. `fieldSemOf` would supply the proof: same obligation, moved. Net ≈ 0. |
| `htags`, `hdisj` | `Typing.lean:207-210` | `htags` is shape-shaped, but `tagsOf` *computes* the set from the term — no stored field to subtype. Storing them duplicates derived data and needs a coherence gate of its own. |
| `hnd : ks.Nodup` | `Combinators.lean:3691` | `Finset Kind` *is* available, but `ks` is bound positionally to `os` by `List.Forall₂`, so order is load-bearing and `Nodup` cannot be separated from the pairing. |
| `Obligations` / `MPOk` | `Soundness.lean:55-104` | All four remaining premises are semantic relations. `MPOk (.legacy _ _) = False` reads typeable, but needs a second mutual `Term` family plus an embedding — structural duplication for a one-line gate. |

### 2.3 Collections already correctly typed

Confirmed with the theorem that settles each: `Attr.l` / `Value.arr` (the reference says lists
are ordered and heterogeneous); `Term.tuple`, `align`/`slots`/`tupleCodec`, `HTuple`/`HProd`
(position *is* the semantics — `align_eq_zip`, `slots_length`); `HUnion`/`DIncomp` and the
`TypedList*` families (permutation-invariant in themselves, but bound positionally to `opts`,
so `List` is *forced* by the correspondence); the `denoteω*`/`κList`/`admList` folds (`||`,
`&&`). `FieldSem`/`RestSem` are not collections; their table is already `MapOf FieldSem`.

## 3. Corrections to my own record

Both caught by putting my claim into a scan's prompt as something to check, not as context.

**The rule in §4 is too narrow.** I wrote that a gate is typeable when it constrains a
collection's *shape*, content when it constrains *what the elements are*. Queue item 6 is
element-level and typeable anyway, because what is too wide is the **carrier of a
non-recursive field** — the same move `Attr.n : WFNumeral` was. As stated, the rule would
have told me to skip it. It needs the third clause.

**My `union` inference was wrong.** I argued that duplicates being observable made `List`
right. Duplicates rule out `Finset`; they say nothing about order, which is separately
unobservable. Correct conclusion: the shape is wrong and the fitting type is barred (§2.1).

## 4. Residue sweep

978 top-level declarations scanned across 19 files. 663 have no in-code reference — **not a
defect count**, this development is mostly leaf results. 153 of those are also absent from all
three documents, carry no attribute, and match no result-naming pattern. 86 theorems have a
trivial proof. **0** pairs of definitions share a body.

### 4.1 Plumbing, safe to delete (~61)

- **`adapt`/`restrict` bridging family** (10), `Combinators.lean:360-535` — left over from when
  `through`/`restrict` went via a general `adapt`; the representations now coincide
  definitionally, which is why most are `rfl`.
- **Payload-traversal cluster** (8), `Combinators.lean:688-2750` — `numPayloads`/`binPayloads`
  are used by nothing but their own laws; the group falls together.
- **Other `Combinators` plumbing** (7) — incl. `entrywise_e`/`entrywise_p`, whose proofs are
  literally `:= carried_e` / `:= carried_p`, and the three `attr_*_of_member` inversion lemmas
  superseded by the tag-projection work.
- **`Discharge.lean`** (21) — the largest concentration, incl. a self-contained
  boolean-literal example cluster and a `dunion`-specific (U) layer the `dunion` work routed
  around.
- **`Opaque.lean`** (8) — depth-recursion scaffolding, incl. `traverse_congr` and the
  `opaq_p_*L` leaf family.
- **Scattered** (7) — `Codec.lean`, `Continuity.lean`, `Denoteω.lean`, and three per-leaf
  lawfulness lemmas in `Soundness.lean` the fueled theorem now subsumes.

Each needs deletion-plus-build to confirm: reachability via `@[simp]`, typeclass resolution
and `decide`/`omega` is not statically decidable. `Equations.lean`'s ~35 equation-table rows
and the numeral exhibits in `HeldSet.lean`/`Domain.lean` came back as candidates and are
**documented results — do not delete.**

### 4.2 Scaffolding

- **Exactly 3 `set_option maxHeartbeats`**, as expected. One justified by an adjacent
  docstring, one weakly (points at the first by analogy), one with none (queue item 11).
- **0 `sorry`, 0 `admit`, 0 commented-out code.** All 25 `admit` greps are prose.
- **2 `attribute [local simp]` blocks in `Opaque.lean`, byte-identical, 160 lines apart** —
  nothing stale, but one shared section would do.
- **52 bare `simp` in `Finset`-touching proofs — and the premise of that check does not hold
  here, which is good news.** `#assert_axioms_all` walks the namespace and fails the build if
  any constant exceeds the sanctioned axioms, so a bare `simp` routing through
  `Classical.choice` is a **build error, not a silent widening**. The residual risk is
  fragility under a mathlib bump, not unsoundness.

## 5. Prior art

The most consequential scan. Summary: **the domain is novel, the machinery mostly is not.**

### 5.1 Closest work

1. **PulseParse / EverCBOR / EverCDDL** — Ramananandro, Ebner, Martínez, Swamy, [arXiv
   2505.17335](https://arxiv.org/abs/2505.17335) (2025). *The closest existing artifact.* CBOR
   is a tagged coproduct with maps, arrays and byte strings plus a deterministic fragment;
   they prove that fragment non-malleable, formalize the CDDL schema language, and — the part
   that matters — *"identify well-formedness conditions on CDDL definitions that ensure that
   they yield unambiguous, non-malleable formats"*, mechanically checked, then generate
   parsers **and** serializers. That is our (U) plus its dischargers, one year early.
2. **Narcissus** — Delaware, Suriyakarn, Pit-Claudel, Ye, Chlipala, ICFP 2019.
   [ACM](https://dl.acm.org/doi/10.1145/3341686) · [preprint](https://arxiv.org/pdf/1803.04870).
   A format is a **relation**, not a function pair — see §5.4.
3. **EverParse / LowParse** — USENIX Security 2019.
   [paper](https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud).
   Laws: safety, inverse-ness, and **non-malleability**.
4. **A Verified Protocol Buffer Compiler** — Ye & Delaware, CPP 2019.
   [ACM](https://dl.acm.org/doi/10.1145/3293880.3294105). Confronts "the same source data can
   be encoded in infinitely many ways" — a direct hit on our `η`.
5. Ancestry: Kennedy, *Pickler Combinators* (JFP 2004) is our combinator inventory minus the
   proofs; Rendel & Ostermann, *Invertible Syntax Descriptions* (2010); Danielsson, *Every Bit
   Counts* (JFP 2012); Tan & Morrisett, *Bidirectional Grammars for Machine Code* (JAR 2017),
   explicitly partial both ways; Zaliva et al., *Verified ASN.1 stack* — where formalizing
   revealed the **standard** was wrong (DER booleans admit several encodings), precedent for
   measuring `η` against a real table.

### 5.2 What to call `(T, μ, e, p)`

Not a lens — `p` does not take the old source, so PutPut is not merely unproved but
meaningless, and asking for it is the first thing a reader will do. Not a Galois connection —
no order on values, and (C) is a definedness side condition, not an adjunction. A **prism** is
the right intuition and the wrong laws (a prism's `build` is total). The accurate name is a
**partial embedding–projection pair**: (R) is `p ∘ e = id` on `T`, and (MP) is the `e ∘ p ⊑ id`
direction with the domain order replaced by "agrees with". Shortest honest sentence: *partial
isomorphisms relaxed to hold only up to store normalization on the attribute side.* (C) as a
definedness condition is standard — Narcissus states encoder correctness the same way.

### 5.3 (U) is reinvention

Named at least four ways: **unambiguity / non-malleability** (EverCDDL, LowParse); **unique
decodability** (Danielsson states our attribute half verbatim); **disjointness for untagged
union elimination** — a live line: Rehman, Huang, Xie, Oliveira, *Union Types with Disjoint
Switches*, ECOOP 2022 ([PDF](https://xnning.github.io/papers/ecoop22switches.pdf)), and Backes,
Hriţcu, Maffei (J. Comp. Security 2014) on **static reasoning about type disjointness with
refinement predicates** — which is our shared-base-refinement discharger; and **predict-set
disjointness** on the parsing side. The concept has a name; take *unambiguity*, with
disjointness as the discharge technique. What was *not* found is a packaged decidable family of
dischargers for a document-store attribute domain — engineering novelty, not conceptual.

### 5.4 The exactness apparatus

Two halves with different answers. **"Exact, not merely sound" is known**: this is
completeness in abstract interpretation — Cousot, *Completeness in Static Analysis by Abstract
Interpretation* ([arXiv 2211.09572](https://arxiv.org/abs/2211.09572)), whose framing
("completeness is usually forgone from the start") is our axis; and the modern refinement,
**local completeness** (Bruni, Giacobazzi, Gori, Ranzato), is precisely "complete on the parts
that matter, and here is the exact place it is not". Two `Bool`s over-approximating
`dom e`/`dom p`, exact on 16 of 23 forms, is a *locally complete* analysis. Cite it or a
reviewer will. **The witnessed escape hatch: no prior art found** — claim it, framed as
*locally complete domain analysis with certified incompleteness witnesses*, and do not oversell
it; it is proof engineering, not new science.

### 5.5 DynamoDB — this heading is empty, and that is the strongest claim

All AWS formal-methods output is protocol or policy, never the data type mapping: the
DynamoDB ATC'22 paper (TLA+ on **replication**), Newcombe et al. CACM 2015, the S3 ShardStore
SOSP'21 paper (crash consistency), Physalia NSDI'20, Cedar (Dafny model of an authorizer).
Nobody has formalized DynamoDB's attribute domain, or any document store's data type mapping.
Adjacent but not prior art: *Foundations of JSON Schema* (WWW 2016) and the NoSQL
schema-inference literature are validation semantics, not proved codecs.

### 5.6 Criticisms worth acting on

Requested explicitly, and the sharpest ones continue this session's own arc:

1. **(W) wants to be a type index, not a law.** If `Codec` were indexed by its stored member —
   `Codec μ` — (W) is discharged structurally for every combinator and vanishes as an
   obligation. This is exactly the side-conditions-into-types move, applied to the one law it
   was not applied to.
2. **(U) wants to be a field, not a hypothesis.** If a discharger *value* sat in the `union`
   constructor, the arc completes there too. The λ_u experience is that untagged unions with
   overlap are a pit and the fix is to make disjointness a typing requirement.
3. **The exactness apparatus may be a symptom.** We need a decidable over-approximation of
   `dom e` *because* `e` is partial on `T`. If `T` carried enough structure that encode were
   **total** on it — precisely what the five repairs did for unorderedness, key-uniqueness,
   non-emptiness and numeral well-formedness — then `Adm` on the value side and its exactness
   theorems would be unnecessary. Worth asking honestly how many of the 7 non-exact forms are
   non-exact because *the value type is still too loose*. If most are, the right move is to
   keep the apparatus only on the attribute side, where partiality is forced by the medium.
4. **A relational format would collapse three laws into two.** With `fmt : V → Set 𝔸`
   (Narcissus), normalization becomes part of the *specification*: "decode inverts `fmt`" and
   "encode refines `fmt`" replace (R)+(C)+(MP), and `η` stops being a separate relation
   compared against `ker p`. Leading refactor candidate.
5. **Hand-written combinators with hand-proved laws is what Narcissus exists to argue
   against**, and ~700 theorems for 23 term forms is evidence for their position, not ours.
6. **The escape hatch has no bound.** It prevents silent widening but not loud widening, and
   nothing stops it reaching 23 excuses and a vacuous claim. Consider a theorem about the
   excuse set itself.
7. **The axiom guard is hygiene, not novelty** — and note our own record that `omega` can pull
   `Classical.choice`, which is why it is load-bearing.

### 5.7 To adopt

**Differential testing against the shipped TypeScript**, the way Cedar and ShardStore do it:
generate random terms and values from the deep embedding, run the Lean-evaluated reference and
the TS implementation, diff. This is the realistic answer to certifying the port — extraction
to TypeScript is not credible. **QuickChick-style derived generators** with soundness *and*
completeness proofs against an inductive relation would turn `Adm`/`AdmA` into a test oracle
for free and feed the above. **Read next:** arXiv 2505.17335, then Narcissus §3–4.

## 6. Carrier refinements: the axis is closed

**Zero defects.** The authoritative list is C1's own table at `codec-formalization.md:1871-1876`
— exactly four members carry a refinement, `N` (grammar / 38 digits / magnitude) and
`SS`/`NS`/`BS` (non-empty), and **all four are now enforced**. Every remaining constraint in
`dynamo-datatypes.md` is either a resource limit §1 deliberately omits or a schema-position
limit about tables, indexes and keys that the model does not have.

| ref | constraint | verdict |
| --- | --- | --- |
| `:27` | attribute names ≥1 char, <64 KB | **OUT-OF-SCOPE-BY-SPEC.** §1's `M` row is `Name ⇀fin 𝔸` with no refinement and C1's table omits `M`. The non-emptiness half *is* kernel-admissible (`{s : String // s ≠ ""}`), but `Name` is a collection element type and function domain, not the carrier of a non-recursive field in the `Attr.n` sense — coercions and instances at ~35 map sites in the largest file, for no spec mandate. Highest cost of any candidate. **Not worth doing.** |
| `:80`, `:103` | string/binary min length zero *"unless a key"* | **NOT-TYPEABLE.** A contextual permission; a subtype cannot express "unless it is a key" without a key concept the model lacks. Would also cost a witness (`Refutations.lean:203` uses `.str ""`). |
| `:83-84`, `:106-107` | partition key ≤2048 B, sort key ≤1024 B | **OUT-OF-SCOPE**, un-typeable in principle — constrains a position in a table schema, not membership in `𝔸`. |
| `:132`, `:185` | item size ≤400 KB | **NOT-TYPEABLE.** A global aggregate over the recursive structure; enforcing it refines `Attr.l`'s list and `Attr.m`'s function — the recursive occurrence, which the kernel rejects. A subtype on `Item` alone is admissible and vacuous. |
| `:130` | nesting ≤32 levels | **NOT-TYPEABLE, and typing it would destroy live theorems.** `{as : List Attr // Attr.depthL as ≤ 31}` nests `Attr` under its own declaration. Worse: the ω-codecs' totality argument *depends on depth being unbounded* — `Opaque.lean:19,27` and `Discharge.lean:222,1120,1371` state it by giving each input its own budget. A 32-cap makes that argument trivial or ill-typed. **The one candidate that is actively destructive.** |
| `:63-65` | ≤38 significant digits, magnitude range | **ALREADY ENFORCED** — `WFNumeral`. |
| `:134`, `:183`, `:187` | sets non-empty, unique, unordered, homogeneous | **ALREADY ENFORCED** — `NEFinset`. |
| `:20-39` | table/index names, reserved words, `#`/`:` | **OUT-OF-SCOPE** — no table, index or expression language in the calculus. |

**Sharpened rule.** The `WFNumeral` move generalises to *concrete, non-recursive field
carriers* only. Depth and item size are the canonical inadmissible case: they refine the
recursive occurrence itself, and no restatement turns them into a subtype. The reference's
size limits are resource limits and §1 excludes them on purpose — treating them as `𝔸`
membership would itself be the defect.

## 7. The exactness hatch: one promotion, one wrong reason

Ranked most to least retirable. Static reading only, so the promotion is *"looks provable,
record-shaped"*, not checked.

**`nameAdmission` — the object half looks promotable.** The excuse survives (its `tuple`
witness `not_ExactV_tuple` still holds), but `ExactV (.object …)` now looks provable. Object
encode demands exactly two things (`objectCodecCore_e_inv`): `valPresentB sems keys = true`,
and `funImage (fun k => (entryCodec …).bind (·.e (f k))) = some g`. Both are decidable over a
`Finset Name` plus a function — *exactly* the shape of the `record` row that was already
repaired, which closes via `funImage_isSome_iff`. Crucially the `fb` stand-ins
(`fbNames`/`fbValue`) and `keepB` live only in `objRead`, so they constrain `p`, not `e`; on
the write side `valPresentAt` treats `.fb` like `.req` and is a plain `decide`. To land it:
rewrite `Adm`'s `.object` row, fill the `.object` case of `Adm_exact`, flip `Analysable`, and
**delete the `nameAdmission → .object` row from `Excuse.covers`** or `excuse_shapes` and
`analysable_excused` break. The attribute side stays excused.

**`payloadShape` — the stated reason is now wrong; the excuse survives for two different
reasons.** It says *"`asWireSet` demands payload homogeneity: a fact about attributes, not
values"*. Homogeneity of values and non-emptiness are structural now, so that sentence is
stale. `not_ExactV_set` still holds, and it is not about homogeneity at all: `collapse` sends
both elements to one string, so both admit while `setImage`'s `Nodup` check refuses. The two
real obstructions, neither visible to any `Bool` on terms:

1. **Collision.** `setImage` requires the images be `Nodup`; element-wise admission cannot see
   a collision *between* two elements.
2. **Wire-kind agreement.** `encSet` picks one kind by trying `sC`, then `nC`, then `bC` for
   *all* elements. A `.custom` codec may send different `.str` inputs to different `Attr`
   constructors, so all three passes fail while every element individually writes. This is the
   surviving residue of the old "homogeneity" reason — genuinely about attributes, but stated
   as if it were the whole story when the witness proves otherwise.

Correct reason: *a set codec must write its elements to **distinct** payloads of a **single**
wire kind; element-wise admission sees neither the collision nor the kind disagreement.* Fix
at `Exactness.lean:281-282` and in `Analysable`'s bullet list; `Adm`'s `.set` comment is
already right, and `not_ExactV_set`'s own docstring already states the corrected reason.

**`opaqueDepth`, `uniqueAdmission`, `nullOwnership`, `valueUnderRead` — reasons accurate,
witnesses hold, not retirable.** Two imprecisions worth fixing:

- `not_ExactV_opaq`'s docstring — **my own sentence** — claims that after the set repair the
  numeral gate is "the only place" `⊤` over-claims. But the constructor's named reason is
  *depth recursion*, and what the witness exhibits is the *`refuse` policy* having no number
  option. Those are two different over-claims; the witness is a policy witness, not a depth
  witness.
- Pre-existing, not from this batch: `Excuse.covers` files `.dunion` under `uniqueAdmission`,
  while `Analysable`'s bullet gives `dunion` a *different* reason ("the tag is checked, the
  matched option's own admission is not").

**Net for `Analysable`/`AnalysableA`:** exactly one promotion available, `.object` on the value
side. `AnalysableA` gets none — the object read still goes through `fbNames`/`fbValue`/`keepB`.

## 9. TypeScript conformance — five live bugs

The model exists to certify `src/`. The five tightenings were used as a checklist against it.
`src/codec.ts` (4023 lines) is the library, `src/attribute.ts` the domain, `src/native.ts` the
AWS-SDK-compatible marshaller.

### 9.1 Correspondence (C2/C3) — total, with two holes

The mapping is already tabulated at `codec-formalization.md:1929-1981`: 24 `CodecDef['kind']`s
against 22 `Term` constructors, stratified `TermDef`/`FieldDef`/`RestDef` with a type-level
assertion that fails the build on an unclassified kind. Checked term by term against
`Term.lean:21-71` — **all present**.

- **GAP** — `literal<const T extends string | number>` (`codec.ts:871`). Lean's arity-one
  `literal` takes any `Value`, so `literal (Value.bool true)`, `literal Value.null` and
  `literal (Value.bytes …)` are model terms with no TS constructor.
- **GAP, still open** — `native` files itself under `def: { kind: 'opaque' }`, so the C3 table
  counts it as `.opaq`. **It is not the same pair**: it writes `NS`, reads `NS`, and honours
  `convertEmptyValues`, none of which `opaque`'s `(T, μ, e, p)` does. One kind, two different
  codecs — and **every bug below hid in the half the table does not describe.** The four C1
  violations are fixed, so the two pairs no longer disagree about what an `N` *carries*; they
  still disagree about everything else, and the table still describes only one of them.

### 9.2 The five tightenings

| # | tightening | verdict |
| --- | --- | --- |
| 1 | `M` unordered, unique-keyed | **OK** — `record`/`object` walk key-by-key; a JS object cannot carry a duplicate and no branch reads enumeration order. |
| 2 | object field tables a set | **OK** — `spec` is a `Record<string, AnyCodec>` flattened once; keys unique by construction. |
| 3 | sets non-empty by type | **OK** in `codec.ts` (all four refuse, and the comment names (C) as the reason). ~~**BUG** in `native.ts`~~ — **fixed**: all three of `SS`/`NS`/`BS` now refuse an empty stored set on read, through one `nonEmpty` helper carrying the (C) argument. |
| 4 | literal alternatives non-empty, repeat-free | ~~**BUG**~~ — non-emptiness **fixed**, see 9.3. Repeat-freedom is still not checked. |
| 5 | `Numeral.WF` on both halves | **OK** in `codec.ts` — `isNumeral` at `992-1006` explicitly cites `Numeral.WF`; both halves gated for `number` for `number`, `decimal`, numeric `literal` and `opaque`. **§4's two named defects are closed there.** ~~**BUG** in `native.ts`~~ — **fixed**, see 9.4. |

### 9.3 ~~`literal()` with no alternatives admits everything~~ — fixed

`codec.ts:874-879` takes `...allowed: readonly T[]`, so **zero** arguments typecheck; and
`admits` at `937-942` is `allowed.length && !allowed.includes(...)`, whose short-circuit makes
an empty `allowed` admit **every** value. So `literal()` compiles and is a codec that encodes
any string as `S` and decodes any `S`. The model has no such term — that is exactly what
`NEFinset` now forbids — so the construction has no denotation, *and* it is silently the wrong
codec: the caller asked for an enum and got `string`.

Also **GAP**: no repeated-alternative check, so `literal('a','a')` is accepted where the
model's `NEFinset` cannot express it. Semantically benign, but C3's "the constructor denotes
this term" stops being injective.

The rest of the family is right: mixed-kind refusal, `ℓ ⊆ D` at construction, a genuine
read-side numeral gate.

**Fixed** by a construction-time `CodecError` beside the other two refusals, and by deleting the
`allowed.length &&` guard rather than correcting it — a truthiness guard in front of a membership
test *inverts* the test exactly when the set is empty, where `∀ x. x ∉ ∅` should refuse
everything. Not a type, and the reason is worth recording: `literal(...Object.values(Status))` is
an honest call that spreads a plain array, which a `(first, ...rest)` signature refuses. The type
cannot carry `ℓ ≠ ∅` without breaking the caller who most wants it, so the construction site
does. The repeated-alternative GAP is untouched.

### 9.4 ~~`native.ts` — four C1 violations~~ — all four fixed

- **`native.ts:78-95`** gates the write on `Number.isFinite` plus `MAX_SAFE_INTEGER`, then
  `carrying('N', value.toString())`. `5e-324` is finite and inside the safe range, so it
  **writes `⟨N, "5e-324"⟩`** — outside `Numerals`. This is precisely the defect §4 records
  `opaque` having had, one file over, still live.
- **`native.ts:226-230`** `fromNativeNumber` is `Number(digits)` with no `isNumeral`. So
  **`{N:''}` reads as `0`** — §4's other named defect, still reachable in this repo through
  `native`. Also `{N:'0x10'}` → `16`, and `{N:'abc'}` → `NaN` returned.
- **`native.ts:265-269`** `NS` decode maps `fromNativeNumber` with neither a numeral check nor
  an emptiness check: `{NS:[]}` and `{NS:['abc']}` both decode.
- **`native.ts:270-271`** as in 9.2 row 3.

**Fixed, and it is a deliberate divergence from the SDK rather than a repair of the port.**
`convertToAttr` checks a finite double on the way in and `convertToNative` checks *nothing* on
the way out; `Carries('N')` is neither. So the port now gates both halves on `isNumeral` and
refuses the three empty stored sets, which means it refuses four things the real SDK accepts —
each one an attribute DynamoDB itself rejects or never wrote. `native.spec.ts` records this as a
`describe` that asserts **both** sides: that the SDK really does the permissive thing, and that
this refuses it. `native.Deviations` (`readNumber`/`writeNumber`) is the way back for a team
migrating a table that already holds such rows, and there is a test that it reproduces the SDK
byte for byte.

One gate suffices on `native`'s read side where `number` needs two: `number`'s second gate
catches a stored numeral that rounds *out* of range on the way into a double, and this reader
hands a wide value back as a `bigint` of the very digits stored, a narrow one from inside the
safe range. Nothing it returns can fail to be writable again.

### 9.5 The C1 embedding verifies — but §5's term list is incomplete

`AttributeValue = ExactlyOne<AttributeCarries>` (`attribute.ts:21-45`) is the unrefined host
`𝔸`. The inhabitants with no image in the model's `𝔸` are exactly:

1. `{N: s}` for `s` failing the grammar, 38 digits, or magnitude — `{N:''}`, `{N:'NaN'}`,
   `{N:'0x10'}`, `{N:'5e-324'}`, `{N:'1e400'}`;
2. `{SS: []}`; 3. `{NS: []}` and `{NS: [s,…]}` with any `s` failing (1); 4. `{BS: []}`.

That is the whole surface, and it is closed because `AttributeCarries` has exactly ten keys and
the other six carry host types the model carries unrefined. **§5's claim that the list is short
and closed verifies.** What does not verify is §5's *term* list: it names `decimal`, `number`,
`literal`, `set`, `opaque` as the terms touching a refined member — and omits `native`, which
touches `N` on both sides, `SS`/`BS` on the read side and `NS` on both, and gated none of them.
It gates all of them now; the list is still wrong, and that is §9.6's remaining item.

### 9.6 Fixes, in order

1. ~~**Route `native.ts`'s number write and read through `codec.ts`'s `isNumeral`, and add the
   emptiness check to its `SS`/`BS`/`NS` decode.**~~ **Landed** — though not by routing through
   `codec.ts`; see §9.7.
2. ~~Make `literal()`'s empty case a `CodecError`, beside the mixed-kind refusal.~~ **Landed.**
3. **Open.** Add `native` to §5's term list, or give it its own term and stop filing it as
   `opaque`. The second is the honest one and it is a model change, not a `src/` change: `native`
   is a fourth pair over `unknown` whose `μ` is nine members wide, and the C3 table currently
   claims `opaque`'s row describes it. §9.1's surviving GAP is the same item.

### 9.7 Where `Carries('N')` lives now

`isNumeral` and `isStoredNumeral` moved from `codec.ts` into `attribute.ts`, exported. §9.6's
first item was written as "route `native` through `codec.ts`'s `isNumeral`", and that is the
wrong direction: `native.ts` is a sibling entry point, deliberately dependency-free, and it
should not import a codec module to learn what an attribute carries.

The predicate is not a property of any codec. It is `Carries('N')` — a property of the *carrier*,
which is what the `Attr.n : WFNumeral` change made exact on the Lean side. `attribute.ts` is the
unrefined host `𝔸` (§9.5), so it is where the refinement belongs, and `codec.ts` and `native.ts`
now import the same one. That is why one file's fix closed four bugs in another: before, there
were two answers to "what does an `N` carry", and only one of them was written down.

The cost is that `isNumeral` is public API (`Rotorise.ts` re-exports `./attribute`). That is
defensible — a caller checking a string before a write is asking a real question — but it was not
a decision the fix needed, and it can be walked back with an internal module if it becomes one.

## 10. EverCDDL, read

Read from the arXiv HTML (§2 PulseParse, §3 EverCBOR, §4 EverCDDL). Quotes are from that
text; where a gloss is inference rather than the paper's own words it is marked.

### 10.1 Their (U) is the *definedness of a compilation pass*, not a premise

**Theorem 4.4.** *"Given a CDDL type `t`, if `elab(t)` is defined, and `p` is the parser
specification associated with `t`, then `p` is injective."*

That is our (U), and the factoring is better than ours. They do not carry a side condition on
the rule and then supply dischargers; they run an **elaborator**, a partial function on
schemas, and *its definedness is the well-formedness check*. `EverCDDL` is "a tool that checks
that a CDDL definition is well-formed, and then produces verified parsers and serializers for
it" — so the user never discharges anything. Theorem 4.3 is the bridge: the elaborated type
has "equivalent validation semantics to the original".

This sharpens the criticism in §5.6.2. (U) does not merely want to be a *field* of the `union`
constructor; it wants to be the **output of a checker** — an `elab : Term → Option Term'` whose
definedness implies the property, with our existing dischargers as its cases. `UAtAct` in
`Obligations` becomes `elab t = some t'` and stops being a semantic obligation the caller
proves.

### 10.2 Their serializer's *type* carries the round trip — this is (R) as a type

```
serializer p = (x: t) → (b: seq U8.t { p b == Some (x, length b) })
```

The refinement is in the codomain, so **(R) holds by construction and is not a law**. Our
analogue is available and constructible, because a Lean structure field may mention an earlier
one:

```lean
structure Codec where
  p : Attr → Option Value
  e : (v : Value) → Option {a : Attr // p a = some v}   -- (R) is the type
```

That would make (R) — the *first* law, not a side condition — structural for every combinator,
which is the largest remaining instance of this session's move. **But it is not obviously
right, and the tension is worth stating rather than resolving:** it fuses definitions with
proofs, so each combinator's `e` produces the retract witness inline instead of once in
`lawfulCore_*`; `Codec.Equiv`, `Codec.Approx` and the `Continuity` results all compare `e`s
whose types would now differ; and Narcissus deliberately went the *other* way, separating a
relational spec from its correctness. It is the same work relocated, and readability is the
thing being traded. Worth a spike, not a commitment.

### 10.3 Non-malleability: they prove it, we deliberately fail it — and `ker p` is the measure

Their property, §2.1: *"if `p(b1) = Some (v, n1)` and `p(b2) = Some (v, n2)` … then `n1 = n2`
and `b1` and `b2` coincide on their first `n1` bytes"* — two inputs decoding to one value must
be equal.

Our analogue would be: `p a₁ = some v → p a₂ = some v → a₁ ≈ a₂`. **We do not have this theorem
and should not: our `ker p` is deliberately not equality**, and §2's two surviving reasons —
`η` normalising an `N`, `drop` discarding names — are exactly its failures. Their CBOR result
holds only of the *deterministic fragment*; DynamoDB has no deterministic fragment, because the
store itself rewrites numerals.

So the honest move is to name the property in their vocabulary and state where it fails:
`SurvivesStore` (`η ⊆ ker p`) is precisely the condition under which the failure is harmless,
and `ker_decimalCodec` / `not_survivesStore_decimalWF` are already the two halves. This costs
nothing and buys legibility to the verified-formats community.

### 10.4 EverCBOR keeps the representation we abandoned — and is right to

Their raw map type, §3.2:

```
Map: (len: raw_u64) → (v: nlist (raw_data & raw_data) len.value) → raw_data
```

A **list of pairs with "no duplicate checking in raw form"**, with key uniqueness as a `valid`
predicate (§3.3: "no two entries have equivalent map keys"), plus **Theorem 3.2**, a
lexicographic byte order on keys, because deterministic CBOR sorts map entries.

That is the representation this arc spent five sites removing, plus the canonical order
`WireOrder.lean` was built for. **The reason they need it and we do not is the layer**: their
`raw_data` models *bytes before parsing*, which genuinely is an ordered sequence that can
repeat a key. DynamoDB's `𝔸` is *post-parse* — the SDK hands over a map, not a byte string —
so our carrier can be exact and no order is forced.

This retro-justifies the arc and simultaneously explains why `WireOrder.lean` is dead (§1 item
4): the module was importing a wire-level obligation into an API-level domain. **The design
axis is whether the domain is the wire or the API**, not whether typing is better than gating.
Worth recording, because it is the answer to "why does the closest prior art not do what we
just did".

### 10.5 Three of their four well-formedness conditions we get free

| their condition (§4.1, Thms 4.1–4.4) | ours |
| --- | --- |
| "all alternatives must be disjoint" (map-group choice) | **(U)** — the one that survives |
| Kleene star: "if `∗a1,∗a2,a3` appears, then `a1` and `a2` must be disjoint and `a1` and `a3` must be disjoint" | free — our `tuple` + tail assigns **positionally** via `align`; there is no boundary to locate |
| map concatenation: "if `g1,g2` appears, then the footprints of `g1` and `g2` must be disjoint" | free — `object` + `rest` dispatches on `k ∈ keys` via `entryCodec`, so the declared and open groups are disjoint by construction |
| "deterministic map form" `g ::= ℓ ⇒ t \| ℓ : t \| ∗(tk ⇒ tv) \| g1 // g2 \| ?g \| g1,g2` | n/a — no group grammar; the field table *is* a `MapOf FieldSem` |

**This reduces the reinvention claim in §5.3.** Three of the four are *ambiguity conditions
forced by having to find boundaries in a byte stream*. Only the choice condition is
domain-independent, and that is the one we have. Our (U) is not "EverCDDL's well-formedness
conditions, rediscovered"; it is the single condition of theirs that survives the change of
layer — and the other three being discharged by our representation is a point in the
representation's favour.

### 10.6 One caveat on the extraction

The gloss *"this implies the elaborated parser's domain is exactly the set of valid CBOR items
for that type"* attached to Theorem 4.4 was the extraction's inference, not a quoted theorem.
Injectivity is not exactness of a domain, so **the §5.4 conclusion stands as written**: the
"exact, not merely sound" domain result is still ours, and the reference for it is local
completeness in Cousot's sense, not this paper. Confirm against the PDF before citing.
