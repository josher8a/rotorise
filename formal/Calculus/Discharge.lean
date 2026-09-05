import Calculus.Soundness

/-!
# §5 — The decidable dischargers of (U)

The machinery of (K): `κ`, `ident`, `adm` and `admA` as total structural recursions over the
term language, exactly as §5's tables state them — `Kind` is §1's and lives in `Domain.lean`,
which this paragraph had among the recursions.

**The per-aspect separation layer this file used to carry is gone.** `SepV`, `SepA`, their
footprint definitions and the discharger stated on them — the combined theorem and its
kind/member half — were retired once the walk showed nothing outside this file and
`Refutations.lean` depended on them, and once `Orthogonality.lean`'s `uAtCan_of_separates`
turned out to state the same discharge on what `select` actually consults. What that layer
proved by hand in phases *slot* and *alternatives*, `Orth` reaches by `decide`; those hand
proofs went with it. The tables above stay: §5 specifies them, and the exact generation still
depends on them through `Adm_le_adm` and `AdmA_le_admA`.

What is left here is the four tables, their row lemmas, and the discharges no phase of the
classifier reaches — the ones whose premise is an arbitrary `q` inside a `refine`, and
`uAtAct_array_literals`, which holds where `UAtCan` is outright false.

§5's (D) is *not* among these, and `not_uAtCan_literal_held` is why: held sets are sets
of values, (U)'s readable side quantifies over attributes, and `held`'s adapter relabels
between them. Two options can hold disjoint sets and read one attribute. (D) is a
well-formedness condition on the `T` index and lives there — `DIncomp`, a premise of
`Typed.union` (Typing.lean); the readable side is decided on stored attributes. `DDisj`
below is the *stronger* reading §5 considered and withdrew, kept only to be refuted.

The `ident` exemption is here in its repaired form. An earlier §5 stated (K) as
`κ(cᵢ) ∩ κ(cⱼ) = ∅ ∨ ident(cᵢ) ∨ ident(cⱼ)` and called it sufficient for (U); it is
not, on either disjunct, and the two counterexamples at the foot of this file are
machine-checked. What carries the exemption is `adm` — the set an `ident` term checks
against — disjoint on *both* sides, which is what §5's worked example,
`union(literal("A"), literal("B"))`, actually has. That pair is discharged in
`Orthogonality.lean` now, by `separates_literal_disjoint` and the phase built on it.
-/

namespace Calculus

/-! ## `κ` — the kinds a term accepts

    `Kind` itself is §1 vocabulary and lives in `Domain.lean`, on both sides of the
    pair (`Value.kind`, `Attr.kind`). What is §5's is `κ`: which of those kinds a
    *term* accepts. -/

mutual

/-- §5's `κ`: the kinds of value a term accepts. `none` is the table's `⊤`, and it
    absorbs — `nullable`'s `∪` and `union`'s `⋃` answer `⊤` whenever a subterm does. -/
def κ : Term → Option (List Kind)
  -- §3 `(literal)`: the kind is the base's, which is the index.
  | .literal k _ => some [k.kind]
  | .string | .decimal => some [.string]
  | .number => some [.number]
  | .boolean => some [.boolean]
  | .null => some [.null]
  | .binary => some [.binary]
  | .set _ => some [.set]
  | .array _ | .tuple _ _ => some [.array]
  | .record _ | .object _ | .dunion _ _ => some [.map]
  | .refine t _ | .legacy t _ => κ t
  | .nullable t => (κ t).map (.null :: ·)
  | .union opts => κList opts
  -- `lazy` is the *most* transparent wrapper in the language, not an opaque one:
  -- `denote (.lazy t) = { denote t with μ := none }`, so `e` and `p` are the
  -- subterm's definitionally and only the member is erased. §5 calls it unanalysable
  -- because the doc's thunk was `Unit → Term`; this `Term` is not that thunk, and the
  -- opacity was the residue of that change rather than a fact about `lazy`.
  | .lazy t => κ t
  | .held _ _ _ | .custom _ _ | .opaq _ => none

/-- `⋃ κ(cᵢ)`, `⊤`-absorbing. -/
def κList : List Term → Option (List Kind)
  | [] => some []
  | t :: ts =>
    match κ t, κList ts with
    | some ks, some ks' => some (ks ++ ks')
    | _, _ => none

end

/-- Whether a set's **base** decides its own membership — what `ident` used to read off the
    element term. `number` and `decimal` check §1's gate on the way in and on the way out, so
    an attempted admission is evidence; `string` and `binary` accept their whole carrier and
    so decide nothing. Indexing `set` turns a propagation into this table, and the four
    answers are the four the propagation gave. -/
def SetBase.ident : SetBase → Bool
  | .string | .binary => false
  | .number | .decimal => true

mutual

/-- §5's `ident`: the term decides its own membership — attempted admission is
    evidence. Holds of `literal` and `dunion`; propagates through the containers and
    the transparent wrappers; never otherwise (`nullable` deliberately: two nullable
    options both admit the null neither subterm decides). -/
def ident : Term → Bool
  | .dunion _ _ => true
  -- `number` and `decimal` decide their own membership: each checks §1's gate on the way
  -- in and on the way out (§3 `(number)` "gates both halves"). The other four ground
  -- scalars accept their whole carrier and so decide nothing.
  | .number | .decimal => true
  -- `(literal)` checks its one value on both halves — the definition of deciding your
  -- own membership, and the reason the constructor is worth having over `refine`.
  | .literal _ _ => true
  -- `nullable` propagates rather than refusing. §5 made it refuse outright, to stop two
  -- nullable options separating on a null neither subterm decides — but with `adm` precise
  -- that refusal is carried by the sets *overlapping at null*, which is the honest reason.
  | .nullable t => ident t
  | .set b => b.ident
  | .array t | .record t => ident t
  -- `refine` *holds* it rather than propagating: `q` is checked on the way in and on the
  -- way out, which is what deciding your own membership means. §3 argues the same — a `p`
  -- returning the value it read without verifying `q` would break (C).
  | .refine _ _ => true
  | .legacy t _ => ident t
  | .tuple ts tail =>
    identList ts && (match tail with | some t => ident t | none => true)
  | .union opts => identList opts
  -- The remaining rows are `false`, and are written out because a row that decides
  -- nothing is a claim like any other. The four ground scalars accept their whole
  -- carrier, so an admission is no evidence about which term admitted.
  | .string | .boolean | .binary | .null => false
  -- `object` is the one container that does not propagate: its admission tests *names*,
  -- and the field terms' own sets are not what the option checks a value against.
  | .object _ => false
  -- `lazy` propagates, for the reason given at `κ`: its pair *is* the subterm's.
  | .lazy t => ident t
  -- `held` propagates: `adm` applies `f` and asks the subterm, so the subterm is what
  -- decides, exactly as it does under `refine`.
  | .held t _ _ => ident t
  -- `custom` decides its own membership outright — its `T` *is* `dom(ce)`.
  | .custom _ _ => true
  -- `opaq` decides its own membership for the same reason `custom` does, and the rows
  -- below are why: `adm (.opaq _)` **is** `dom((opaqCodecω _).e)`, so an admission is an
  -- answer from the codec rather than a syntactic guess. The old row was `!lossy`, forced
  -- by `ident_of_adm` when a scalar-prefix row refused only at `.num`; the semantic row
  -- refuses far more (a `numSet`, an array holding a numeral the store will not take),
  -- and at *every* policy — `Numeral.WF (Double.toDec d)` is not a theorem — so `!lossy`
  -- is no longer sound and `true` is what `ident_of_adm` now forces.
  | .opaq _ => true

def identList : List Term → Bool
  | [] => true
  | t :: ts => ident t && identList ts

end

/-! ## `adm` — the sets an `ident` term checks against

    §5's third auxiliary, and the specification now states it as the two functions below
    rather than as one: its table is term-by-term and matches these definitions clause for
    clause, so a reviewer can read the two side by side. `ident` says a term decides its own
    membership; `adm` says *against what*. Only two terms carry a real set — a `literal`'s values and a
    `discriminatedUnion`'s tags — and `refine`/`legacy` pass one through. Everywhere
    else `adm` is `true`: **no information**, which is what makes two such options
    never separable this way.

    In particular `adm` does *not* propagate through the containers, though `ident`
    does. `adm(array(c))` would have to contain the empty array whatever `c` is, so
    propagating it would claim a separation that is false — see
    `not_uAtCan_array_literals` below.

    ### The two rows that ask their own codec

    `custom` and `opaque` are the language's two escape hatches, and they are the two
    rows here that **do not describe a set at all**. Each one asks the codec it denotes:

        adm  (.custom ce _)   v = (ce v).isSome
        adm  (.opaq lossy)    v = ((opaqCodecω lossy).e v).isSome
        admA (.custom _ cp)   a = (cp a).isSome
        admA (.opaq lossy)    a = ((opaqCodecω lossy).p a).isSome

    Three things follow, and they are the same three for both.

    *They are exact by construction.* `denote`'s rows set `e := ce` and
    `e := (opaqCodecω lossy).e` — the `custom` row definitionally, `opaque` by
    `denote_opaq` — so the row and `dom(e)`
    are the same function and `ExactV`/`ExactA` at either term is `Iff.rfl`. That is not a
    sharp analysis of an escape hatch; it is the analysis *declining* to be one, and the
    exactness is the codec's, borrowed. `Exactness.lean` says so again where the two
    `Exact` rows are proved.

    *They are as precise as the semantics is.* No syntactic set could name
    `opaqCodecω`'s domain: it recurses on the *input's own depth*, refusing a `numSet` of
    numerals the store will not take, or an array with one such numeral at any depth. A
    row over the term cannot see past the top constructor — the row this one replaced saw
    exactly that far, which gave `number` a separation `set(number)` could not have for no
    reason in the semantics. Deferring sees all of it, because it does not look.

    *Nothing here knows anything about either implementation.* Swap `opaqCodecω` for a
    different `opaque` — a different numeric policy, a different set of options, a
    different fuel discipline — and every theorem downstream of these rows is still true
    and still proved, because none of them ever mentions what the codec answers. That is
    what `custom` has always had and what this buys `opaque`: the analysis is decoupled
    from the hatch. Precision is the consequence, not the goal.

    ### …and the one respect in which they are opposite

    The likeness is **the analysis, and only the analysis**. `opaque` is not a `custom`,
    and the difference is the warranty behind the codec each row asks:

    * `custom` carries a real premise. `Obligations (.custom ce cp)` (`Soundness.lean`) is
      `Lawful ⟨dom(ce), none, ce, cp⟩` — a proof obligation on whoever writes the term, and
      nothing in the calculus discharges it. The row asks a codec **the user warrants**.
    * `opaque` carries none. `Obligations (.opaq _) = True`, and it is `True` because the
      laws are *theorems* here: `lawful_opaqCodecω` and `carrier_opaqCodecω`
      (`Opaque.lean`), off the stabilization and depth-preservation lemmas. The row asks a
      codec **the calculus warrants**.

    So `opaque` is strictly the stronger of the two — same decoupling, no premise — and
    that is what "a *well-behaved* `custom`" means. A reading of these rows as "`opaque` is
    a `custom`" gets the obligation exactly backwards.

    The price is paid and worth naming. Neither row can be *read* to learn what the term
    admits — a reviewer wanting that reads the codec — and `admA` had to become
    `noncomputable`, which `adm` already was (`opaqCodecω` is, and `custom` carries
    arbitrary functions). Nothing in §5 evaluates these; every use is a proof. -/

/-- The tags a `(dunion)`'s options answer to, pooled. Spelled out rather than a
    `flatMap` so the membership lemma is one induction. -/
def allTags (d : Name) : List Term → Finset String
  | [] => ∅
  | t :: ts => tagsOf d t ∪ allTags d ts

theorem mem_allTags {d : Name} {ts : List Term} {t tag} (ht : t ∈ ts)
    (htag : tag ∈ tagsOf d t) : tag ∈ allTags d ts := by
  induction ts with
  | nil => exact absurd ht (by simp)
  | cons t₀ ts ih =>
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact Finset.mem_union.mpr (Or.inl htag)
    · exact Finset.mem_union.mpr (Or.inr (ih ht'))

/-- `admA`'s literal row: what the *stored attribute* tells you about `ℓ`.

    For every base but `number` the stored attribute **is** the value, so `ℓ` bounds the readable
    side outright in one `decide`. At `number` it does not — the numeral goes through
    `Double.ofDec` — and this row used to be `⊤` on that ground, which is what §5 called the
    `literal-S`/`literal-N` split. **The ground did not support the conclusion.** No syntactic
    set of attributes names the numerals that read into `ℓ`, and the row does not need one: it
    can *ask*, since `ofDec` is a function it may call and `denote (.literal .number ls)` is
    `literalCodec .number ls`. What survives of the split is that the numeric answer costs a
    `bind` through an axiom where the others cost a `decide` — a difference in how the row is
    computed, not in what it decides. With one rule that is a *case of the definition* rather
    than two constructors, which is the honest place for it: it was never a difference between
    two rules, only between two bases of one.

    Not `inL`'s mirror, and that asymmetry is the content: `adm` is `inL` exactly, because the
    write side sees the value. -/
noncomputable def admALit : (k : GroundKind) → NEFinset k.Carrier → Attr → Bool
  | .string,  ls, .s s    => decide (s ∈ ls.1)
  | .boolean, ls, .bool b => decide (b ∈ ls.1)
  | .binary,  ls, .b b    => decide (b ∈ ls.1)
  | .null,    _,  .null   => true
  -- **The row that used to be `⊤`, asking its codec instead.** The old justification was
  -- that `Double.ofDec` is axiomatized, so no syntactic set of *attributes* bounds which
  -- numerals a numeric literal reads. True, and beside the point: the row does not have to
  -- name the set, it can ask, and `denote (.literal .number ls)` **is**
  -- `literalCodec .number ls` (`rfl`), so this is `dom(p)` on the nose. What the analysis
  -- ever needed was not *which* numerals a stored text reads to but whether the answer is
  -- **unique**, and `Double.ofDec` being a function gives that for free — which is why
  -- disjoint alternative sets now separate in the table and not only in the pair; the
  -- discharge itself is `Orthogonality.lean`'s, through `separates_literal_disjoint`.
  | .number,  ls, a       => ((literalCodec .number ls).p a).isSome
  -- `decimal` asks for the same reason and gets a sharper answer. Its alternatives *are*
  -- stored numerals, so unlike `number` the row could in principle be spelled out — but
  -- asking keeps one definition of what the base reads instead of two that must agree, and
  -- a different `decimal` codec would need no edit here.
  | .decimal, ls, a       => ((literalCodec .decimal ls).p a).isSome
  | _, _, _ => false

mutual

/-- `adm`, value side. `noncomputable` only because the `literal` row at `number` compares
    `Double`s, whose
    `DecidableEq` is axiomatized (§1) — the recursion itself is structural. -/
noncomputable def adm : Term → Value → Bool
  -- **`inL`, the codec's own predicate** — where three rows used to spell it out twice for the
  -- n-ary bases and once more, case by case, for arity one. `adm` bounding the write is
  -- exactly what `Codec.restrict` restricts by, so there was never a second definition to
  -- give; there were three constructors making it look like there was.
  | .literal k ls => inL k ls
  -- The discriminator projection is `OptionSem.byTag`'s own (`tagOfV`), so this table
  -- and the admission it bounds read the same function rather than two copies of one
  -- lookup-and-match.
  | .dunion d opts => fun v =>
    match tagOfV d v with
    | some tag => decide (tag ∈ allTags d opts)
    | none => false
  -- `q` is a predicate on *values*, so it applies here without ceremony: `refine`'s `e` is
  -- defined only where `q` holds, so `adm t ∩ q` is a sound bound and a strictly better one
  -- than the passthrough. `admA` was long said not to be able to follow — "`q` tests the
  -- value a read *produces*, and no syntactic set of attributes bounds that" — which is a
  -- reason to stop being *syntactic*, not a reason to drop `q`. It now follows, one decode
  -- out; see `refineReads`. `held` is the row that is still one-sided.
  | .refine t q => fun v => adm t v && q v
  | .legacy t _ => adm t
  -- §1's two number gates, recorded for the same reason a literal's set is: a gate the term
  -- owns is exactly what `adm` is for. Only `decimal` is a `refine` over an ungated base
  -- (`decimalCodec_e_restrict`, over `wfDecimalCodec`). At `number` there is none to refine:
  -- `Attr.n` carries `Numeral.WF`, so `numberCodec` **is** §1's set — `Combinators.lean`'s
  -- "The base at `N` is §1's own set, not an ungated one", and the reason `decimal`'s
  -- restriction lemma has no numeric counterpart to cite beside it.
  | .nullable t => fun v => adm t v || (match v with | .null => true | _ => false)
  | .number => inD
  | .decimal => isStored
  -- A union admits what some option admits — the same `⋃` `κ` already takes. Without it
  -- the union spelling of a literal set forgets both sets, where the n-ary literal keeps
  -- them, which would make `union(literal a, literal b)` strictly weaker than
  -- `literal(a, b)` for no reason the semantics gives.
  | .union opts => fun v => admList opts v
  -- Everything below is `⊤` — **no information** — and each row says why, so that a `⊤`
  -- is a recorded decision rather than the residue of a catch-all.
  --
  -- The four ground scalars whose codec accepts the whole carrier of their kind. (`number`
  -- and `decimal` are the two that do not, and they are rows above.)
  | .string | .boolean | .binary | .null => fun _ => true
  -- The containers. `adm (array c)` would have to contain the empty array whatever `c`
  -- is, so propagating the element's set would claim a separation that is false —
  -- `not_uAtCan_array_literals` is the witness. Same argument for the other four.
  | .set _ | .array _ | .tuple _ _ | .record _ | .object _ => fun _ => true
  -- `held` is transparent here too, and `f` is what makes it so rather than what blocks
  -- it: `(c.through f g).e v = c.e (f v)` by `Iff.rfl`, so the writable set is the
  -- subterm's pulled back along `f`. `f` is *data the term carries*, and `adm` is a
  -- function that can apply it — nothing here needs `held`'s iso obligation.
  | .held t f _ => fun v => adm t (f v)
  -- `lazy` propagates, for the reason given at `κ`.
  | .lazy t => adm t
  -- `custom` carries its pair as data, which is the reason it is *analysable*, not the
  -- reason it is not: `denote`'s `custom` row sets `e := ce`, so `dom(e)` is `ce`'s and
  -- this row is exact. The first of the two rows that ask their own codec; see the
  -- section header.
  | .custom ce _ => fun v => (ce v).isSome
  -- `opaq` is the second member of that family, and this row is the whole of the change
  -- that made it one. `denote (.opaq lossy)` **is** `opaqCodecω lossy` (`denote_opaq`), so
  -- asking the codec is asking the denotation, and the row is `dom(e)` on the nose.
  --
  -- What it replaces was a scalar-prefix approximation — `.num ↦ lossy`, everything else
  -- `⊤` — which saw only the top constructor of the hole. A non-lossy `opaque` also refuses
  -- a `.numSet`, and an array or map carrying a numeral anywhere inside; so does a *lossy*
  -- one, at any numeral whose text is not `Numeral.WF`. None of that is syntax, and none of
  -- it needs to be: `opaqCodecω` recurses on the value's own depth, and so does this row,
  -- by deferring to it.
  | .opaq lossy => fun v => ((opaqCodecω lossy).e v).isSome

/-- `adm`'s union row, as the list recursion the kernel needs. -/
noncomputable def admList : List Term → Value → Bool
  | [], _ => false
  | t :: ts, v => adm t v || admList ts v

end

/-- **`refine`'s read-side gate**: decode with the base, then apply `q` to what comes out.

    The row this replaces was `admA (.refine t q) = admA t` — the predicate dropped — and
    the reason on record was that `q` tests the value a read *produces*, so no *syntactic*
    set of attributes bounds it. The premise is true and the conclusion does not follow, in
    exactly the way `number`'s and `opaq`'s `⊤`s did not follow: a row is not confined to
    syntax. It may call the denotation, and the denotation is what produces the value `q`
    tests. `(denote t).p a` is that value, or `none`; the gate is `q` of it.

    Shared verbatim by §5's `admA` and §5.5's `AdmA`, so the two rows are the *same*
    function at `refine` and `AdmA_le_admA` is a containment rather than a coincidence. -/
noncomputable def refineReads (t : Term) (q : Value → Bool) (a : Attr) : Bool :=
  match (denote t).p a with
  | some v => q v
  | none => false

/-- The gate, unfolded at a successful read. -/
theorem refineReads_some {t : Term} {q : Value → Bool} {a : Attr} {v : Value}
    (h : (denote t).p a = some v) : refineReads t q a = q v := by
  simp [refineReads, h]

/-- …and at a failed one. -/
theorem refineReads_none {t : Term} {q : Value → Bool} {a : Attr}
    (h : (denote t).p a = none) : refineReads t q a = false := by
  simp [refineReads, h]

mutual

/-- `adm`, attribute side. The two wrappers that are `⊤` for `adm` part company here,
    and the reason is which half of the pair each one touches.

    `legacy` is **not** transparent: `extendRead` widens `p` past the subterm's admissible set,
    which is the direction `admA` bounds. So the row names both channels —
    `admA t a || (r a).isSome` — rather than passing the subterm's through, and
    `not_admA_legacy` refutes that passthrough, one disjunct of this row and not the row.

    `held` **is** transparent, and this is the one case where `admA` sees further than `adm`.
    `through`'s `g` post-processes a read and is total, so `dom(p)` is the subterm's *exactly*
    (`through_p`): the adapter changes which value comes out, never which attributes go in.
    Only `f` is opaque and `f` gates the write, which is why `adm` stays `⊤`.
    A `held` over a literal against that literal is a pair this separates and §5's single `⊤`
    row could not.

    Both sides now see through `held`, by different routes: this one because `g` is total
    and post-processes, the value side because `f` is *applied* rather than guessed at.
    What stays asymmetric is the shape of the answer — `admA` passes the subterm's set
    through unchanged, `adm` pulls it back along `f`.

    `number` and a numeric `literal` are the **third and fourth rows that ask their own
    codec**, and
    they arrived by the same correction `opaq` did. Both were `⊤`, and both `⊤`s were bought
    with one non-argument: `Double.ofDec` is axiomatized, therefore no syntactic set of
    attributes bounds the read. The premise is true; the conclusion confuses *cannot bound
    which values* with *cannot bound which option*. `numberCodec.p` answers `none` at every
    attribute constructor but `.n`, and at an `.n` it answers at most one value, because
    `ofDec` is a **function**. Uniqueness is all `admA` ever needed, and it is free. The rows
    are `(numberCodec.p ·).isSome` and `((literalCodec .number ls).p ·).isSome`, both `dom(p)`
    on the nose; `opaque` against `number`, and two literals at disjoint alternative sets, are
    the two separations that were previously refuted or deferred to the pair reading.

    **`refine` is the fifth, and the same mistake bought it.** Its row was `admA t` with `q`
    discarded, on the ground that `q` tests the value a read produces and no *syntactic* set
    of attributes bounds that. True of syntax, and the row is not syntax: it decodes with the
    base and applies `q` to the result (`refineReads`). That is not merely sound, it is
    exact whenever the base's row is — `dom((c.restrict q).p) = {a | ∃ v, c.p a = some v ∧ q v}`
    is what the row computes — and two refinements of one base with disjoint predicates are
    the separation it buys. -/
noncomputable def admA : Term → Attr → Bool
  | .dunion d opts => fun a =>
    match tagOfA d a with
    | some tag => decide (tag ∈ allTags d opts)
    | none => false
  -- `refine` asks its base to decode and then applies `q` — the fifth row to ask rather
  -- than describe, and the last of the family. See `refineReads`.
  | .refine t q => fun a => admA t a && refineReads t q a
  | .held t _ _ => admA t
  | .union opts => fun a => admAList opts a
  -- `decimal` holds numerals *as their text*, so its gate is a plain test on the stored
  -- attribute. `number`'s gate is not — the numeral goes through `Double.ofDec` — which is
  -- why its row asks the codec below instead of testing anything.
  | .nullable t => fun a => admA t a || (match a with | .null => true | _ => false)
  | .decimal => fun a => match a with | .n x => Numeral.Stored x | _ => false
  -- The payoff over `refine`: for every base but `number` the stored attribute *is* the
  -- value, so `ℓ` bounds the readable side in a `decide`. At `number` `ℓ` still bounds it,
  -- one indirection out, through the codec — see `admALit`'s `.number` row.
  | .literal k ls => admALit k ls
  -- As on the value side, the `⊤` rows are written out with their reasons.
  --
  -- Ground scalars accepting their whole carrier.
  | .string | .boolean | .binary | .null => fun _ => true
  -- **`number` is no longer one of them.** It sat in that group on the ground that
  -- `Double.ofDec` is an axiom, so no syntactic set of attributes bounds which numerals
  -- are readable. That is true and it is not what the row needed: `numberCodec.p` answers
  -- `none` at every attribute constructor but `.n`, so *which member* is bounded even
  -- though *which values* is not. Asking the codec gets both — `denote .number` **is**
  -- `numberCodec` (`rfl`), so this row is `dom(p)`, exactly, and it is the third of the
  -- rows that ask rather than describe.
  | .number => fun a => (numberCodec.p a).isSome
  -- The containers, by the empty-container argument on the value side.
  | .set _ | .array _ | .tuple _ _ | .record _ | .object _ => fun _ => true
  -- **`legacy` asks too now, and it is the last row that parted into `⊤`.** The excuse was
  -- that `extendRead` widens `p` past the subterm's admissible set, which is the direction
  -- `admA` bounds — true, and the wrong conclusion, because the thing it widens *by* is `r`,
  -- which the term carries. Both channels are named, so the row is their union.
  --
  -- `not_admA_legacy` still stands and is about something else: §5's *passthrough*, `admA t`
  -- alone, really is unsound here. A union is not a passthrough. `Exactness.lean`'s section
  -- "why `legacy` was in the wrong family" is the analysis, and reached it first for `AdmA`.
  | .legacy t r => fun a => admA t a || (r a).isSome
  -- `lazy` propagates here too, and for the same reason: `p` is the subterm's.
  | .lazy t => admA t
  -- `custom`'s read side, exact for the same reason: `p := cp`.
  | .custom _ cp => fun a => (cp a).isSome
  -- `opaq`'s read side, deferring the same way: `p := (opaqCodecω lossy).p`, so the row is
  -- `dom(p)` exactly — the refused `.ns`, and the `.l`/`.m` carrying an unreadable numeral
  -- somewhere inside, are all seen, and none of them by a rule about `opaque`.
  | .opaq lossy => fun a => ((opaqCodecω lossy).p a).isSome

/-- …and on the attribute side. -/
noncomputable def admAList : List Term → Attr → Bool
  | [], _ => false
  | t :: ts, a => admA t a || admAList ts a

end

/-! ### Tag admission, on both sides

`(dunion)`'s admission and `adm`/`admA` at a `dunion` are the same shape — a lookup of the
discriminator, and a membership test on the tag it carries. Stating that shape once is
what lets the `dunion` cases below say the one thing they are about: the tag the
admitting option matched is one of the union's tags. -/

/-- `adm` at a `dunion` is the same test, against the union's whole tag set. -/
theorem adm_dunion {d : Name} {opts : List Term} {v : Value} :
    adm (.dunion d opts) v = true ↔
      ∃ tag, tagOfV d v = some tag ∧ tag ∈ allTags d opts := by
  simp only [adm]
  cases tagOfV d v with
  | none => simp
  | some tag => simp

/-- …and `admA` likewise. -/
theorem admA_dunion {d : Name} {opts : List Term} {a : Attr} :
    admA (.dunion d opts) a = true ↔
      ∃ tag, tagOfA d a = some tag ∧ tag ∈ allTags d opts := by
  simp only [admA]
  cases tagOfA d a with
  | none => simp
  | some tag => simp

/-! ## κ is sound for the denotation -/

/-- Every option of a `⋃` is a sublist of it. -/
theorem κList_mem : ∀ {ts : List Term} {ks}, κList ts = some ks →
    ∀ t ∈ ts, ∃ ks', κ t = some ks' ∧ ∀ k ∈ ks', k ∈ ks
  | [], _, _, t, ht => absurd ht (by simp)
  | t₀ :: ts, ks, h, t, ht => by
      replace h : (match κ t₀, κList ts with
        | some ks₀, some ks' => some (ks₀ ++ ks') | _, _ => none) = some ks := h
      cases hk₀ : κ t₀ with
      | none => rw [hk₀] at h; exact nomatch h
      | some ks₀ =>
        cases hks : κList ts with
        | none => rw [hk₀, hks] at h; exact nomatch h
        | some ks' =>
          rw [hk₀, hks] at h
          replace h : some (ks₀ ++ ks') = some ks := h
          cases h
          rcases List.mem_cons.mp ht with rfl | ht'
          · exact ⟨ks₀, hk₀, fun k hk => List.mem_append.mpr (Or.inl hk)⟩
          · obtain ⟨ks₁, hκ₁, hsub⟩ := κList_mem hks t ht'
            exact ⟨ks₁, hκ₁, fun k hk => List.mem_append.mpr (Or.inr (hsub k hk))⟩

/-- Fourteen of `κ`'s rules name a **single kind**, and are settled by the same two
    moves: `κ` reduces to that singleton, and the codec's own `e` refuses every value of
    another kind. Written out that is five lines fourteen times; here it is once. -/
local macro "single_kind" hk:ident hv:ident he:ident : tactic =>
  `(tactic| (cases $hk:ident
             cases $hv:ident <;> first
               | exact List.mem_cons_self _ _
               | exact nomatch $he:ident))

/-- Encoding lands in `κ`: a term's writable values have the kinds its `κ` names.
    (Where `κ` answers `⊤` there is nothing to say — the table's point.)

    The rules that are not `single_kind` are exactly the ones where `κ` is *computed*
    from a subterm's: the two transparent wrappers, `nullable`'s `∪`, `union`'s `⋃`,
    and `dunion`, whose kind comes from the option that admitted rather than from its
    own syntax. Four more answer `⊤`, where the hypothesis is unsatisfiable. -/
theorem κ_sound : ∀ (t : Term) {ks : List Kind} {v a},
    κ t = some ks → (denote t).e v = some a → Value.kind v ∈ ks
  | t, ks, v, a, hκ, he => by
    cases t with
    | string => single_kind hκ v he
    | decimal => single_kind hκ v he
    | literal k ls =>
      -- `(literal)` is the one single-kind rule whose kind comes from *data*, so the macro
      -- cannot serve. What it needs is only the *prism*: `e` is defined exactly where `inL`
      -- holds, and `inL` holds only at the base's own kind. `numberCodec` never has to be
      -- unfolded — its gate is a `dite` on `Numeral.WF`, whose decision is a string parser.
      cases hκ
      have hq : inL k ls v = true := (restrict_e.mp he).1
      cases k <;> cases v <;> simp_all [inL, Value.kind]
    | number => single_kind hκ v he
    | boolean => single_kind hκ v he
    | null => single_kind hκ v he
    | binary => single_kind hκ v he
    | set t' => single_kind hκ v he
    | array t' => single_kind hκ v he
    | tuple ts tail => single_kind hκ v he
    | record t' => single_kind hκ v he
    -- the payload is matched because `single_kind` refutes the non-`map` values *by
    -- reduction*: `bodySem` is a companion, so it reduces only at a constructor
    | object body => cases body with | mk fields ff rest => single_kind hκ v he
    | dunion d opts =>
      -- a stamped option writes a `map`, so the kind is `map` however it was reached
      cases hκ
      obtain ⟨o, ho, hadm, -⟩ := altCodec_e_admits he
      simp only [optionSems_eq, denoteTagged_eq] at ho
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ho
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch hadm
    | refine t' q => exact κ_sound t' hκ (restrict_e.mp he).2
    | legacy t' r => exact κ_sound t' hκ he
    | nullable t' =>
      -- `nullable`'s `∪`: `null` is the wrapper's own kind, everything else the
      -- subterm's, and `orNull` sends every non-`null` value straight to it
      replace hκ : (κ t').map (Kind.null :: ·) = some ks := hκ
      obtain ⟨ks', hκt, rfl⟩ := Option.map_eq_some'.mp hκ
      cases hw : (denote t').ownsNull with
      | true =>
        -- the guard declined: the wrapper writes exactly what the subterm writes
        rw [show (denote (.nullable t')).e = (denote t').e from
          withNull_e_of_owns hw] at he
        exact List.mem_cons_of_mem _ (κ_sound t' hκt he)
      | false =>
        rw [show denote (.nullable t') = (denote t').withNull from rfl,
          withNull_eq_orNull hw] at he
        cases v
        case null => exact List.mem_cons_self _ _
        all_goals exact List.mem_cons_of_mem _ (κ_sound t' hκt he)
    | union opts =>
      -- `union`'s `⋃`: the kind is the admitting option's, and `κList` contains it
      obtain ⟨o, ho, -, hoe⟩ := altCodec_e_admits he
      simp only [optionSems_eq, denoteTagged_eq] at ho
      obtain ⟨tx, htx, rfl⟩ := List.mem_map.mp ho
      rw [optionSemOf_c] at hoe
      obtain ⟨ksx, hκx, hsub⟩ := κList_mem hκ tx htx
      exact hsub _ (κ_sound tx hκx hoe)
    -- `κ` is `⊤` here: nothing is claimed, and the hypothesis is unsatisfiable
    | held t' f g => exact nomatch hκ
    | lazy γ => exact κ_sound γ hκ he
    | custom ce cp => exact nomatch hκ
    | opaq lossy => exact nomatch hκ
/-- An option's admission lifts to the list — the `⋃` of `adm`'s union row. -/
theorem admList_of_mem : ∀ {opts : List Term} {t : Term} {v : Value},
    t ∈ opts → adm t v = true → admList opts v = true
  | t' :: ts, t, v, hm, h => by
    rcases List.mem_cons.mp hm with rfl | hm'
    · simp [admList, h]
    · simp [admList, admList_of_mem hm' h]

/-- …and on the attribute side. -/
theorem admAList_of_mem : ∀ {opts : List Term} {t : Term} {a : Attr},
    t ∈ opts → admA t a = true → admAList opts a = true
  | t' :: ts, t, a, hm, h => by
    rcases List.mem_cons.mp hm with rfl | hm'
    · simp [admAList, h]
    · simp [admAList, admAList_of_mem hm' h]

theorem adm_sound : ∀ (t : Term) {v a},
    (denote t).e v = some a → adm t v = true
  | t, v, a, he => by
    cases t
    -- `adm` at a literal **is** the codec's own prism, so soundness is the prism's first
    -- projection and nothing else. This was three cases — a `simp_all` for strings, a
    -- `Double.ofDec` split for numbers, and a five-way one for arity one.
    case literal k ls => exact (restrict_e.mp he).1
    case dunion d opts =>
      -- the admitting option's tag check is exactly `adm`'s, at one option
      obtain ⟨o, ho, hadm, -⟩ := altCodec_e_admits he
      simp only [optionSems_eq, denoteTagged_eq] at ho
      simp only [List.mem_map] at ho
      obtain ⟨-, ⟨tx, htx, rfl⟩, rfl⟩ := ho
      obtain ⟨tag, hV, htag⟩ := byTag_admitV.mp hadm
      exact adm_dunion.mpr ⟨tag, hV,
        mem_allTags htx htag⟩
    case refine t' q =>
      obtain ⟨hq, hc⟩ := restrict_e.mp he
      simp only [adm, adm_sound t' hc, hq, Bool.and_self]
    case nullable t' =>
      cases hw : (denote t').ownsNull with
      | true =>
        rw [show (denote (.nullable t')).e = (denote t').e from
          withNull_e_of_owns hw] at he
        simp [adm, adm_sound t' he]
      | false =>
        rw [show denote (.nullable t') = (denote t').orNull from
          withNull_eq_orNull hw] at he
        rcases orNull_e.mp he with ⟨rfl, -⟩ | ⟨-, hc⟩
        · simp [adm]
        · simp [adm, adm_sound t' hc]
    case number =>
      cases v with
      | num d =>
        rw [show (denote .number).e (.num d) = numberCodec.e (.num d) from rfl,
          numberCodec_e_num] at he
        by_cases hw : Numeral.WF d.toDec = true
        · simp [adm, inD, hw]
        · rw [dif_neg hw] at he; exact nomatch he
      | _ => exact nomatch he
    case decimal =>
      cases v with
      | str s =>
        rw [show (denote .decimal).e (.str s) = decimalCodec.e (.str s) from rfl,
          decimalCodec_e_str] at he
        by_cases hs : Numeral.Stored s = true
        · simp [adm, isStored, hs]
        · rw [dif_neg hs] at he; exact nomatch he
      | _ => exact nomatch he
    case legacy t' r => exact adm_sound t' (extendRead_e.mp he)
    case lazy t' => exact adm_sound t' he
    case held t' f g => exact adm_sound t' he
    case custom ce cp => simp_all [adm, denote]
    case union opts =>
      obtain ⟨o, ho, -, hoe⟩ := altCodec_e_admits he
      simp only [optionSems_eq, denoteTagged_eq] at ho
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      rw [optionSemOf_c] at hoe
      exact admList_of_mem htx (adm_sound tx hoe)
    -- the row *is* the definedness being asserted, exactly as at `custom` one line up
    case opaq lossy => simp_all [adm, denote]
    all_goals rfl

/-- Reading lands in `admA`. -/
theorem admA_sound : ∀ (t : Term) {a v},
    (denote t).p a = some v → admA t a = true
  | t, a, v, hp => by
    cases t
    case literal k ls =>
      -- The read side is the prism's second projection *plus* the base's own reading. Two
      -- shapes of row, and they split here: the four bases whose stored attribute *is* the
      -- value are spelled out and close through `restrict_p`, while the two numeric bases ask
      -- their codec, so `hp` **is** the answer being asked for —
      -- `denote (.literal k ls)` is `literalCodec k ls` by `rfl` at either.
      cases k
      case number  => cases a <;> simp_all [admA, admALit, denote]
      case decimal => cases a <;> simp_all [admA, admALit, denote]
      all_goals
        obtain ⟨hb, hq⟩ := restrict_p.mp hp
        cases a <;>
          simp only [baseCodec, stringCodec, booleanCodec, binaryCodec, nullCodec,
                     Option.some.injEq] at hb <;>
          first
            | (subst hb; simp [admA, admALit, inL] at hq ⊢; exact hq)
            | exact absurd hb (by simp)
            | simp [admA, admALit]
    case dunion d opts =>
      obtain ⟨o, ho, hadm, -⟩ := altCodec_p_admits hp
      simp only [optionSems_eq, denoteTagged_eq] at ho
      simp only [List.mem_map] at ho
      obtain ⟨-, ⟨tx, htx, rfl⟩, rfl⟩ := ho
      obtain ⟨tag, hA, htag⟩ := byTag_admitA.mp hadm
      exact admA_dunion.mpr ⟨tag, hA,
        mem_allTags htx htag⟩
    case refine t' q =>
      obtain ⟨hp', hq⟩ := restrict_p.mp hp
      rw [admA, Bool.and_eq_true]
      exact ⟨admA_sound t' hp', by rw [refineReads_some hp']; exact hq⟩
    case nullable t' =>
      cases hw : (denote t').ownsNull with
      | true =>
        rw [show (denote (.nullable t')).p = (denote t').p from
          withNull_p_of_owns hw] at hp
        simp [admA, admA_sound t' hp]
      | false =>
        rw [show denote (.nullable t') = (denote t').orNull from
          withNull_eq_orNull hw] at hp
        rcases orNull_p.mp hp with ⟨rfl, -⟩ | ⟨-, hc⟩
        · simp [admA]
        · simp [admA, admA_sound t' hc]
    case decimal => cases a <;> simp_all [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, decimalCodec, admA]
    case held t' f g =>
      obtain ⟨w, hw, -⟩ := through_p.mp hp
      exact admA_sound t' hw
    case lazy t' => exact admA_sound t' hp
    case custom ce cp => simp_all [admA, denote]
    case union opts =>
      obtain ⟨o, ho, -, hop⟩ := altCodec_p_admits hp
      simp only [optionSems_eq, denoteTagged_eq] at ho
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      rw [optionSemOf_c] at hop
      exact admAList_of_mem htx (admA_sound tx hop)
    case opaq lossy => simp_all [admA, denote]
    -- `number` joined them: the row is `dom(p)`, and `hp` says `p` is defined here
    case number => simp_all [admA, denote]
    -- `legacy` is the union of two named channels, so the read landed in one of them
    case legacy t' r =>
      rw [denote_legacy] at hp
      simp only [admA, Bool.or_eq_true]
      rcases extendRead_p.mp hp with hcv | ⟨-, hrv⟩
      · exact Or.inl (admA_sound t' hcv)
      · exact Or.inr (by simp [hrv])
    all_goals rfl

/-! ### `admA`'s `legacy` row, and why it is not the passthrough

§5 lists `refine`, `optional`, `fallback` and `legacy` as passing `adm` through on one `adm`.
The value side does; the attribute side cannot, because `extendRead` widens `p` by `r`. That
rules out the *passthrough* and not a row: `r` is data the term carries, so `dom(p)` is
`dom((denote t).p) ∪ dom(r)`, both halves named, and the row is `admA t a || (r a).isSome`.
`Exactness.lean`'s "why `legacy` was in the wrong family" has the fuller argument.

**The witness below refutes the passthrough, which is one disjunct and not the row.**
`admA_sound` would break for `admA t` alone: the witness reads an `N` attribute out of a
`legacy` over a string literal, so a passthrough would claim the read is inside
`literal("A")`'s admissible set. This is the specification defect with no other
machine-checked witness.

Asking the codec — `((denote (.legacy t r)).p a).isSome` — is exact and costs one line, and is
**refused**: it replaces the subterm's over-approximation with its exact read domain, so it
sees through `admA (.object _) = ⊤`, which `ARCHITECTURE.md` §5 records as load-bearing slack.
Two objects cannot be separated by `SepA` since both rows are `⊤`; wrapped in a `legacy` they
could be, while `select` still attempts both — `not_uAtCan_of_sepJ`'s failure one wrapper out. -/

/-- A migration that reads a numeral into the literal's value — the shape `legacy` exists
    for, and the shape no syntactic set over the subterm can bound. -/
def rNumeral : Attr → Option Value
  | .n _ => some (.str "A")
  | _ => none

/-- The read really does land outside the subterm's `admA`. -/
theorem legacy_p_outside_admA :
    (denote (.legacy (.literal .string (.of "A" ∅)) rNumeral)).p (.n (.of "1")) = some (.str "A") ∧
      admA (.literal .string (.of "A" ∅)) (.n (.of "1")) = false := ⟨rfl, rfl⟩

/-- **§5's `adm` cannot pass through `legacy` on the read side.** Stated as the row's
    refutation rather than as an omission, so the divergence between the document's one
    `adm` and the model's two is a theorem rather than a comment. -/
theorem not_admA_legacy :
    ¬ ∀ (t : Term) (r : Attr → Option Value) (a : Attr) (v : Value),
      (denote (.legacy t r)).p a = some v → admA t a = true := by
  intro h
  have hbad := h (.literal .string (.of "A" ∅)) rNumeral (.n (.of "1")) (.str "A")
    legacy_p_outside_admA.1
  rw [legacy_p_outside_admA.2] at hbad
  exact nomatch hbad

/-! ## Admission is guarded -/

/-- Any option's value admission is `κ`-guarded: an admitted value has a kind the
    option's (non-`⊤`) `κ` names. -/
theorem admitV_kind (t : Term) {ks : List Kind} {v}
    (hκ : κ t = some ks)
    (h : (optionSemOf (denote t) (specOf t)).admitV v = true) :
    Value.kind v ∈ ks := by
  cases hs : specOf t with
  | none =>
    rw [hs] at h
    replace h : ((denote t).e v).isSome = true := h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    exact κ_sound t hκ ha
  | some spec =>
    rw [hs] at h
    cases t
    case object body =>
      replace hκ : some [Kind.map] = some ks := hκ
      cases hκ
      cases v <;> first
        | exact List.mem_cons_self _ _
        | exact nomatch h
    all_goals exact nomatch hs

/-- Any option's attribute admission is member-guarded: with a lawful pair and a
    named member, an admitted attribute carries that member — §5's read-side (W),
    doing (D)'s job through the member index. -/
theorem admitA_member (t : Term) {μ a}
    (hμ : μSyn t = some μ) (hlaw : Lawful (denote t))
    (h : (optionSemOf (denote t) (specOf t)).admitA a = true) :
    a.member = μ := by
  cases hs : specOf t with
  | none =>
    rw [hs] at h
    replace h : ((denote t).p a).isSome = true := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    refine hlaw.reads ?_ hv
    rw [denote_μ]
    exact hμ
  | some spec =>
    rw [hs] at h
    cases t
    case object body =>
      replace hμ : some Member.M = some μ := hμ
      cases hμ
      cases a <;> first
        | rfl
        | exact nomatch h
    all_goals exact nomatch hs

/-! ## Options admit their own canonical pairs -/

/-- Only `optional` denotes to `opt`, which is what the value-side guard needs of a
    non-`optional` field. Stated where every argument is a variable — at the use site
    the field is `ff k`, and eliminating a function application in place is more
    trouble than naming the fact. -/
theorem fieldSem_ne_opt {fd : Field}
    (h : (match fd with | Field.optional _ => false | _ => true) = true) :
    ∀ c, fieldSem fd ≠ FieldSem.opt c := by
  cases fd <;> simp_all [fieldSem]

/-- Name admission from names alone: everything present is declared, everything
    required is present.

    Two hypotheses in, `keysOk` out — literally. `keysOk` is now a pair of quantifiers
    over the declared names, so this is `⟨hsub, hreq⟩` where the row form needed a
    `List.any` witness built by hand and a `List.all` over the mapped row. -/
theorem keysOk_of_names {fields : Finset Name} {ff : {k // k ∈ fields} → Field}
    {keys : Finset Name}
    (hsub : ∀ k ∈ keys, k ∈ fields)
    (hreq : ∀ k : {k // k ∈ fields},
      (match ff k with | Field.optional _ => false | _ => true) = true → k.1 ∈ keys) :
    keysOk ⟨fields, fun k => match ff k with | Field.optional _ => false | _ => true⟩
      keys = true := by
  simp only [keysOk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hsub, hreq⟩

/-- Object-encode under a closed rest policy stamps name admission: every written name
    is declared and every non-`opt` name is written.

    **One statement where there were two.** The list representation had a value row and
    an attribute row, and the second half of this lemma was the first transported along
    `traverse_fst`. `M`'s payload is a key set with a function on it, and encoding does
    not touch the key set — so the value side's admission *is* the attribute side's, and
    there is nothing to transport. -/
theorem keysOk_of_encode {fields : Finset Name} {ff : {k // k ∈ fields} → Field}
    {keys : Finset Name}
    {f : {k // k ∈ keys} → Value} {g : {k // k ∈ keys} → Attr}
    (hval : valPresentB ⟨fields, fun k => fieldSem (ff k)⟩ keys = true)
    (hfi : funImage (fun k : {k // k ∈ keys} =>
        (entryCodec ⟨fields, fun k => fieldSem (ff k)⟩ none k.1).bind
          (fun c => c.e (f k))) = some g) :
    keysOk ⟨fields, fun k => match ff k with | Field.optional _ => false | _ => true⟩
      keys = true := by
  refine keysOk_of_names (fun k hk => ?_) (fun k hb => ?_)
  · -- a name the entry function is defined at is declared: `rc?` is `none`, so
    -- `entryCodec` succeeds only through the field table
    by_contra hnk
    have hw := funImage_some hfi ⟨k, hk⟩
    rw [show entryCodec (⟨fields, fun k => fieldSem (ff k)⟩ : MapOf FieldSem) none k
        = none from by simp only [entryCodec, MapOf.at, dif_neg hnk]] at hw
    exact nomatch hw
  · exact valPresentB_spec hval (MapOf.at_of_mem (m := ⟨fields, _⟩) k)
      (fieldSem_ne_opt hb)

/-- A closed option admits its own canonical pairs, on both sides. An *open* object —
    a rest codec — is excluded, as §5 demands: an undeclared name disqualifies the
    option even where its rest codec would hold it. -/
theorem optionSem_self_admit (t : Term)
    (hcl : t.isOpenObject = false)
    (hlaw : Lawful (denote t)) {v a}
    (he : (denote t).e v = some a) :
    (optionSemOf (denote t) (specOf t)).admitV v = true ∧
    (optionSemOf (denote t) (specOf t)).admitA a = true := by
  cases hs : specOf t with
  | none =>
    constructor
    · show ((denote t).e v).isSome = true
      rw [he]; rfl
    · show ((denote t).p a).isSome = true
      rw [hlaw.retract he]; rfl
  | some spec =>
    cases t
    case object body =>
      cases body with | mk fields ff rest =>
      replace hs : some (⟨fields, fun k =>
        match ff k with | Field.optional _ => false | _ => true⟩ : MapOf Bool) =
        some spec := hs
      cases hs
      have hrc : rcOf (restSem rest) = none := by
        cases rest with
        | drop => rfl
        | refuse => rfl
        | codec tr =>
          exact absurd rfl
            (Term.isOpenObject_eq_false.mp hcl (.mk fields ff (.codec tr)) tr rfl)
      replace he : (objectCodecCore
          ⟨fields, fun k => fieldSem (ff k)⟩
          (rcOf (restSem rest))
          (keepB (restSem rest)
            ⟨fields, fun k => fieldSem (ff k)⟩)).e v =
        some a := he
      obtain ⟨keys, fv, g, rfl, rfl, hval, hfi⟩ := objectCodecCore_e_inv he
      rw [hrc] at hfi
      -- both halves are the same `keysOk`, at the key set the two payloads share
      exact ⟨keysOk_of_encode hval hfi, keysOk_of_encode hval hfi⟩
    all_goals exact nomatch hs

/-- Any option's value admission is `adm`-guarded. -/
theorem admitV_adm (t : Term) {v}
    (h : (optionSemOf (denote t) (specOf t)).admitV v = true) : adm t v = true := by
  cases hs : specOf t with
  | none =>
    rw [hs] at h
    replace h : ((denote t).e v).isSome = true := h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    exact adm_sound t ha
  | some spec =>
    cases t
    case object body => rfl
    all_goals exact nomatch hs

/-- Any option's attribute admission is `admA`-guarded. -/
theorem admitA_admA (t : Term) {a}
    (h : (optionSemOf (denote t) (specOf t)).admitA a = true) : admA t a = true := by
  cases hs : specOf t with
  | none =>
    rw [hs] at h
    replace h : ((denote t).p a).isSome = true := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    exact admA_sound t hv
  | some spec =>
    cases t
    case object body => rfl
    all_goals exact nomatch hs

/-! ## The discharger -/

/-- `Pairwise`, upgraded with membership. -/
theorem pairwise_imp_mem {α : Type} {R S : α → α → Prop} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, R x y → S x y) → List.Pairwise R l →
      List.Pairwise S l
  | [], _, _ => .nil
  | a :: l, h, hp => by
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
      refine List.Pairwise.cons (fun y hy =>
          h a (List.mem_cons_self a l) y (List.mem_cons_of_mem a hy) (hhead y hy)) ?_
      exact pairwise_imp_mem
        (fun x hx y hy => h x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy))
        htail

/-! ### Why a discharger may drop §5's two `ident` conjuncts

    §5 states (K)'s second disjunct as `ident(cᵢ) ∧ ident(cⱼ) ∧ adm(cᵢ) ∩ adm(cⱼ) = ∅`, and
    every discharger this development has written keeps only the `adm` clause. Dropping a
    conjunct from a premise *weakens* the discharger, so the theorem is stronger either way —
    but it leaves `ident` asserting nothing, which is how a faithful transcription becomes an
    unlocatable claim. Here is the argument that the two conjuncts are redundant, which
    until now lived only in prose.

    It turns on `adm`'s default: every term that is not a `literal`, a
    `discriminatedUnion`, or a transparent wrapper over one answers `true` everywhere,
    and those are exactly the terms `ident` holds of at the leaves. So a term whose `adm`
    ever *refuses* is `ident` — and two options with disjoint `adm` must each refuse
    somewhere, provided each also admits somewhere. -/

mutual

/-- **`adm` is informative only where `ident` holds.** If `adm` refuses a single value,
    the term is `ident`. This is the pinning `ident` otherwise lacks: `κ`, `adm` and
    `admA` each have a soundness lemma tying them to the denotation, and `ident` has no
    denotational content to tie — what it has is this relation to `adm`, which is what
    §5 actually uses it for. -/
theorem ident_of_adm : ∀ {t : Term} {v : Value}, adm t v = false → ident t = true

  | .dunion _ _, _, _ => rfl
  | .refine _ _, _, _ => rfl
  | .literal _ _, _, _ => rfl
  | .number, _, _ => rfl
  | .decimal, _, _ => rfl
  | .legacy t _, v, h => ident_of_adm (t := t) (v := v) h
  | .union opts, v, h => identList_of_admList (opts := opts) (v := v) h
  | .nullable t, v, h => ident_of_adm (t := t) (v := v) (by
      simp only [adm, Bool.or_eq_false_iff] at h; exact h.1)
  | .lazy t, v, h => ident_of_adm (t := t) (v := v) h
  | .held t f _, v, h => ident_of_adm (t := t) (v := f v) h
  -- the two rows that ask their own codec: a refusal is the codec's, and both terms are
  -- `ident` unconditionally for exactly that reason
  | .custom _ _, _, _ => rfl
  | .opaq _, _, _ => rfl
  | .string, _, h | .boolean, _, h | .binary, _, h
  | .null, _, h | .set _, _, h | .array _, _, h | .tuple _ _, _, h
  | .record _, _, h | .object _, _, h => nomatch h

/-- A union all of whose options refuse a value is one all of whose options decide their
    own membership — `ident_of_adm` lifted to the list, which `adm`'s union row makes
    necessary. -/
theorem identList_of_admList : ∀ {opts : List Term} {v : Value},
    admList opts v = false → identList opts = true
  | [], _, _ => rfl
  | t :: ts, v, h => by
    simp only [admList, Bool.or_eq_false_iff] at h
    simp [identList, ident_of_adm h.1, identList_of_admList h.2]

end

/-- **§5's (K), recovered from `SepV`'s second disjunct.** Disjoint `adm` implies both
    `ident` conjuncts — given that each option admits *something*.

    That side condition is not bookkeeping: `dunion(d)` with no options is derivable, admits
    nothing, and is therefore `adm`-disjoint from `string`, which is not `ident`. -/
theorem admDisj_ident {x y : Term} (hdisj : ∀ v, adm x v = true → adm y v = false)
    (hx : ∃ v, adm x v = true) (hy : ∃ v, adm y v = true) :
    ident x = true ∧ ident y = true := by
  obtain ⟨vx, hvx⟩ := hx
  obtain ⟨vy, hvy⟩ := hy
  refine ⟨ident_of_adm (v := vy) ?_, ident_of_adm (v := vx) (hdisj vx hvx)⟩
  by_contra hc
  exact absurd (hdisj vy (by simpa using hc)) (by simp [hvy])

/-! ### The gap that remains, exhibited

    `admDisj_ident`'s two side conditions are not bookkeeping. A term whose admissible
    set is *empty* is `adm`-disjoint from everything, so it separates itself from options
    §5's (K) would refuse — and one such term is derivable. -/

/-- A `discriminatedUnion` with no options refuses every value: `allTags` is empty. -/
theorem adm_dunion_nil (d : Name) (v : Value) : adm (.dunion d []) v = false := by
  simp only [adm, allTags]
  cases tagOfV d v <;> rfl

/-- And it is derivable — `(dunion)`'s premises are quantified over the option list. -/
theorem typed_dunion_nil (d : Name) : Typed (.dunion d []) (HUnion []) (some .M) :=
  .dunion .nil (by simp) (by simp)

theorem not_ident_string : ident .string = false := rfl

/-- **The pair reading of the same fact**, and it is not superseded: it discharges the whole
    `UAtCan` for an `n`-ary family in one step, where the retired per-aspect route separated a
    pair at a time.
    Two refinements of one base read an attribute to the **same** value, so at most one
    predicate accepts it, and the readable side separates for the same reason the writable
    side does.

    The condition is *relational* — it is about options sharing a base, not about any one
    option's admissible set — which is why it is a discharger of its own as well as a row.
    `uniqueAdmission_of_disjoint` takes the two families as arbitrary predicates, so nothing
    here has to be syntactic: the attribute family is `∃ v, base.p a = some v ∧ q v`, which
    is exactly what `refineReads` computes, and disjointness is the base reading `a` to one
    value. -/
theorem uAtCan_of_refine_disjoint {base : Term} {qs : List (Value → Bool)}
    (hlaw : LawfulCore (denote base))
    (hdisj : List.Pairwise (fun q q' => ∀ v, q v = true → q' v = false) qs) :
    UAtCan (qs.map (fun q => Term.refine base q)) := by
  show UniqueAdmission (semsOf (qs.map (fun q => Term.refine base q)))
  refine uniqueAdmission_of_disjoint
    (SVs := qs.map (fun q v => q v = true))
    (SAs := qs.map (fun q a => ∃ v, (denote base).p a = some v ∧ q v = true))
    ?_ ?_ ?_ ?_ ?_
  · rw [semsOf, List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun q _ v hv => ?_
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hv
    exact (restrict_e.mp hw).1
  · rw [semsOf, List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun q _ a ha => ?_
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨hp, hq⟩ := restrict_p.mp hw
    exact ⟨w, hp, hq⟩
  · rw [List.pairwise_map]
    refine hdisj.imp fun h v hv hv' => ?_
    simp only at hv hv'
    rw [h v hv] at hv'; exact nomatch hv'
  · rw [List.pairwise_map]
    refine hdisj.imp fun h a hx hy => ?_
    obtain ⟨v, hv, hqv⟩ := hx
    obtain ⟨v', hv', hqv'⟩ := hy
    rw [hv] at hv'; cases hv'
    rw [h v hqv] at hqv'; exact nomatch hqv'
  · rw [semsOf, List.map_map]
    refine forall_mem_map fun q _ t a he => ?_
    simp only [Function.comp_apply] at he ⊢
    rw [optionSemOf_c] at he
    obtain ⟨hq, hb⟩ := restrict_e.mp he
    refine ⟨?_, ?_⟩
    · show ((denote (.refine base q)).e t).isSome = true
      rw [show (denote (.refine base q)).e t = some a from he]; rfl
    · show ((denote (.refine base q)).p a).isSome = true
      rw [show (denote (.refine base q)).p a = some t from
        restrict_p.mpr ⟨hlaw.retract hb, hq⟩]
      rfl

/-- **Literals over any base, in one theorem.** Drop the lawfulness side-condition by
    taking it from soundness, and what is left is the whole result: for *any derivable
    term* as base, a union of refinements with pairwise disjoint predicates admits uniquely
    on both sides.

    §3's `(literal-S)` and `(literal-N)` are two instantiations — `string` and the ungated
    double codec, at `∈ ℓ`. `boolean` and `binary` are two more, for which §3 writes no
    rule. And the base need not be ground at all: a union of disjoint refinements of one
    `object`, or of one `union`, discharges by the same theorem. There was never a
    per-member argument to make. -/
theorem uAtCan_of_refine_disjoint_of_typed {base : Term} {T μ}
    {qs : List (Value → Bool)} (h : Typed base T μ) (hob : Obligations base)
    (hdisj : List.Pairwise (fun q q' => ∀ v, q v = true → q' v = false) qs) :
    UAtCan (qs.map (fun q => Term.refine base q)) :=
  uAtCan_of_refine_disjoint (soundness_both h hob).1 hdisj

/-! ### Literals over a primitive §3 gives no `literal` rule for

    §3 names two `literal` rules, at `S` and at `N`. Nothing makes those two special: a
    literal over any ground term is `refine(base, ∈ ℓ)`, which is derivable already, and
    since `adm` now carries `q` and refinements of one base separate on both sides, such a
    union discharges exactly as a string literal's does. The two rules are the two someone
    bothered to name, not the two that are possible. -/

/-- A boolean "literal", as the refinement it is. -/
def isTrueV : Value → Bool := fun v => match v with | .bool b => b | _ => false

/-- …and its complement. -/
def isFalseV : Value → Bool := fun v => match v with | .bool b => !b | _ => false

/-- It is derivable, with the member the base names — no rule of its own. -/
theorem typed_boolLiteral : ∃ T, Typed (.refine .boolean isTrueV) T (some .BOOL) :=
  ⟨_, Typed.refine Typed.boolean⟩

/-- A base that is not ground at all, to show the theorem does not care. Two disjoint
    refinements of one `array(string)` separate exactly as two literals over `string` do —
    "literal" was never the operative word, "one base, disjoint predicates" was. -/
theorem uAtCan_refine_container {q q' : Value → Bool}
    (hd : List.Pairwise (fun a b => ∀ v, a v = true → b v = false) [q, q']) :
    UAtCan [Term.refine (.array .string) q, Term.refine (.array .string) q'] :=
  uAtCan_of_refine_disjoint_of_typed (Typed.array Typed.string)
    trivial hd

/-- And a union of two discharges on **both** sides, by the same shared-base argument that
    settles numeric literals — a primitive §3 never wrote a `literal` rule for. -/
theorem uAtCan_boolLiterals :
    UAtCan [Term.refine .boolean isTrueV, Term.refine .boolean isFalseV] := by
  have h : ∀ v, isTrueV v = true → isFalseV v = false := by
    intro v hv; cases v <;> simp_all [isTrueV, isFalseV]
  exact uAtCan_of_refine_disjoint (qs := [isTrueV, isFalseV])
    lawful_booleanCodec.core (by simpa using h)

/-! ### `nullable`, and a refusal that stopped being stipulated

    §5 makes `nullable` *never* `ident`, deliberately — "two nullable options both admit the
    null neither subterm decides". That was `adm` being `⊤` doing the work. With `adm`
    precise the same pair is still refused, but for the reason that was always the true
    one: their admissible sets **overlap at null**. So `ident` can propagate, and the
    refusal is derived rather than stipulated. -/

/-- Two nullable options still fail to separate — and now because their sets meet. -/
theorem not_sep_nullable_pair :
    ¬ (∀ v, adm (.nullable (.literal .string (.of "A" ∅))) v = true →
            adm (.nullable (.literal .string (.of "B" ∅))) v = false) := by
  intro h; exact absurd (h .null (by simp [adm, inL])) (by simp [adm, inL])

/-- But a nullable option separates from a plain one, which it could not while `adm` said
    `⊤` — the whole of what the row buys. -/
theorem sep_nullable_plain (v : Value) :
    adm (.nullable (.literal .string (.of "A" ∅))) v = true → adm (Term.literal .string (.of "C" ∅)) v = false := by
  cases v <;> simp_all [adm, inL]

/-! ### `lazy` is transparent, and all four tables now say so

    `denote (.lazy t) = { denote t with μ := none }`: the pair is the subterm's
    and only the member is erased. §5 lists `lazy` with `custom` and `opaque` as
    unanalysable, but that is inherited from the doc's thunk, which was `Unit → Term`.
    `Term.lazy` carries a plain `Term` — a deliberate change, made because a closure adds
    no constructible term and defeats the termination checker (`Term.lean`) — and the
    opacity in `κ`/`ident`/`adm`/`admA` was left behind by it.

    The four soundness cases are each a one-line appeal to the subterm's, which is the
    evidence that the propagation is definitional rather than argued. -/

/-- A `lazy` over a literal separates from a plain literal — the wrapper is invisible. -/
theorem sep_lazy_literal (v : Value) :
    adm (.lazy (.literal .string (.of "A" ∅))) v = true → adm (Term.literal .string (.of "C" ∅)) v = false := by
  cases v <;> simp_all [adm, inL]

/-- …and on the attribute side, where `lazy` is as transparent as it is on the writable
    one — unlike `legacy`, whose opacity really is one-sided. -/
theorem sepA_lazy_literal (a : Attr) :
    admA (.lazy (.literal .string (.of "A" ∅))) a = true → admA (Term.literal .string (.of "C" ∅)) a = false := by
  cases a <;> simp_all [admA, admALit]

/-- Nesting does not dim it: `κ` reaches a doubly-`lazy` scalar. -/
theorem kappa_lazy_lazy : κ (.lazy (.lazy .string)) = some [.string] := rfl

/-- And `ident` reaches through too, so a `lazy` option is `adm`-informative at all. -/
theorem ident_lazy : ident (.lazy (.literal .string (.of "A" ∅))) = true := rfl

/-! ### What "unanalysable" turned out to mean

    `held` and `custom` were on the unanalysable list because they carry Lean functions,
    and a function is not something a reader can look inside. But `adm` is not a reader:
    it is a function with the term in hand, and the term *carries* `f`, `ce` and `cp` as
    data. It can apply them.

    `(c.through f g).e v = c.e (f v)` holds by `Iff.rfl`, so `held`'s writable set is the
    subterm's pulled back along `f` — exactly, and with no appeal to `held`'s iso
    obligation, which is about `T` and roundtripping rather than about the domain.
    `custom` is starker still: `denote` sets `e := ce` and `p := cp`, so both rows are
    `isSome` of the very function the term carries, and `custom`'s `T` is *defined* as
    `dom(ce)`.

    And `opaq` is no longer the exception. It was called *largely* unanalysable on the
    ground that `opaqCodecω`'s domain is a recursion over the *input's* own depth, so no
    set the syntax names is precise about it. True, and the wrong conclusion: the row does
    not have to name the set, it can ask. `adm (.opaq lossy)` is now
    `((opaqCodecω lossy).e ·).isSome`, so the recursion the syntax cannot bound is the
    recursion the row runs, and `opaq` sits beside `custom` rather than after it.

    Three senses had been running together: (i) the term does not carry the information —
    true of nothing here, and `opaq` was the last row where it was still assumed;
    (ii) the domain cannot be computed without running the codec — true of `opaq` and of
    `custom`, and the reason both rows *do* run it, at the price of being
    `noncomputable`; (iii) a reader cannot see through it — true of `held`, `custom` and
    `opaq`, and not a property of the calculus. -/

/-- `held`'s writable set, exactly: the subterm's, pulled back along `f`. -/
theorem adm_held (t : Term) (f g : Value → Value) (v : Value) :
    adm (.held t f g) v = adm t (f v) := rfl

/-- `custom`'s rows are `dom(ce)` and `dom(cp)` on the nose — the sharpest form of
    "analysable": not a bound on the pair but the pair itself. -/
theorem adm_custom (ce : Value → Option Attr) (cp : Attr → Option Value) (v : Value) :
    adm (.custom ce cp) v = (ce v).isSome := rfl

/-- …and the read side likewise. -/
theorem admA_custom (ce : Value → Option Attr) (cp : Attr → Option Value) (a : Attr) :
    admA (.custom ce cp) a = (cp a).isSome := rfl

/-- Exact against the denotation, **both directions**. This is the statement a
    soundness-only bundling could never force: an over-approximation is sound however
    loose, and only the converse pins it. -/
theorem adm_custom_exact (ce : Value → Option Attr) (cp : Attr → Option Value) (v : Value)
    :
    adm (.custom ce cp) v = true ↔ ∃ a, (denote (.custom ce cp)).e v = some a := by
  simp [adm, denote, Option.isSome_iff_exists]

/-! ### What the unified `literal` carries

    At arity one `literal(v)` and `refine(g, · = v)` denote the same pair, so it is fair to
    ask why the constructor exists. `adm` is the same either way. `admA` is not: `ℓ` is data
    the *term* owns, so it can be tested against the stored attribute, where `refine`'s `q`
    is a value predicate and cannot be pushed there. That is the whole of it, and it holds
    at every base but one. -/

/-- `admA` sees the value at a boolean base, which §3 never wrote a `literal` rule for at all
    and which the model could not express before the base became an index. -/
theorem admA_literal_bool (ls : NEFinset Bool) (b : Bool) :
    admA (.literal .boolean ls) (.bool b) = decide (b ∈ ls.1) := rfl

/-- …and at a binary one, likewise. -/
theorem admA_literal_bin (ls : NEFinset Bytes) (b : Bytes) :
    admA (.literal .binary ls) (.b b) = decide (b ∈ ls.1) := rfl

/-- The writable side sees `ℓ` everywhere, `number` included — it is `inL`, the codec's prism.

    No longer `rfl`: `inL`'s `number` row splits on the carrier's gate, and the alternative is
    named by the element's own `d.2`. That is the whole cost of ~~LiteralD~~'s deletion on this
    side, and `adm_literal_exact` is what it bought. -/
theorem adm_literal_num (ls : NEFinset WFDouble) (d : WFDouble) :
    adm (.literal .number ls) (.num d.1) = decide (d ∈ ls.1) := by
  simp [adm, inL, d.2]

/-- **Where the two bases part — and they part by *how much work the row does*, not by
    whether it can be written.** A string literal's stored text *is* its value, so `ℓ` is
    visible in one `decide`. A numeric literal's is not: the stored numeral goes through
    `Double.ofDec`, and no syntactic set of *attributes* names the ones that read into `ℓ`.

    That used to be recorded as `admA_literalN_blind : admA (.literal .number ls) (.n x) =
    true` — the read side is `⊤` — and the conclusion was wrong. The row never needed to
    *name* the set; it only needed to be able to *decide* membership, and it can, by
    asking the codec (`denote (.literal .number ls)` is `literalCodec .number ls`, by
    `rfl`). What is left of the asymmetry is that the numeric answer is a `bind` through an
    axiomatized function rather than a `decide` — which is a statement about how the row is
    computed, not about what it knows. -/
theorem admA_literalS_sees (ls : NEFinset String) (s : String) :
    admA (.literal .string ls) (.s s) = decide (s ∈ ls.1) := rfl

/-- …and the numeric side sees `ℓ` as well, one indirection further out: an `N` attribute is
    admitted exactly when the numeral it holds reads to a well-formed member of `ℓ`. -/
theorem admA_literalN_sees (ls : NEFinset WFDouble) (x : WFNumeral) :
    admA (.literal .number ls) (.n x) = true ↔
      ∃ d : WFDouble, Double.ofDec x.1 = some d.1 ∧ d ∈ ls.1 := by
  show ((literalCodec .number ls).p (.n x)).isSome = true ↔ _
  rw [literalNCodec_p_n, numberCodec_p_n]
  cases hd : Double.ofDec x.1 with
  | none => simp
  | some d =>
    constructor
    · intro h
      cases hw : Numeral.WF d.toDec with
      | false => simp [hw] at h
      | true =>
        refine ⟨⟨d, hw⟩, rfl, ?_⟩
        -- `cases hm : decide` rather than `by_contra`, which reaches `Classical.em`
        cases hm : decide ((⟨d, hw⟩ : WFDouble) ∈ ls.1) with
        | false => simp [hw, inL, hm] at h
        | true => exact of_decide_eq_true hm
    · rintro ⟨d', hof, hmem⟩
      obtain rfl : d = d'.1 := Option.some.inj hof
      simp [d'.2, inL, hmem]

/-- …and every other attribute constructor is refused outright, because `numberCodec.p` is:
    the row bounds *which member* even where it cannot bound which values. -/
theorem admA_literalN_notN (ls : NEFinset WFDouble) (s : String) :
    admA (.literal .number ls) (.s s) = false := rfl

/-- **A union of numeric literals discharges on both sides — in one step, for any arity.**
    This used to be advertised as the *only* route, on the ground that §5's `admA` row sent a
    numeric literal to `⊤` and the table therefore could not tell two of them apart. The
    second half of that was wrong — the row asks the codec and tells two literals apart — and
    the correction does not cost
    this theorem anything: read from the *pair*, the options are refinements of a single
    `numberCodec` with disjoint predicates, and `uniqueAdmission_of_sharedBase` settles an
    `n`-ary family and both sides at once, where the table settles a pair at a time.

    Which is the honest reading of what a numeric literal set *is*: options told apart by
    the value a read produces, never by the text the store holds. That reading is now
    available to the table as well, because the table's row asks the same codec. -/
theorem uAtCan_of_literalN_disjoint {lss : List (NEFinset WFDouble)}
    (hdisj : List.Pairwise (fun ls ls' => ∀ d ∈ ls.1, d ∉ ls'.1) lss) :
    UAtCan (lss.map (Term.literal .number)) := by
  show UniqueAdmission (semsOf (lss.map (Term.literal .number)))
  have hs : semsOf (lss.map (Term.literal .number))
      = (lss.map (literalCodec .number)).map OptionSem.byAttempt := by
    simp [semsOf, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, List.map_map, specOf, optionSemOf, denote]
  rw [hs]
  refine uniqueAdmission_of_sharedBase (base := numberCodec) (qs := lss.map (inL .number))
    lawful_numberCodec.core ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun ls _ =>
      ⟨literalCodec_e_restrict .number ls, literalCodec_p_restrict .number ls⟩
  · rw [List.pairwise_map]
    refine hdisj.imp fun h v hv => ?_
    cases v
    case num d =>
      -- the gate is now inside `inL`'s `number` row, so the split names the subtype
      cases hw : Numeral.WF d.toDec with
      | false => simp [inL, hw] at hv
      | true =>
        simp only [inL, hw, dite_true, decide_eq_true_eq] at hv
        simp only [inL, hw, dite_true, decide_eq_false_iff_not]
        exact h ⟨d, hw⟩ hv
    all_goals exact Bool.noConfusion hv

/-! ### Separation, as one set per option per side

    `SepV` and `SepA` each offer a *choice* — a disjoint kind or a disjoint admissible
    set, a distinct member or a disjoint `admA` — and the choice is made per pair. That
    shape is an artifact of asking the question pairwise. Asked per *option*, the two
    sources of constraint simply **intersect**: an option admits a value only if `κ`
    allows its kind and `adm` allows the value. Disjointness of the intersections is
    implied by disjointness in either factor, so `SepV` and `SepA` are exactly what makes
    these families pairwise disjoint — and `uniqueAdmission_of_disjoint` finishes it,
    once, for both sides. -/

/-! ## The other two rows of §5's table

    §5's discharger table has four rows, and until now a reviewer checking it changed
    vocabulary halfway across: two rows are about `UAtCan opts` — a list of
    **terms** — and two are about `UniqueAdmission os`, a list of `OptionSem`. Worse,
    `(dunion)`'s row was never stated at all: it appeared only inside
    `lawful_dunionCodec`, where it is an argument rather than a claim.

    `(dunion)`'s row moves to term level here, so three of the four are one vocabulary.
    The fourth cannot follow, and the reason is worth stating rather than working
    around: `denote` gives `(opaque)` the **fuel-free** `opaqCodecω`, which budgets each
    input by its own depth and is not `altCodec` over any one list of options. Its (U)
    is therefore a statement about `opaqCodec` at a fuel, one level below the term
    language. That is a fact about `opaque`, not a gap in the table. -/

/-- The options of a `(dunion)`, exactly as `denote`'s dunion case builds them: tag
    admission on `d`, where `(union)`'s `semsOf` uses name admission. -/
noncomputable def semsOfD (d : Name) (opts : List Term) : List OptionSem :=
  (opts.map fun t' => (tagsOf d t', denote t')).map fun o => .byTag d o.1 o.2

/-- And it really is the denotation's option list — the `rfl` that keeps `semsOfD` from
    drifting away from `denote`. -/
theorem denote_dunion_semsOfD (d : Name) (opts : List Term) :
    denote (.dunion d opts) = altCodec (semsOfD d opts) (some .M) := by
  simp only [denote_dunion_tags, denoteTagged_eq, semsOfD, dunionCodec, List.map_map]

/-- §5 (U) for a `(dunion)`, in `UAtCan`'s vocabulary. -/
def UAtCanD (d : Name) (opts : List Term) : Prop :=
  UniqueAdmission (semsOfD d opts)

/-- **Row three: `(dunion)`'s (U) is a theorem, not a premise** — §5's "the one union
    whose (U) is discharged by the rule itself". The premises are exactly `Typed.dunion`'s
    two syntactic side conditions, so a derivable `discriminatedUnion` never carries an
    obligation — `Obligations.dunion` is the other half of that claim, and says the
    rule's obligation list has no (U) entry to begin with. Stated here because inside
    `lawful_dunionCodec` it is an argument to a lemma, and a reviewer checking §5's table
    has nothing to point at. -/
theorem uAtCan_dunion {d : Name} {opts : List Term}
    (htags : ∀ t' ∈ opts, (tagsOf d t').Nonempty)
    (hdisj : List.Pairwise (fun a b => ∀ tag ∈ tagsOf d a, tag ∉ tagsOf d b) opts) :
    UAtCanD d opts :=
  uniqueAdmission_byTag (dunion_stamp htags) (List.pairwise_map.mpr hdisj)

/-- **Row four: `(opaque)`'s (U), unconditionally.** `uniqueAdmission_opaque` asks for the
    recursive option's lawfulness; `lawful_opaqCodec` supplies it, so the row has no
    premises at all. It is stated about `opaqCodec` at a fuel rather than about the term
    `opaque` for the reason given above — `denote` of `opaque` is not a sum over one
    list. -/
theorem uAtCan_opaque (lossy : Bool) :
    UniqueAdmission (opaqOptions lossy (opaqCodec fuel lossy)) :=
  uniqueAdmission_opaque fuel lossy (lawful_opaqCodec fuel lossy)

/-! ## What asking the codec buys

    Before the rows above, `adm (.opaq _)` and `admA (.opaq _)` were `⊤` and `κ (.opaq _)`
    is `none`. The retired per-aspect separation offered exactly two routes on each side — a
    disjoint kind, resp. a distinct member, or a disjoint admissible set — and an `opaque`
    option had **neither**. So `union(opaque, c)` was never separable, for any `c` that admits
    anything at all; `Orthogonality.lean`'s `not_orth_opaq_string_lossy` is what remains of
    that fact, decided rather than refuted by hand.

    It was an artifact of the analysis rather than of the semantics: `opaqCodec`'s `N`
    option is `Codec.empty` when `numbers = 'refuse'`, so a non-lossy `opaque` writes no
    number and reads no `N`, and `union(opaque false, number)` really is disjoint on both
    sides. The rows see the writable half of that — and, since they ask the codec rather
    than reading the policy bit, they see the nested half too (`adm_opaq_false_numSet`).
    Nothing below mentions the policy bit; it is the codec that answers. -/

/-- `opaque` admits every string, at either policy — the one absorption that survived the
    semantic row, and the witness the refutations are instantiated at.

    Its predecessor was `adm (.opaq true) v = true` for **every** `v`, and that is no
    longer true: `adm` asks `opaqCodecω`, and a lossy `opaque` still refuses `.num d`
    whenever `Numeral.WF (Double.toDec d)` fails. `Double.toDec` is axiomatized
    (`Domain.lean`) with no such guarantee, so the blanket `⊤` was a claim the row made and
    the codec does not. Nothing downstream wanted it: the refutations below want a value
    *both* options admit, and a string is one. -/
theorem adm_opaq_str (b : Bool) (s : String) : adm (.opaq b) (.str s) = true := by
  show ((opaqCodec (0+1) b).e (.str s)).isSome = true
  rw [opaqCodec_e_str]; rfl

theorem admA_opaq_s (b : Bool) (s : String) : admA (.opaq b) (.s s) = true := by
  show ((opaqCodec (0+1) b).p (.s s)).isSome = true
  rw [opaqCodec_p_s]; rfl

/-- A refusing policy writes no numeral — the fact the old scalar-prefix row carried, now
    read off the codec rather than off a `match`. -/
theorem adm_opaq_false_num (d : Double) : adm (.opaq false) (.num d) = false := by
  show ((opaqCodec (0+1) false).e (.num d)).isSome = false
  rw [opaqCodec_e_num]; rfl

theorem admA_opaq_false_n (x : WFNumeral) : admA (.opaq false) (.n x) = false := by
  show ((opaqCodec (0+1) false).p (.n x)).isSome = false
  rw [opaqCodec_p_n]; rfl

/-- **And the refusal the old row could not state.** A non-lossy `opaque` refuses a *set*
    of numbers too, and a `numSet` is not a `.num`: the row this replaces matched on the
    top constructor and so gave `number` a separation `set(number)` could not have, for no
    reason in the semantics. The semantic row sees it because it does not look — `encSet`
    fails at the first element the element codec refuses, and every element is refused.

    `adm (.set .number)` is itself `⊤` (the empty-container argument), so this does not by
    itself hand `set(number)` a `SepV`; what it removes is the *asymmetry* — the analysis
    of `opaque` no longer stops at depth zero, and any option whose own row is informative
    at a set now meets a matching refusal here. -/
theorem adm_opaq_false_numSet (S : NEFinset Double) :
    adm (.opaq false) (.numSet S) = false := by
  show ((opaqCodec (1+1) false).e (.numSet S)).isSome = false
  rw [opaqCodec_e_numSet]
  cases he : (setCodec (opaqCodec 1 false)).e (.numSet S) with
  | none => rfl
  | some a =>
    obtain ⟨x, hx⟩ := S.2
    have := encSet_elem (c := opaqCodec 1 false) (inj := Value.num) (S := S) (a := a) he x hx
    rw [show (opaqCodec 1 false).e (.num x) = _ from opaqCodec_e_num false 0 x] at this
    exact nomatch this

/-- **`held` of an `opaque` is that `opaque`, on the stored side.** `through`'s `g` is
    total and post-processes a read, so it changes which value comes out and never which
    attributes go in.

    `refine` was stated here alongside it — `admA (.refine (.opaq b) q) = admA (.opaq b)`,
    "no wrapper the language has rescues an `opaque` option's read-side footprint" — and
    that half is **false**. It was true of the old row, which dropped `q`; it is not true of
    the read. `refine_opaq_narrows` below is the general form, and `admA_refine_bot` the
    sharpest instance: a refinement can shrink an `opaque`'s footprint to nothing. -/
theorem admA_held_opaq (b : Bool) (f g : Value → Value) :
    admA (.held (.opaq b) f g) = admA (.opaq b) := rfl

/-- The corrected statement: the footprint is the `opaque`'s **intersected** with `q` of
    what it decodes to. -/
theorem refine_opaq_narrows (b : Bool) (q : Value → Bool) (a : Attr) :
    admA (.refine (.opaq b) q) a
      = (((opaqCodecω b).p a).isSome && refineReads (.opaq b) q a) := rfl

/-- **A refinement by `⊥` reads nothing, at any base.** The row sees it, which is the whole
    of the change: the old row answered `admA t` here and claimed the read was unnarrowed. -/
theorem admA_refine_bot (t : Term) : admA (.refine t (fun _ => false)) = fun _ => false := by
  funext a
  simp only [admA, refineReads]
  cases h : (denote t).p a <;> simp [h]

/-! ## Premises checked at a pair

    Two helpers for instantiating a discharger's `∀ t ∈ opts` and `Pairwise` premises at a
    two-option union. They outlived the discharger they were written for: `Orthogonality.lean`
    uses both, which is why they are here rather than deleted with it. -/

/-- A premise of the form `∀ t ∈ [x, y], P t`, checked at the two options. -/
theorem forall_mem_pair {α : Type} {P : α → Prop} {x y : α} (hx : P x) (hy : P y) :
    ∀ z ∈ [x, y], P z := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hx
  · rcases List.mem_cons.mp hz with rfl | hz
    · exact hy
    · exact absurd hz (by simp)

/-- A pairwise premise over two options, checked at the single unordered pair. -/
theorem pairwise_pair {α : Type} {R : α → α → Prop} {x y : α} (h : R x y) :
    List.Pairwise R [x, y] := by
  refine List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil)
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact h
  · exact absurd hz (by simp)

/-! ## Why one-sided `ident` was never an exemption from (K)

    An earlier §5 stated **(K)** as `∀ i ≠ j. κ(cᵢ) ∩ κ(cⱼ) = ∅ ∨ ident(cᵢ) ∨ ident(cⱼ)`
    and called it *sufficient* for (U). It is not, and the two counterexamples below are
    why no discharger here or in `Orthogonality.lean` carries the `ident` half. §5 now carries the repaired
    form — `ident` on both sides **and** disjoint `adm` — and cites these two as its
    reason, so what follows is the machine-checked half of a correction the doc has
    already made, not a live disagreement with it.

    The withdrawn rule was right about what `ident` buys: attempted admission on a
    `literal` is evidence, where attempted admission on `string` is not. What it dropped
    is that evidence only *resolves* a pair when it is available on **both** sides and
    the two admissible sets are **disjoint**. §5's own worked example,
    `union(literal("A"), literal("B"))`, has both; the rule offered in support of it
    demanded neither. -/

/-- A helper: two options of a two-element union that both admit one value refute (U).
    `hne` separates the options at some other value, so the singleton filter fails. -/
theorem not_uAtCan_pair {t₁ t₂ : Term} {v w : Value} {a : Attr}
    (he : (denote t₁).e v = some a)
    (h₂ : (optionSemOf (denote t₂) (specOf t₂)).admitV v = true)
    (hne : (optionSemOf (denote t₁) (specOf t₁)).admitV w ≠
      (optionSemOf (denote t₂) (specOf t₂)).admitV w) :
    ¬ UAtCan [t₁, t₂] := by
  intro h
  have ho : optionSemOf (denote t₁) (specOf t₁) ∈ semsOf [t₁, t₂] :=
    List.mem_cons_self _ _
  have hfilt := (h _ ho v a (by rw [optionSemOf_c]; exact he)).2
  -- the second option survives the filter too, so the filter cannot be `[o₁]`
  have hmem : optionSemOf (denote t₂) (specOf t₂) ∈
      [optionSemOf (denote t₁) (specOf t₁)] := by
    rw [← hfilt]
    exact List.mem_filter.mpr
      ⟨List.mem_cons_of_mem _ (List.mem_cons_self _ _), h₂⟩
  rcases List.mem_cons.mp hmem with heq | hnil
  · exact hne (congrArg (fun o => OptionSem.admitV o w) heq.symm)
  · exact absurd hnil (by simp)

/-- **One-sided `ident` does not discharge (U).** `union(literal("A"), string)` passes
    the exemption §5 withdrew — `ident(literal("A"))` holds — and violates (U) at the
    value `"A"`, which both options admit. `literal`'s attempt *is* evidence; `string`'s is not, and one
    honest answer does not resolve a pair. -/
theorem not_uAtCan_literal_string :
    ¬ UAtCan [Term.literal .string (.of "A" ∅), Term.string] := by
  have hA : (denote (Term.literal .string (.of "A" ∅))).e (Value.str "A") = some (Attr.s "A") := by
    show (if "A" ∈ ["A"] then some (Attr.s "A") else none) = some (Attr.s "A")
    rw [if_pos (List.mem_cons_self _ _)]
  have hB : (denote (Term.literal .string (.of "A" ∅))).e (Value.str "B") = none := by
    show (if "B" ∈ ["A"] then some (Attr.s "B") else none) = none
    rw [if_neg (by simp)]
  refine not_uAtCan_pair (v := .str "A") (a := Attr.s "A") (w := .str "B") hA rfl ?_
  · show ((denote (Term.literal .string (.of "A" ∅))).e (Value.str "B")).isSome ≠
      ((denote Term.string).e (Value.str "B")).isSome
    rw [hB]
    exact fun h => nomatch h

/-- **Two-sided `ident` does not discharge (U) either.** `ident` propagates through
    `array` (§5's table), so `union(array(literal("A")), array(literal("B")))` has it on
    both sides — and both options admit the empty array, which neither literal ever
    sees. Propagating `ident` through a container does not propagate disjointness of
    the admissible sets: every container admits its empty case. -/
theorem not_uAtCan_array_literals :
    ¬ UAtCan [Term.array (.literal .string (.of "A" ∅)), Term.array (.literal .string (.of "B" ∅))] := by
  refine not_uAtCan_pair (v := .arr []) (a := Attr.l []) (w := .arr [.str "A"])
    rfl rfl ?_
  -- separated one fuel down, where the element codecs are live: `["A"]` is written by
  -- the first option and refused by the second
  show ((match (if "A" ∈ ["A"] then some (Attr.s "A") else none),
      some ([] : List Attr) with
      | some y, some ys => some (y :: ys) | _, _ => none).map Attr.l).isSome ≠
    ((match (if "A" ∈ ["B"] then some (Attr.s "A") else none),
      some ([] : List Attr) with
      | some y, some ys => some (y :: ys) | _, _ => none).map Attr.l).isSome
  rw [if_pos (List.mem_cons_self _ _), if_neg (by simp)]
  exact fun h => nomatch h

/-! ### …and the same union meets the residue the laws actually carry

    `not_uAtCan_array_literals` refutes `UAtCan` at `[]` — a canonical pair of *each*
    option, and one the union never writes, since both admit it and `altCodec` declines
    what it cannot resolve. `UAtAct` (§5, `Soundness.lean`) asks only where the union
    acts, and the same term meets it: every value the union does write is read back by
    the option that wrote it.

    So the two residues are not the same condition, and the gap is not a curiosity — it
    holds `union(array(literal "A"), array(literal "B"))`, which is a schema people write.
    What carries it is that a `literal`'s two halves test one set, so an element the
    neighbouring option declines to *write* is one it declines to *read*. That is exactly
    what `held` breaks (`not_uAtCan_literal_held`), which is why the argument is about
    literals and not about containers in general. -/

/-! `literalCodec` at the string base, in the shape the four lemmas below need.

Named rather than unfolded. ~~literalSCodec~~ used to be a hand-written pair, so `simp
[literalSCodec]` was one step; the unified codec is `Codec.restrict` over `baseCodec`, and
unfolding that inside a `simp_all` with two hypotheses in play runs out of heartbeats — the
`whnf` reaches for `numberCodec`'s `dite` on `Numeral.WF`, which is a string parser. The fix is
the one the other three numeric sites use: state the consequence once, and rewrite with it. -/

theorem literalCodec_string_e (ls : NEFinset String) : ∀ v : Value,
    (literalCodec .string ls).e v
      = (match v with | .str s => if s ∈ ls.1 then some (Attr.s s) else none | _ => none)
  | .str _ => by simp [literalCodec, baseCodec, Codec.restrict, inL, stringCodec]
  | .num _ | .bool _ | .bin _ | .null | .strSet _ | .numSet _ | .binSet _
  | .arr _ | .map _ _ => rfl

theorem literalCodec_string_p (ls : NEFinset String) : ∀ a : Attr,
    (literalCodec .string ls).p a
      = (match a with | .s s => if s ∈ ls.1 then some (Value.str s) else none | _ => none)
  | .s _ => by simp [literalCodec, baseCodec, Codec.restrict, inL, stringCodec]
  | .n _ | .bool _ | .b _ | .null | .ss _ | .ns _ | .bs _ | .l _ | .m _ _ => rfl

/-- §3 `(literal-S)`'s two halves test one set, so a `literal` declines to read the
    attribute it declines to write. -/
theorem literalS_p_none {ls ls' : NEFinset String} {t : Value} {a : Attr}
    (he : (literalCodec .string ls).e t = some a) (hne : (literalCodec .string ls').e t = none) :
    (literalCodec .string ls').p a = none := by
  rw [literalCodec_string_e] at he hne
  cases t <;> simp_all
  obtain ⟨-, rfl⟩ := he
  rw [literalCodec_string_p]
  simp [hne]

/-- …the reading half of the same §3 `(literal-S)` fact. -/
theorem literalS_e_none {ls ls' : NEFinset String} {t : Value} {a : Attr}
    (hp : (literalCodec .string ls).p a = some t) (hne : (literalCodec .string ls').p a = none) :
    (literalCodec .string ls').e t = none := by
  rw [literalCodec_string_p] at hp hne
  cases a <;> simp_all
  obtain ⟨-, rfl⟩ := hp
  rw [literalCodec_string_e]
  simp [hne]

/-- §3 `(array)`'s traversal inherits it: an element the neighbour refuses makes the
    whole list unreadable, at the position the writing traversal already fixed. -/
theorem traverse_literalS_p_none {ls ls' : NEFinset String} {vs : List Value} {as : List Attr}
    (he : traverse (literalCodec .string ls).e vs = some as)
    (hne : traverse (literalCodec .string ls').e vs = none) :
    traverse (literalCodec .string ls').p as = none := by
  cases hres : traverse (literalCodec .string ls').p as with
  | none => rfl
  | some ws =>
    exfalso
    have hall : ∀ v ∈ vs, ((literalCodec .string ls').e v).isSome := by
      intro v hv
      obtain ⟨a, ha, hea⟩ := (traverse_eq_some.mp he).mem_left hv
      obtain ⟨w, -, hpw⟩ := (traverse_eq_some.mp hres).mem_left ha
      cases hev : (literalCodec .string ls').e v with
      | none => rw [literalS_p_none hea hev] at hpw; exact nomatch hpw
      | some _ => rfl
    have hs := traverse_isSome_of_all hall
    rw [hne] at hs
    exact nomatch hs

/-- …and dually, at §3 `(array)`. -/
theorem traverse_literalS_e_none {ls ls' : NEFinset String} {as : List Attr} {vs : List Value}
    (hp : traverse (literalCodec .string ls).p as = some vs)
    (hne : traverse (literalCodec .string ls').p as = none) :
    traverse (literalCodec .string ls').e vs = none := by
  cases hres : traverse (literalCodec .string ls').e vs with
  | none => rfl
  | some ws =>
    exfalso
    have hall : ∀ a ∈ as, ((literalCodec .string ls').p a).isSome := by
      intro a ha
      obtain ⟨v, hv, hpv⟩ := (traverse_eq_some.mp hp).mem_left ha
      obtain ⟨w, -, hew⟩ := (traverse_eq_some.mp hres).mem_left hv
      cases hpa : (literalCodec .string ls').p a with
      | none => rw [literalS_e_none hpv hpa] at hew; exact nomatch hew
      | some _ => rfl
    have hs := traverse_isSome_of_all hall
    rw [hne] at hs
    exact nomatch hs

/-- §3 `(array)` over §3 `(literal-S)`: it refuses on the attribute side whatever it
    refuses on the value side, at the attribute its neighbour wrote. -/
theorem arrayLiteral_p_none {ls ls' : NEFinset String} {t : Value} {a : Attr}
    (he : (arrayCodec (literalCodec .string ls)).e t = some a)
    (hne : (arrayCodec (literalCodec .string ls')).e t = none) :
    (arrayCodec (literalCodec .string ls')).p a = none := by
  cases t with
  | arr vs =>
    simp only [arrayCodec, Option.map_eq_some'] at he
    obtain ⟨as, has, rfl⟩ := he
    simp only [arrayCodec] at hne ⊢
    cases h2 : traverse (literalCodec .string ls').e vs with
    | some _ => rw [h2] at hne; exact nomatch hne
    | none => rw [traverse_literalS_p_none has h2]; rfl
  | _ => exact nomatch he

/-- …and dually, the same §3 pair. -/
theorem arrayLiteral_e_none {ls ls' : NEFinset String} {t : Value} {a : Attr}
    (hp : (arrayCodec (literalCodec .string ls)).p a = some t)
    (hne : (arrayCodec (literalCodec .string ls')).p a = none) :
    (arrayCodec (literalCodec .string ls')).e t = none := by
  cases a with
  | l as =>
    simp only [arrayCodec, Option.map_eq_some'] at hp
    obtain ⟨vs, hvs, rfl⟩ := hp
    simp only [arrayCodec] at hne ⊢
    cases h2 : traverse (literalCodec .string ls').p as with
    | some _ => rw [h2] at hne; exact nomatch hne
    | none => rw [traverse_literalS_e_none hvs h2]; rfl
  | _ => exact nomatch hp

/-- The two §5 options are distinct — needed only to read a singleton filter back. -/
theorem optionSem_arrayLiterals_ne :
    OptionSem.byAttempt (arrayCodec (literalCodec .string (.of "A" ∅))) ≠
      OptionSem.byAttempt (arrayCodec (literalCodec .string (.of "B" ∅))) := by
  intro h
  have := congrArg (fun o => o.admitV (.arr [.str "A"])) h
  simp [OptionSem.byAttempt, arrayCodec, traverse, literalCodec, baseCodec, Codec.restrict, inL, stringCodec] at this

/-- **§5's two residues, separated at a schema people write.**
    `union(array(literal "A"), array(literal "B"))` fails `UAtCan`
    (`not_uAtCan_array_literals`) and meets `UAtAct` — so the soundness theorem covers it
    once (U) is asked where the union acts rather than at every option's canonicals. The
    union declines the empty array, and every value it does write round-trips through the
    option that wrote it. -/
theorem uAtAct_array_literals :
    UAtAct [Term.array (.literal .string (.of "A" ∅)), Term.array (.literal .string (.of "B" ∅))] := by
  show UniqueBothWays [OptionSem.byAttempt (arrayCodec (literalCodec .string (.of "A" ∅))),
    OptionSem.byAttempt (arrayCodec (literalCodec .string (.of "B" ∅)))]
  have lawA : LawfulCore (arrayCodec (literalCodec .string (.of "A" ∅))) :=
    lawfulCore_arrayCodec (lawful_literalCodec _ _).core
  have lawB : LawfulCore (arrayCodec (literalCodec .string (.of "B" ∅))) :=
    lawfulCore_arrayCodec (lawful_literalCodec _ _).core
  refine ⟨?_, ?_⟩
  · intro o ho t a hf he
    rcases List.mem_cons.mp ho with rfl | ho'
    · obtain ⟨-, hB⟩ := filter_pair_left_inv optionSem_arrayLiterals_ne hf
      rw [OptionSem.byAttempt_admitV] at hB
      have hBe : (arrayCodec (literalCodec .string (.of "B" ∅))).e t = none := by
        cases h : (arrayCodec (literalCodec .string (.of "B" ∅))).e t with
        | none => rfl
        | some _ => rw [h] at hB; exact nomatch hB
      refine filter_pair_left ?_ ?_
      · rw [OptionSem.byAttempt_admitA, lawA.retract he]; rfl
      · rw [OptionSem.byAttempt_admitA, arrayLiteral_p_none he hBe]; rfl
    · rcases List.mem_singleton.mp ho' with rfl
      obtain ⟨hA, -⟩ := filter_pair_right_inv optionSem_arrayLiterals_ne hf
      rw [OptionSem.byAttempt_admitV] at hA
      have hAe : (arrayCodec (literalCodec .string (.of "A" ∅))).e t = none := by
        cases h : (arrayCodec (literalCodec .string (.of "A" ∅))).e t with
        | none => rfl
        | some _ => rw [h] at hA; exact nomatch hA
      refine filter_pair_right ?_ ?_
      · rw [OptionSem.byAttempt_admitA, arrayLiteral_p_none he hAe]; rfl
      · rw [OptionSem.byAttempt_admitA, lawB.retract he]; rfl
  · intro o ho a t a' hf hp he
    rcases List.mem_cons.mp ho with rfl | ho'
    · obtain ⟨-, hB⟩ := filter_pair_left_inv optionSem_arrayLiterals_ne hf
      rw [OptionSem.byAttempt_admitA] at hB
      have hBp : (arrayCodec (literalCodec .string (.of "B" ∅))).p a = none := by
        cases h : (arrayCodec (literalCodec .string (.of "B" ∅))).p a with
        | none => rfl
        | some _ => rw [h] at hB; exact nomatch hB
      have h' : (arrayCodec (literalCodec .string (.of "A" ∅))).e t = some a' := he
      refine filter_pair_left ?_ ?_
      · rw [OptionSem.byAttempt_admitV, h']; rfl
      · rw [OptionSem.byAttempt_admitV, arrayLiteral_e_none hp hBp]; rfl
    · rcases List.mem_singleton.mp ho' with rfl
      obtain ⟨hA, -⟩ := filter_pair_right_inv optionSem_arrayLiterals_ne hf
      rw [OptionSem.byAttempt_admitA] at hA
      have hAp : (arrayCodec (literalCodec .string (.of "A" ∅))).p a = none := by
        cases h : (arrayCodec (literalCodec .string (.of "A" ∅))).p a with
        | none => rfl
        | some _ => rw [h] at hA; exact nomatch hA
      have h' : (arrayCodec (literalCodec .string (.of "B" ∅))).e t = some a' := he
      refine filter_pair_right ?_ ?_
      · rw [OptionSem.byAttempt_admitV, arrayLiteral_e_none hp hAp]; rfl
      · rw [OptionSem.byAttempt_admitV, h']; rfl

/-- Both counterexamples are `ident` on the side(s) the withdrawn exemption appealed to
    — so it admitted them outright, rather than excluding them by a side condition. The
    `adm`-disjointness §5 now demands is what excludes them. -/
example : ident (.literal .string (.of "A" ∅)) = true := rfl
example : ident (.array (.literal .string (.of "A" ∅))) = true := rfl
example : ident (.array (.literal .string (.of "B" ∅))) = true := rfl

/-! ## Why (D) does not discharge the readable side either

    An earlier §5 listed **(D)** — incomparable held sets — as a discharger of (U)'s
    readable side, and held that stating it as genuine *disjointness* would be sound
    though needlessly strict. Disjointness is not sound either: held sets are sets of
    **values**, (U)'s readable side quantifies over **attributes**, and `held` is exactly
    the term that separates the two. Its adapter relabels, so two options can hold
    disjoint sets of values and still read one attribute — each to its own value. §5 now
    says this, and (D) is a well-formedness condition on the `T` index rather than a
    discharger; the witness below is what settled it.

    That witness is `union(literal("A"), held(literal("A"), f, g))` with `f` and `g`
    swapping `"B"` for `"A"`. Its held sets are `{"A"}` and `{"B"}` — disjoint, so (D)
    passes in the strongest form ever proposed for it — and both options read the
    attribute `S "A"`, the first to `"A"` and the second to `"B"`. What decides the
    readable side is a condition on stored attributes: distinct members, or disjoint
    `admA`. -/

/-- (D) in its held-set form, as the disjointness §5 proposes: no value is held by two
    options. Stated so the counterexample below can be about it.

    This is *not* the rule's premise: `(union)` carries `DIncomp` (`Typing.lean`), §5's
    incomparability. `DDisj` is the strictly stronger reading §5 considered and withdrew,
    and it is here only to be refuted — the witness below satisfies it and still fails
    (U). -/
def DDisj (Tx Ty : Held) : Prop := ∀ v, Tx v → ¬ Ty v

/-- The relabelling adapter: `"B"` on the outside is `"A"` on the inside. -/
def fRel : Value → Value := fun v => match v with | .str "B" => .str "A" | _ => .null

/-- Its inverse on the carriers. -/
def gRel : Value → Value := fun v => match v with | .str "A" => .str "B" | _ => .null

/-- `held(literal("A"), fRel, gRel)` — holds `{"B"}`, stores it as `S "A"`. -/
def tRel : Term := .held (.literal .string (.of "A" ∅)) fRel gRel

/-- The attribute-side twin of `not_uAtCan_pair`. -/
theorem not_uAtCan_pair_A {t₁ t₂ : Term} {v w : Value} {a : Attr}
    (he : (denote t₁).e v = some a)
    (h₂ : (optionSemOf (denote t₂) (specOf t₂)).admitA a = true)
    (hne : (optionSemOf (denote t₁) (specOf t₁)).admitV w ≠
      (optionSemOf (denote t₂) (specOf t₂)).admitV w) :
    ¬ UAtCan [t₁, t₂] := by
  intro h
  have ho : optionSemOf (denote t₁) (specOf t₁) ∈ semsOf [t₁, t₂] :=
    List.mem_cons_self _ _
  have hfilt := (h _ ho v a (by rw [optionSemOf_c]; exact he)).1
  have hmem : optionSemOf (denote t₂) (specOf t₂) ∈
      [optionSemOf (denote t₁) (specOf t₁)] := by
    rw [← hfilt]
    exact List.mem_filter.mpr
      ⟨List.mem_cons_of_mem _ (List.mem_cons_self _ _), h₂⟩
  rcases List.mem_cons.mp hmem with heq | hnil
  · exact hne (congrArg (fun o => OptionSem.admitV o w) heq.symm)
  · exact absurd hnil (by simp)

/-- Both options are derivable, and their held sets are disjoint — so this really is a
    union (D) admits, in the disjointness form §5 once proposed and withdrew. -/
theorem typed_tRel :
    Typed tRel (fun v => ∃ s, s ∈ ["A"] ∧ fRel v = .str s) (some .S) := by
  refine Typed.held (I := fun w => ∃ s, s ∈ ["A"] ∧ w = .str s) ?_
  have h := Typed.literal .string (.of "A" ∅)
  have hT : HLit .string (.of "A" ∅) = fun w => ∃ s, s ∈ ["A"] ∧ w = Value.str s := by
    funext w; simp [HLit, NEFinset.of]
  rw [hT] at h
  exact h

theorem dDisj_tRel :
    DDisj (fun v => ∃ s, s ∈ ["A"] ∧ v = .str s)
      (fun v => ∃ s, s ∈ ["A"] ∧ fRel v = .str s) := by
  rintro v ⟨s, hs, rfl⟩ ⟨s', hs', hf⟩
  -- `v = "A"`, so `fRel v = null`, which is no string
  have : s = "A" := by simpa using hs
  subst this
  exact nomatch hf

/-- **(D) does not discharge the readable side.** Disjoint held sets, and both options
    admit the attribute `S "A"` — the first reading it to `"A"`, the second to `"B"`. -/
theorem not_uAtCan_literal_held :
    ¬ UAtCan [Term.literal .string (.of "A" ∅), tRel] := by
  have hA : (denote (Term.literal .string (.of "A" ∅))).e (Value.str "A") = some (Attr.s "A") := by
    show (if "A" ∈ ["A"] then some (Attr.s "A") else none) = some (Attr.s "A")
    rw [if_pos (List.mem_cons_self _ _)]
  refine not_uAtCan_pair_A (v := .str "A") (a := Attr.s "A") (w := .str "A") hA ?_ ?_
  · show (((if "A" ∈ ["A"] then some (Value.str "A") else none).map gRel)).isSome = true
    rw [if_pos (List.mem_cons_self _ _)]
    rfl
  · show ((denote (Term.literal .string (.of "A" ∅))).e (Value.str "A")).isSome ≠
      ((denote (Term.literal .string (.of "A" ∅))).e (fRel (Value.str "A"))).isSome
    rw [hA]
    show true ≠ ((denote (Term.literal .string (.of "A" ∅))).e Value.null).isSome
    exact fun h => nomatch h


end Calculus
