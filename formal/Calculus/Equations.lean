import Calculus.Soundness
import Calculus.Denoteω

/-!
# §6 — Equations

Which rewrites preserve the pair. `≡` is §6's own reading: the same held set, the same
member, and `e` and `p` agreeing everywhere both are defined.

All eleven of §6's "Hold" rows are proved here. Two of them are cited elsewhere as
load-bearing and came first:

* `nullable(nullable(c)) ≡ nullable(c)` — §6 gives the reason the proof uses, that the
  value language has one null, and the model bears it out in the strongest form: `e` and
  `p` are *equal* on the nose, not merely agreeing. §3's separate point stands
  unchanged — null-honesty is what makes each `nullable` lawful, and so what makes the
  idempotence lawful rather than lucky; it is just not what the rewrite itself needs.
* `union(c₁ … cₙ) ≡ union(c_σ(1) … c_σ(n))` — §5 leans on this for "declaration order is
  never consulted". Proved in its generating case, the adjacent transposition, since
  those generate every permutation.

The remaining rows: `held`'s identity and composition, `refine`'s meet and its full case,
`legacy` with its own reading (and `≈` on `Can(c)`), `union` of one, and the member
preservation of the three codec wrappers.

The last row, `union` associativity, is the table's only *conditional* one — and it turns
out not to need its conditions. See the section below for why, and
`Refutations.not_eq_altCodec_assoc` for the behavioural difference `≡` is blind to.

The "Do not hold" table is settled in `Refutations.lean`. §6 is complete.
-/

namespace Calculus

/-- §6's `≡`. Note it is *not* equality of the pair: `e` and `p` need only agree where
    both are defined, which is what lets a rewrite shrink a domain. -/
structure Codec.Equiv (c d : Codec) : Prop where
  /-- The same held set. -/
  heldSet : ∀ v, c.T v ↔ d.T v
  /-- The same member. -/
  member : c.μ = d.μ
  /-- `e` agrees wherever both are defined. -/
  writes : ∀ {v a a'}, c.e v = some a → d.e v = some a' → a = a'
  /-- `p` agrees wherever both are defined. -/
  reads : ∀ {a v v'}, c.p a = some v → d.p a = some v' → v = v'

theorem Codec.Equiv.refl (c : Codec) : Codec.Equiv c c :=
  ⟨fun _ => Iff.rfl, rfl, fun h h' => Option.some.inj (h.symm.trans h'),
    fun h h' => Option.some.inj (h.symm.trans h')⟩

/-- There is no `Codec.Equiv.trans`, and the omission is not an oversight: `≡` compares
    `e` and `p` only *where both are defined*, so a codec that writes and reads nowhere is
    `≡` to everything and chains two codecs that disagree outright. Refuted as
    `Refutations.not_equiv_trans`, with all three codecs `Lawful` and on their `Carrier`.
    §6 is a table of rewrites, each proved on its own; it is not a congruence to reason
    in transitively. -/
theorem Codec.Equiv.symm {c d : Codec} (h : Codec.Equiv c d) : Codec.Equiv d c :=
  ⟨fun v => (h.heldSet v).symm, h.member.symm,
    fun hd hc => (h.writes hc hd).symm, fun hd hc => (h.reads hc hd).symm⟩

/-! ## §6 at term level — the translation table, written down

`FIDELITY.md` §3 records a level mismatch inside §6: the **Hold** rows are stated here about
*combinators* (`through`, `restrict`, `extendRead`, `orNull`, `altCodec`, …) while the
**Do not hold** rows in `Refutations.lean` are stated about *terms*. Checking a Hold row
against the specification therefore needed an eight-entry translation, five of whose entries
share no substring with the term they translate, and that table was written down nowhere.

Here it is, as theorems. Each is `rfl` — `denoteω` dispatches straight onto the combinator —
so nothing is proved by these except the correspondence itself, which is the point: a
reviewer holding §6's table can now land on the combinator without knowing the codebase.

The term-level twins of the Hold rows follow each row's combinator statement, so both halves
of §6 can be read in one language. -/

section Bridge

theorem denoteω_set (t : Term) : denoteω (.set t) = setCodec (denoteω t) := rfl
theorem denoteω_array (t : Term) : denoteω (.array t) = arrayCodec (denoteω t) := rfl
theorem denoteω_record (t : Term) : denoteω (.record t) = recordCodec (denoteω t) := rfl

/-- `held` denotes `through` — the entry that reads least like its term. -/
theorem denoteω_held (t : Term) (f g : Value → Value) :
    denoteω (.held t f g) = (denoteω t).through f g := rfl

/-- `refine` denotes `restrict`. -/
theorem denoteω_refine (t : Term) (q : Value → Bool) :
    denoteω (.refine t q) = (denoteω t).restrict q := rfl

/-- `legacy` denotes `extendRead`. -/
theorem denoteω_legacy (t : Term) (r : Attr → Option Value) :
    denoteω (.legacy t r) = (denoteω t).extendRead r := rfl

/-- `nullable` denotes `orNull`. -/
theorem denoteω_nullable (t : Term) : denoteω (.nullable t) = (denoteω t).orNull := rfl

/-- `union` denotes `altCodec`, over the options' semantics and their unanimous member. -/
theorem denoteω_union (opts : List Term) :
    denoteω (.union opts) =
      altCodec (denoteωOpts opts) (unanimous (denoteωMems opts)) := rfl

/-- `discriminatedUnion` denotes `dunionCodec`. -/
theorem denoteω_dunion (d : Name) (opts : List Term) :
    denoteω (.dunion d opts) = dunionCodec d (denoteωTags d opts) := rfl

/-- `opaque` denotes `opaqCodecω` — the fuel-free one, which is why §5's discharger table has
    a row about `opaqCodec` at a fuel and a reason rather than a term-level twin. -/
theorem denoteω_opaq (lossy : Bool) : denoteω (.opaq lossy) = opaqCodecω lossy := rfl

/-- `object` denotes `objectCodec`. -/
theorem denoteω_object (fields : List (Name × Field)) (rest : Rest) :
    denoteω (.object fields rest) = objectCodec (denoteωF fields) (denoteωR rest) := rfl

end Bridge

/-! ## `nullable` is idempotent -/

/-- The two pairs are not merely `≡` but equal, on both halves: the value language has
    one null, so the outer `𝟙` is the only one anything is ever written to or read
    from. -/
theorem orNull_e_idem (c : Codec) : c.orNull.orNull.e = c.orNull.e := by
  funext v
  cases v <;> rfl

theorem orNull_p_idem (c : Codec) : c.orNull.orNull.p = c.orNull.p := by
  funext a
  cases a <;> rfl

/-- §6: `nullable(nullable(c)) ≡ nullable(c)`. -/
theorem equiv_orNull_idem (c : Codec) : Codec.Equiv c.orNull.orNull c.orNull := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro v
    constructor
    · rintro (h | h)
      · exact h
      · exact Or.inr h
    · exact Or.inl
  · intro v a a' h h'
    rw [orNull_e_idem] at h
    exact Option.some.inj (h.symm.trans h')
  · intro a v v' h h'
    rw [orNull_p_idem] at h
    exact Option.some.inj (h.symm.trans h')

private theorem filterV_null {c : Codec} :
    [OptionSem.byAttempt c, nullOption].filter (·.admitV .null)
      = (if (c.e .null).isSome then [OptionSem.byAttempt c, nullOption] else [nullOption]) := by
  cases hc : (c.e Value.null) <;> simp [OptionSem.byAttempt, nullCodec, hc, List.filter]

private theorem filterV_ne {c : Codec} {v : Value} (hv : v ≠ .null) :
    [OptionSem.byAttempt c, nullOption].filter (·.admitV v)
      = (if (c.e v).isSome then [OptionSem.byAttempt c] else []) := by
  cases v <;> cases hc : c.e _ <;> simp_all [OptionSem.byAttempt, nullCodec, List.filter]

private theorem filterA_null {c : Codec} :
    [OptionSem.byAttempt c, nullOption].filter (·.admitA .null)
      = (if (c.p .null).isSome then [OptionSem.byAttempt c, nullOption] else [nullOption]) := by
  cases hc : (c.p Attr.null) <;> simp [OptionSem.byAttempt, nullCodec, hc, List.filter]

private theorem filterA_ne {c : Codec} {a : Attr} (ha : a ≠ .null) :
    [OptionSem.byAttempt c, nullOption].filter (·.admitA a)
      = (if (c.p a).isSome then [OptionSem.byAttempt c] else []) := by
  cases a <;> cases hc : c.p _ <;> simp_all [OptionSem.byAttempt, nullCodec, List.filter]

/-! ## `nullable` *is* `union` with the null point — at `≡`, and only at `≡`

§3 of the specification calls `nullable(c)` "structurally the two-option union
`union(c, ⟨NULL⟩-point)`" — that sentence is still there. What used to follow it is not:
§3 said the two "coincide under honesty, which is why the precedence is harmless."

Mechanizing that sentence showed it wrong in both directions, and the correction is
sharper than the claim, so §3 now states the dichotomy instead ("`nullable` is either the
union or the identity"). This section is what changed it:

* the **equivalence needs no premise at all** — not honesty, not lawfulness
  (`equiv_orNull_altCodec`). `≡` compares the pairs where both are defined, and the only
  place the two disagree is where the union is *un*defined;
* the **equality needs more than honesty**: the base must not touch the null point at
  all (`orNull_eq_altCodec`). Honesty does not give that, and the witness is not exotic —
  it is `nullable(nullable(c))`, the very term §6's idempotence row is about, where both
  options admit `null` and the union therefore refuses (`orNull_ne_altCodec`).

What the precedence buys, however, is nothing. `orNull_eq_self` below closes the
dichotomy: where `nullable(c)` differs from `union(c, ⟨NULL⟩-point)` — that is, where the
base already handles null — the wrapper is *equal to its own base*. So the two
constructions never disagree on a codec anyone would write: either `nullable` is the
union, or it is the identity. The only term outside both is `nullable(null)`, member `⊤`
over the `NULL` point, which is of no use. -/

/-- The equivalence, unconditionally. -/
theorem equiv_orNull_altCodec (c : Codec) :
    Codec.Equiv c.orNull (altCodec [.byAttempt c, nullOption] none) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro v
    refine ⟨?_, ?_⟩
    · rintro (hT | rfl)
      · exact ⟨.byAttempt c, List.mem_cons_self _ _, hT⟩
      · exact ⟨nullOption, by simp, rfl⟩
    · rintro ⟨o, ho, hT⟩
      rcases List.mem_cons.mp ho with rfl | ho'
      · exact .inl hT
      · rcases List.mem_cons.mp ho' with rfl | h
        · exact .inr hT
        · exact absurd h (by simp)
  · intro v a a' h h'
    obtain ⟨o, hf, hoe⟩ := altCodec_e.mp h'
    rcases orNull_e.mp h with ⟨rfl, rfl⟩ | ⟨hv, hce⟩
    · rw [filterV_null] at hf
      split at hf
      · exact nomatch hf
      · cases hf; exact Option.some.inj hoe
    · rw [filterV_ne hv, if_pos (by rw [hce]; rfl)] at hf
      cases hf
      exact Option.some.inj (hce.symm.trans hoe)
  · intro a v v' h h'
    obtain ⟨o, hf, hop⟩ := altCodec_p.mp h'
    rcases orNull_p.mp h with ⟨rfl, rfl⟩ | ⟨ha, hcp⟩
    · rw [filterA_null] at hf
      split at hf
      · exact nomatch hf
      · cases hf; exact Option.some.inj hop
    · rw [filterA_ne ha, if_pos (by rw [hcp]; rfl)] at hf
      cases hf
      exact Option.some.inj (hcp.symm.trans hop)

/-- The equality, and the premise it really needs: the base does not touch the null
    point. Strictly stronger than null-honesty — honesty constrains which *attribute* a
    value writes to, and says nothing about whether `c` writes `null` at all. -/
theorem orNull_eq_altCodec {c : Codec} (he : c.e .null = none) (hp : c.p .null = none) :
    c.orNull = altCodec [.byAttempt c, nullOption] none := by
  refine Codec.ext ?_ rfl ?_ ?_
  · funext v
    refine propext ⟨?_, ?_⟩
    · rintro (hT | rfl)
      · exact ⟨.byAttempt c, List.mem_cons_self _ _, hT⟩
      · exact ⟨nullOption, by simp, rfl⟩
    · rintro ⟨o, ho, hT⟩
      rcases List.mem_cons.mp ho with rfl | ho'
      · exact .inl hT
      · rcases List.mem_cons.mp ho' with rfl | h
        · exact .inr hT
        · exact absurd h (by simp)
  · funext v
    cases v <;> simp [Codec.orNull, altCodec, OptionSem.byAttempt, nullCodec, he,
      List.filter] <;> cases hc : c.e _ <;> simp_all
  · funext a
    cases a <;> simp [Codec.orNull, altCodec, OptionSem.byAttempt, nullCodec, hp,
      List.filter] <;> cases hc : c.p _ <;> simp_all

/-- …and null-honesty is not enough for it. `nullable(string)` is lawful and honest in
    both directions, and `nullable` of it answers at `null` where the union refuses —
    both options admit, so (U) fails there and `altCodec` is undefined. -/
theorem orNull_ne_altCodec :
    (stringCodec.orNull).orNull.e .null = some .null ∧
    (altCodec [.byAttempt stringCodec.orNull, nullOption] none).e .null = none ∧
    (stringCodec.orNull).orNull ≠ altCodec [.byAttempt stringCodec.orNull, nullOption] none :=
  ⟨rfl, rfl, fun h => by
    have : (stringCodec.orNull).orNull.e .null
        = (altCodec [.byAttempt stringCodec.orNull, nullOption] none).e .null := by rw [h]
    exact nomatch this⟩

/-- **`nullable` is either the union or the identity.** If the base already handles the
    null point, the wrapper adds nothing at all — not `≡`, *equal*. Together with
    `orNull_eq_altCodec` (the base does not handle it: the wrapper *is* the union) this
    is a dichotomy, and it is what makes `nullable` redundant wherever it differs from
    `union(c, null)`:

    * `nullable(opaque) = opaque` — `opaque` offers the `NULL` point among its options;
    * `nullable(nullable(c)) = nullable(c)` — §6's idempotence row, as an equation
      rather than an equivalence;
    * `nullable(union(…, null)) = union(…, null)`.

    The `μ = none` premise is what the wrapper itself always satisfies, so the dichotomy
    is closed under nesting. The one term it does not reach is `nullable(null)` — member
    `⊤` over the `NULL` point, distinct from both `null` and any union, and of no use. -/
theorem orNull_eq_self {c : Codec} (hl : Lawful c) (hc : Carrier c)
    (hr : ∀ a v, c.p a = some v → v = .null → a = .null)
    (hn : (c.e .null).isSome) (hμ : c.μ = none) : c.orNull = c := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hn
  obtain rfl : a = .null := hr a .null (hl.retract ha) rfl
  have hp : c.p .null = some .null := hl.retract ha
  refine Codec.ext ?_ hμ.symm ?_ ?_
  · funext v
    refine propext ⟨?_, ?_⟩
    · rintro (h | rfl)
      · exact h
      · exact hc.domE ha
    · exact .inl
  · funext v; cases v <;> simp [Codec.orNull, ha]
  · funext x; cases x <;> simp [Codec.orNull, hp]

/-! ## `union` is commutative

    Resolution is unique admission, never declaration order (§5) — so swapping two
    options changes nothing. Proved for an adjacent swap, which generates every
    permutation. -/

/-- The filter of a swapped pair is the swap of the filter, and in the one case that
    matters — a singleton, where `altCodec` acts — the two are equal. -/
theorem filter_swap_singleton {α : Type} (P : α → Bool) (x y : α) (l : List α) :
    ∀ {o}, (x :: y :: l).filter P = [o] → (y :: x :: l).filter P = [o] := by
  intro o h
  cases hx : P x <;> cases hy : P y <;> simp only [List.filter, hx, hy] at h ⊢
  · exact h
  · exact h
  · exact h
  · exact nomatch h

/-- §6: `union(c₁, c₂, …) ≡ union(c₂, c₁, …)`. The pair is literally the same on every
    input at which either side is defined, since `altCodec` reads the option list only
    through "exactly one admits". -/
theorem equiv_altCodec_swap (o₁ o₂ : OptionSem) (os : List OptionSem)
    (μA : Option Member) :
    Codec.Equiv (altCodec (o₁ :: o₂ :: os) μA) (altCodec (o₂ :: o₁ :: os) μA) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro v
    constructor <;> rintro ⟨o, ho, hT⟩ <;>
      · rcases List.mem_cons.mp ho with rfl | ho'
        · exact ⟨o, List.mem_cons_of_mem _ (List.mem_cons_self _ _), hT⟩
        · rcases List.mem_cons.mp ho' with rfl | ho''
          · exact ⟨o, List.mem_cons_self _ _, hT⟩
          · exact ⟨o, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ho''), hT⟩
  · intro v a a' h h'
    obtain ⟨o, hf, hoe⟩ := altCodec_e.mp h
    obtain ⟨o', hf', hoe'⟩ := altCodec_e.mp h'
    rw [filter_swap_singleton _ _ _ _ hf] at hf'
    obtain rfl : o = o' := by simpa using hf'
    exact Option.some.inj (hoe.symm.trans hoe')
  · intro a v v' h h'
    obtain ⟨o, hf, hop⟩ := altCodec_p.mp h
    obtain ⟨o', hf', hop'⟩ := altCodec_p.mp h'
    rw [filter_swap_singleton _ _ _ _ hf] at hf'
    obtain rfl : o = o' := by simpa using hf'
    exact Option.some.inj (hop.symm.trans hop')

/-! ## `held` is an identity, and composes

§6's first two rows. The second is the one worth stating carefully: the writing halves
compose in the order written and the reading halves compose *reversed*, which is what
"note the reversal on the reading half" means and what the model makes literal. -/

/-- §6: `held(c, id, id) ≡ c`. -/
theorem equiv_through_id (c : Codec) : Codec.Equiv (c.through id id) c := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩
  · exact fun h h' => Option.some.inj ((through_e.mp h).symm.trans h')
  · intro a v v' h h'
    obtain ⟨w, hw, rfl⟩ := through_p.mp h
    exact Option.some.inj (hw.symm.trans h')

/-- §6: `held(held(c, f, g), f′, g′) ≡ held(c, f ∘ f′, g′ ∘ g)`. -/
theorem equiv_through_comp (c : Codec) (f g f' g' : Value → Value) :
    Codec.Equiv ((c.through f g).through f' g') (c.through (f ∘ f') (g' ∘ g)) := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩
  · exact fun h h' => Option.some.inj (h.symm.trans h')
  · intro a v v' h h'
    obtain ⟨w, hw, rfl⟩ := through_p.mp h
    obtain ⟨x, hx, rfl⟩ := through_p.mp hw
    obtain ⟨y, hy, rfl⟩ := through_p.mp h'
    rw [hx] at hy
    cases hy
    rfl

/-! ## `refine` — prisms meet, and a full one is no refinement -/

/-- §6: `refine(refine(c, q), q′) ≡ refine(c, q ∩ q′)`. -/
theorem equiv_restrict_meet (c : Codec) (q q' : Value → Bool) :
    Codec.Equiv ((c.restrict q).restrict q') (c.restrict (fun v => q v && q' v)) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro v
    constructor
    · rintro ⟨⟨hT, hq⟩, hq'⟩
      exact ⟨hT, by simp [hq, hq']⟩
    · rintro ⟨hT, hqq⟩
      simp only [Bool.and_eq_true] at hqq
      exact ⟨⟨hT, hqq.1⟩, hqq.2⟩
  · intro v a a' h h'
    obtain ⟨-, hin⟩ := restrict_e.mp h
    exact Option.some.inj ((restrict_e.mp hin).2.symm.trans (restrict_e.mp h').2)
  · intro a v v' h h'
    obtain ⟨hin, -⟩ := restrict_p.mp h
    exact Option.some.inj ((restrict_p.mp hin).1.symm.trans (restrict_p.mp h').1)

/-- §6: `refine(c, T) ≡ c` for `⊢ c : T ⇝ μ`. A refinement admitting everything the codec
    holds is no refinement — and note the premise needed is only that `q` agrees with `T`,
    not that the pair is on its carrier: `≡` compares `e` and `p` where *both* are defined,
    so a `q` that rejects something outside `T` costs nothing. -/
theorem equiv_restrict_full (c : Codec) (q : Value → Bool)
    (hq : ∀ v, c.T v ↔ q v = true) : Codec.Equiv (c.restrict q) c := by
  refine ⟨fun v => ⟨fun h => h.1, fun h => ⟨h, (hq v).mp h⟩⟩, rfl, ?_, ?_⟩
  · exact fun h h' => Option.some.inj ((restrict_e.mp h).2.symm.trans h')
  · exact fun h h' => Option.some.inj ((restrict_p.mp h).1.symm.trans h')

/-! ## `legacy` with its own reading -/

/-- The pair is not merely `≡` but equal: both branches of `extendRead`'s match give
    `c.p a`, so re-reading through `c`'s own `p` adds nothing at all. -/
theorem extendRead_self_p (c : Codec) : (c.extendRead c.p).p = c.p := by
  funext a
  show (match c.p a with | some v => some v | none => c.p a) = c.p a
  cases c.p a <;> rfl

/-- §6: `legacy(c, p_c) ≡ c`. -/
theorem equiv_extendRead_self (c : Codec) : Codec.Equiv (c.extendRead c.p) c := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩
  · intro v a a' h h'
    exact Option.some.inj (h.symm.trans h')
  · intro a v v' h h'
    rw [extendRead_self_p] at h
    exact Option.some.inj (h.symm.trans h')

/-- §6: `legacy(c, r) ≈ c` on `Can(c)`. A migration differs from the current encoding only
    *off* the canonical set — on it, `(R)` has already made `c.p` succeed, so `r` is never
    consulted. The premise is exactly `(R)`, which is why this row is about lawful codecs
    and not about `extendRead` in general. -/
theorem extendRead_eq_on_can (c : Codec) (r : Attr → Option Value) (hc : Lawful c)
    {a : Attr} (ha : Can c a) : (c.extendRead r).p a = c.p a := by
  obtain ⟨v, hv⟩ := ha
  have hp : c.p a = some v := hc.retract hv
  show (match c.p a with | some v => some v | none => r a) = c.p a
  rw [hp]

/-! ## `union` of one -/

/-- §6: `union(c) ≡ c`. Choice of one: the filter is `[o]` exactly when `o` admits, and
    `altCodec` then reads `o`'s own pair. Where `o` does not admit, the union is undefined
    and `≡` asks nothing — which is the clause that makes this row true for a `byNames`
    option as well as a `byAttempt` one. -/
theorem equiv_altCodec_single (o : OptionSem) :
    Codec.Equiv (altCodec [o] o.c.μ) o.c := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro v
    constructor
    · rintro ⟨x, hx, hT⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hT
      · exact absurd hx' (by simp)
    · exact fun h => ⟨o, List.mem_cons_self _ _, h⟩
  · intro v a a' h h'
    obtain ⟨x, hf, hxe⟩ := altCodec_e.mp h
    obtain rfl : x = o := by simpa using (mem_of_filter_eq_singleton hf).1
    exact Option.some.inj (hxe.symm.trans h')
  · intro a v v' h h'
    obtain ⟨x, hf, hxp⟩ := altCodec_p.mp h
    obtain rfl : x = o := by simpa using (mem_of_filter_eq_singleton hf).1
    exact Option.some.inj (hxp.symm.trans h')

/-! ## Wrappers preserve the member

§6's last "Hold" row, `μ(w(c)) = μ(c)` for `w ∈ {held, refine, legacy, optional,
fallback}`, and §4's reason index keys stay stable under refactoring.

Three of the five are codec wrappers. The other two are **fields**, and this file used to
say their half of the row was "the stratification of §4 and not a statement about
`Codec.μ` at all". That was an evasion: §4 says in as many words that *a field carries a
member like anything else*, and `FieldSem.codec` is where the model puts it. Stated
through that accessor the two rows are `rfl` — which is the honest form of the claim
rather than a reason to skip it, and it is what makes the row five of five. -/

theorem through_μ (c : Codec) (f g : Value → Value) : (c.through f g).μ = c.μ := rfl

theorem restrict_μ (c : Codec) (q : Value → Bool) : (c.restrict q).μ = c.μ := rfl

theorem extendRead_μ (c : Codec) (r : Attr → Option Value) :
    (c.extendRead r).μ = c.μ := rfl

/-- §4 `(opt)`: an optional attribute is still stored somewhere, and where is the
    subterm's member. -/
theorem optional_μ (den : Term → Codec) (t : Term) :
    (fieldSemOf den (.optional t)).codec.μ = (den t).μ := rfl

/-- §4 `(fallback)`: the stand-in is written through the same codec, so the member is
    the subterm's too. -/
theorem fallback_μ (den : Term → Codec) (t : Term) (v : Value) :
    (fieldSemOf den (.fallback t v)).codec.μ = (den t).μ := rfl

/-! ## `union` is associative

§6's last row, and the only conditional one in the table: "associative, where both sides
satisfy (D) and (K) — and only on inputs satisfying (U): an ambiguity *inside* the nested
option fails locally on the left, where the outer union may still resolve, and globally on
the right."

The behaviour is exactly as described. What the mechanization adds is that under §6's own
`≡` the conditions are **not needed** — the row holds outright. The reason is the clause
`≡` is defined with: `e` and `p` agree *where both are defined*. In precisely the case the
hedge describes the right side is undefined, so the obligation is vacuous and the two sides
cannot disagree.

That cuts both ways, and both halves are on the record: the row is stronger than §6 claims,
and `≡` is weaker than the hedge's prose suggests. `Refutations.not_eq_altCodec_assoc`
exhibits the difference `≡` cannot see. -/

/-- The member index nests the same way it flattens. Both sides conclude the head member
    or `⊤`, so the content is entirely in whether the condition agrees. -/
theorem unanimous_pair_assoc (a b c : Option Member) :
    unanimous [a, unanimous [b, c]] = unanimous [a, b, c] := by
  show (if ([unanimous [b, c]].all (· == a)) = true then a else none)
      = (if ([b, c].all (· == a)) = true then a else none)
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  by_cases hcb : (c == b) = true
  · have hu : unanimous [b, c] = b := by
      show (if ([c].all (· == b)) = true then b else none) = b
      simp only [List.all_cons, List.all_nil, Bool.and_true, if_pos hcb]
    rw [hu, eq_of_beq hcb, Bool.and_self]
  · have hu : unanimous [b, c] = none := by
      show (if ([c].all (· == b)) = true then b else none) = none
      simp only [List.all_cons, List.all_nil, Bool.and_true, if_neg hcb]
    rw [hu]
    cases a with
    | none => simp
    | some x =>
      have hne : ((b == some x) && (c == some x)) = false := by
        cases hbx : (b == some x) with
        | false => simp
        | true =>
          cases hcx : (c == some x) with
          | false => simp
          | true =>
            exact absurd (by rw [eq_of_beq hbx, eq_of_beq hcx]; simp) hcb
      simp [hne]

/-! ### Resolution, named

`altCodec` reads its option list only through "exactly one admits", so at two and three
options its pair has a small closed form. Naming those forms is what lets the
associativity argument be stated about *resolution* rather than about codecs. -/

/-- Resolving two options: the one that admits, or nothing. -/
def resolve₂ {β : Type} (B C : Bool) (E₂ E₃ : Option β) : Option β :=
  match B, C with
  | true, false => E₂
  | false, true => E₃
  | _, _ => none

/-- Resolving a *nested* union: the inner pair resolves first, and the head is consulted
    only where the inner failed. This asymmetry is the whole of §6's hedge. -/
def resolveNested {β : Type} (A : Bool) (inner E₁ : Option β) : Option β :=
  match A, inner with
  | true, none => E₁
  | false, some b => some b
  | _, _ => none

/-- Resolving three options *flat*: all three compete at once. -/
def resolve₃ {β : Type} (A B C : Bool) (E₁ E₂ E₃ : Option β) : Option β :=
  match A, B, C with
  | true, false, false => E₁
  | false, true, false => E₂
  | false, false, true => E₃
  | _, _, _ => none

theorem altCodec_pair_e (o₂ o₃ : OptionSem) (μ' : Option Member) (v : Value) :
    (altCodec [o₂, o₃] μ').e v =
      resolve₂ (o₂.admitV v) (o₃.admitV v) (o₂.c.e v) (o₃.c.e v) := by
  cases hB : o₂.admitV v <;> cases hC : o₃.admitV v <;>
    simp [altCodec, List.filter, resolve₂, hB, hC]

theorem altCodec_pair_p (o₂ o₃ : OptionSem) (μ' : Option Member) (a : Attr) :
    (altCodec [o₂, o₃] μ').p a =
      resolve₂ (o₂.admitA a) (o₃.admitA a) (o₂.c.p a) (o₃.c.p a) := by
  cases hB : o₂.admitA a <;> cases hC : o₃.admitA a <;>
    simp [altCodec, List.filter, resolve₂, hB, hC]

theorem altCodec_triple_e (o₁ o₂ o₃ : OptionSem) (μ : Option Member) (v : Value) :
    (altCodec [o₁, o₂, o₃] μ).e v =
      resolve₃ (o₁.admitV v) (o₂.admitV v) (o₃.admitV v)
        (o₁.c.e v) (o₂.c.e v) (o₃.c.e v) := by
  cases hA : o₁.admitV v <;> cases hB : o₂.admitV v <;> cases hC : o₃.admitV v <;>
    simp [altCodec, List.filter, resolve₃, hA, hB, hC]

theorem altCodec_triple_p (o₁ o₂ o₃ : OptionSem) (μ : Option Member) (a : Attr) :
    (altCodec [o₁, o₂, o₃] μ).p a =
      resolve₃ (o₁.admitA a) (o₂.admitA a) (o₃.admitA a)
        (o₁.c.p a) (o₂.c.p a) (o₃.c.p a) := by
  cases hA : o₁.admitA a <;> cases hB : o₂.admitA a <;> cases hC : o₃.admitA a <;>
    simp [altCodec, List.filter, resolve₃, hA, hB, hC]

theorem altCodec_nest_e (o₁ o₂ o₃ : OptionSem) (μ μ' : Option Member) (v : Value) :
    (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] μ')] μ).e v =
      resolveNested (o₁.admitV v) ((altCodec [o₂, o₃] μ').e v) (o₁.c.e v) := by
  have key : (OptionSem.byAttempt (altCodec [o₂, o₃] μ')).admitV v
      = ((altCodec [o₂, o₃] μ').e v).isSome := rfl
  have hc : (OptionSem.byAttempt (altCodec [o₂, o₃] μ')).c = altCodec [o₂, o₃] μ' := rfl
  show (match [o₁, OptionSem.byAttempt (altCodec [o₂, o₃] μ')].filter (·.admitV v) with
        | [o] => o.c.e v | _ => none) = _
  cases hA : o₁.admitV v <;> cases hI : (altCodec [o₂, o₃] μ').e v <;>
    simp only [List.filter, hA, key, hI, hc, Option.isSome, resolveNested]

theorem altCodec_nest_p (o₁ o₂ o₃ : OptionSem) (μ μ' : Option Member) (a : Attr) :
    (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] μ')] μ).p a =
      resolveNested (o₁.admitA a) ((altCodec [o₂, o₃] μ').p a) (o₁.c.p a) := by
  have key : (OptionSem.byAttempt (altCodec [o₂, o₃] μ')).admitA a
      = ((altCodec [o₂, o₃] μ').p a).isSome := rfl
  have hc : (OptionSem.byAttempt (altCodec [o₂, o₃] μ')).c = altCodec [o₂, o₃] μ' := rfl
  show (match [o₁, OptionSem.byAttempt (altCodec [o₂, o₃] μ')].filter (·.admitA a) with
        | [o] => o.c.p a | _ => none) = _
  cases hA : o₁.admitA a <;> cases hI : (altCodec [o₂, o₃] μ').p a <;>
    simp only [List.filter, hA, key, hI, hc, Option.isSome, resolveNested]

/-- The held sets coincide. Nesting a union changes how it *resolves*, never what it
    holds — which is why this half needs no side condition at all. -/
theorem altCodec_assoc_heldSet (o₁ o₂ o₃ : OptionSem) (μa μb : Option Member) (v : Value) :
    (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] μb)] μa).T v
      ↔ (altCodec [o₁, o₂, o₃] μa).T v := by
  constructor
  · rintro ⟨x, hx, hT⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨x, List.mem_cons_self _ _, hT⟩
    · rcases List.mem_cons.mp hx' with rfl | hx''
      · obtain ⟨y, hy, hTy⟩ := hT
        exact ⟨y, List.mem_cons_of_mem _ hy, hTy⟩
      · exact absurd hx'' (by simp)
  · rintro ⟨x, hx, hT⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨x, List.mem_cons_self _ _, hT⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self _ _), ⟨x, hx', hT⟩⟩

/-- **Associativity, with the codecs abstracted away.** Three admission flags, three
    per-option results, and the two ways of resolving them. Whenever both resolve, they
    resolve alike.

    Reading down the eight cases — `A`, `B`, `C` being which option admits — is reading
    §6's hedge:

    * `f f f`, `f t t` — neither side resolves; the inner pair is empty or ambiguous.
    * `f f t`, `f t f`, `t f f` — exactly one option admits; both sides return it.
    * `t f t`, `t t f` — the head and one inner option both claim it; both sides refuse.
    * `t t t` — **§6's row.** The head admits and the inner pair is ambiguous, so the
      nested form's inner union fails and its outer union resolves to the head, while the
      flat form sees three claimants and refuses. One side defined, the other not, which
      is exactly why `≡` cannot see the difference and why the row needs no conditions.
      `Refutations.not_eq_altCodec_assoc` exhibits it concretely. -/
theorem nest_flat_resolve {β : Type} (A B C : Bool) (E₁ E₂ E₃ : Option β) {x y : β}
    (hn : resolveNested A (resolve₂ B C E₂ E₃) E₁ = some x)
    (hf : resolve₃ A B C E₁ E₂ E₃ = some y) : x = y := by
  cases A <;> cases B <;> cases C
  · exact nomatch hn
  · cases E₃ with
    | none => exact nomatch hn
    | some b => exact (Option.some.inj hn).symm.trans (Option.some.inj hf)
  · cases E₂ with
    | none => exact nomatch hn
    | some b => exact (Option.some.inj hn).symm.trans (Option.some.inj hf)
  · exact nomatch hn
  · exact Option.some.inj (hn.symm.trans hf)
  · cases E₃ with
    | none => exact nomatch hf
    | some b => exact nomatch hn
  · cases E₂ with
    | none => exact nomatch hf
    | some b => exact nomatch hn
  · exact nomatch hf

/-- §6: `union(c₁, union(c₂, c₃)) ≡ union(c₁, c₂, c₃)` — with no side condition.

    Each half is three steps: put both sides in closed form, then appeal to
    `nest_flat_resolve`. The write and read halves differ only in `e` versus `p`. -/
theorem equiv_altCodec_assoc (o₁ o₂ o₃ : OptionSem) :
    Codec.Equiv
      (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] (unanimous [o₂.c.μ, o₃.c.μ]))]
        (unanimous [o₁.c.μ, unanimous [o₂.c.μ, o₃.c.μ]]))
      (altCodec [o₁, o₂, o₃] (unanimous [o₁.c.μ, o₂.c.μ, o₃.c.μ])) := by
  refine ⟨altCodec_assoc_heldSet o₁ o₂ o₃ _ _, unanimous_pair_assoc _ _ _, ?_, ?_⟩
  · intro v a a' hn hf
    rw [altCodec_nest_e, altCodec_pair_e] at hn
    rw [altCodec_triple_e] at hf
    exact nest_flat_resolve (o₁.admitV v) (o₂.admitV v) (o₃.admitV v)
      (o₁.c.e v) (o₂.c.e v) (o₃.c.e v) hn hf
  · intro a v v' hn hf
    rw [altCodec_nest_p, altCodec_pair_p] at hn
    rw [altCodec_triple_p] at hf
    exact nest_flat_resolve (o₁.admitA a) (o₂.admitA a) (o₃.admitA a)
      (o₁.c.p a) (o₂.c.p a) (o₃.c.p a) hn hf

/-! ## §6's Hold rows, at term level

Each row's twin, stated where a reader of `codec-calculus.md` §6 would look for it: about a
`Term`, the way `Refutations.lean`'s "Do not hold" rows already are. Every one is its
combinator row through the bridge above, so they cost a line each and buy the property
`FIDELITY.md` §3 asked for — both halves of §6 in one language. -/

section Terms

/-- §6: `held(c, id, id) ≡ c`. -/
theorem equiv_denoteω_held_id (t : Term) :
    Codec.Equiv (denoteω (.held t id id)) (denoteω t) := equiv_through_id _

/-- §6: `held(held(c, f, g), f′, g′) ≡ held(c, f ∘ f′, g′ ∘ g)`. -/
theorem equiv_denoteω_held_comp (t : Term) (f g f' g' : Value → Value) :
    Codec.Equiv (denoteω (.held (.held t f g) f' g'))
      (denoteω (.held t (f ∘ f') (g' ∘ g))) := equiv_through_comp _ _ _ _ _

/-- §6: `refine(refine(c, q), q′) ≡ refine(c, q ∩ q′)`. -/
theorem equiv_denoteω_refine_meet (t : Term) (q q' : Value → Bool) :
    Codec.Equiv (denoteω (.refine (.refine t q) q'))
      (denoteω (.refine t (fun v => q v && q' v))) := equiv_restrict_meet _ _ _

/-- §6: `refine(c, T) ≡ c` for `⊢ c : T ⇝ μ`. The premise is the row's, read off the
    denotation rather than the judgement — `typed_TSub` is what connects the two. -/
theorem equiv_denoteω_refine_full (t : Term) (q : Value → Bool)
    (hq : ∀ v, (denoteω t).T v ↔ q v = true) :
    Codec.Equiv (denoteω (.refine t q)) (denoteω t) := equiv_restrict_full _ _ hq

/-- §6: `legacy(c, p_c) ≡ c`. -/
theorem equiv_denoteω_legacy_self (t : Term) :
    Codec.Equiv (denoteω (.legacy t (denoteω t).p)) (denoteω t) :=
  equiv_extendRead_self _

/-- §6: `legacy(c, r) ≈ c` on `Can(c)`. -/
theorem denoteω_legacy_eq_on_can (t : Term) (r : Attr → Option Value)
    (hc : Lawful (denoteω t)) {a : Attr} (ha : Can (denoteω t) a) :
    (denoteω (.legacy t r)).p a = (denoteω t).p a :=
  extendRead_eq_on_can _ r hc ha

/-- §6: `nullable(nullable(c)) ≡ nullable(c)`. -/
theorem equiv_denoteω_nullable_idem (t : Term) :
    Codec.Equiv (denoteω (.nullable (.nullable t))) (denoteω (.nullable t)) :=
  equiv_orNull_idem _

/-- §6: `μ(w(c)) = μ(c)` for the three codec wrappers. The two field wrappers are
    `optional_μ` and `fallback_μ`, which are already stated over a denotation. -/
theorem denoteω_held_μ (t : Term) (f g : Value → Value) :
    (denoteω (.held t f g)).μ = (denoteω t).μ := rfl

theorem denoteω_refine_μ (t : Term) (q : Value → Bool) :
    (denoteω (.refine t q)).μ = (denoteω t).μ := rfl

theorem denoteω_legacy_μ (t : Term) (r : Attr → Option Value) :
    (denoteω (.legacy t r)).μ = (denoteω t).μ := rfl

end Terms

end Calculus
