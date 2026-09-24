import Calculus.Soundness
import Calculus.Denote
import Calculus.Opaque

/-!
# §6 — Equations

Which rewrites preserve the pair. `≡` is §6's own reading: the same held set, the same
member, and `e` and `p` agreeing everywhere both are defined.

All eleven of §6's "Hold" rows are proved here. Two of them are cited elsewhere as
load-bearing and came first:

* `union(c₁ … cₙ) ≡ union(c_σ(1) … c_σ(n))` — §5 leans on this for "declaration order is
  never consulted". Proved at *every* permutation and as an **equality** of the pair
  (`altCodec_perm`), not merely `≡`, over pairwise compatible, lawful options. Deriving the general case from the adjacent one would
  need `≡` to compose, and `Refutations.not_equiv_trans` says it does not.

The remaining rows: `held`'s identity and composition, `refine`'s meet and its full case,
`alternate reader` with its own reading (and `≈` on `Can(c)`), `union` of one, and the member
preservation of the three codec wrappers.

The last row, `union` associativity, needs no condition: a nested union and its flattening
consult the same options in the same order, so the two are equal on both halves.

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



/-! ## `union` is commutative, at every permutation

    Resolution takes the first admitter. Where the options are lawful and pairwise
    compatible, every admitter writes and reads alike, so reordering the options changes
    nothing. The general case is proved directly, and the adjacent one falls out of it at
    `List.Perm.swap`: `≡` does not compose (`Refutations.not_equiv_trans`), and an equality
    does. The two codecs are **equal**, not only equivalent. -/

/-- Two options that are defined at the same answers are equal. -/
theorem option_eq_of_some_iff {β : Type} {x y : Option β} (h : ∀ b, x = some b ↔ y = some b) :
    x = y := by
  cases hx : x with
  | none =>
    cases hy : y with
    | none => rfl
    | some b => rw [hx] at h; exact nomatch (h b).mpr hy
  | some b => exact ((h b).mp hx).symm

/-- §6: `union(c₁ … cₙ) ≡ union(c_σ(1) … c_σ(n))`, **on the nose**, over options that are
    attempted, lawful and pairwise compatible. -/
theorem altCodec_perm {os os' : List OptionSem} (h : os.Perm os') (μA : Option Member)
    (hatt : ∀ o ∈ os, o = .byAttempt o.c) (hl : ∀ o ∈ os, Lawful o.c)
    (hC : ∀ o ∈ os, ∀ o' ∈ os, Compat o.c o'.c) :
    altCodec os μA = altCodec os' μA := by
  have m := fun o => h.mem_iff (a := o)
  have hatt' : ∀ o ∈ os', o = .byAttempt o.c := fun o ho => hatt o ((m o).mpr ho)
  have hl' : ∀ o ∈ os', Lawful o.c := fun o ho => hl o ((m o).mpr ho)
  have hC' : ∀ o ∈ os', ∀ o' ∈ os', Compat o.c o'.c :=
    fun o ho o' ho' => hC o ((m o).mpr ho) o' ((m o').mpr ho')
  refine Codec.ext ?_ rfl ?_ ?_
  · funext v
    exact propext ⟨fun ⟨o, ho, hT⟩ => ⟨o, (m o).mp ho, hT⟩,
      fun ⟨o, ho, hT⟩ => ⟨o, (m o).mpr ho, hT⟩⟩
  · funext v
    refine option_eq_of_some_iff fun b => ⟨fun he => ?_, fun he => ?_⟩
    · obtain ⟨o, ho, -, hoe⟩ := altCodec_e_admits he
      exact altCodec_e_of_mem hatt' hl' hC' ((m o).mp ho) hoe
    · obtain ⟨o, ho, -, hoe⟩ := altCodec_e_admits he
      exact altCodec_e_of_mem hatt hl hC ((m o).mpr ho) hoe
  · funext a
    refine option_eq_of_some_iff fun b => ⟨fun hp => ?_, fun hp => ?_⟩
    · obtain ⟨o, ho, -, hop⟩ := altCodec_p_admits hp
      exact altCodec_p_of_mem hatt' hC' ((m o).mp ho) hop
    · obtain ⟨o, ho, -, hop⟩ := altCodec_p_admits hp
      exact altCodec_p_of_mem hatt hC ((m o).mpr ho) hop

/-- The row as §6 states it, in `≡`: `Codec.Equiv.refl` transported along the equality. -/
theorem equiv_altCodec_perm {os os' : List OptionSem} (h : os.Perm os') (μA : Option Member)
    (hatt : ∀ o ∈ os, o = .byAttempt o.c) (hl : ∀ o ∈ os, Lawful o.c)
    (hC : ∀ o ∈ os, ∀ o' ∈ os, Compat o.c o'.c) :
    Codec.Equiv (altCodec os μA) (altCodec os' μA) :=
  altCodec_perm h μA hatt hl hC ▸ Codec.Equiv.refl _

/-- §6: `union(c₁, c₂, …) ≡ union(c₂, c₁, …)`, the general theorem at `List.Perm.swap`. -/
theorem equiv_altCodec_swap (o₁ o₂ : OptionSem) (os : List OptionSem) (μA : Option Member)
    (hatt : ∀ o ∈ o₁ :: o₂ :: os, o = .byAttempt o.c)
    (hl : ∀ o ∈ o₁ :: o₂ :: os, Lawful o.c)
    (hC : ∀ o ∈ o₁ :: o₂ :: os, ∀ o' ∈ o₁ :: o₂ :: os, Compat o.c o'.c) :
    Codec.Equiv (altCodec (o₁ :: o₂ :: os) μA) (altCodec (o₂ :: o₁ :: os) μA) :=
  equiv_altCodec_perm (List.Perm.swap o₂ o₁ os) μA hatt hl hC

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

/-! ## `alternate reader` with its own reading -/

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

/-- §6: `union(c) ≡ c`. Choice of one: `o` is the first admitter exactly when `o` admits,
    and `altCodec` then reads `o`'s own pair. Where `o` does not admit, the union is undefined
    and `≡` asks nothing — which is the clause that makes this row true for a `byStructure`
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
    · exact fun h => ⟨o, List.mem_cons_self, h⟩
  · intro v a a' h h'
    obtain ⟨x, hf, hxe⟩ := altCodec_e.mp h
    obtain rfl : x = o := by simpa using List.mem_of_find?_eq_some hf
    exact Option.some.inj (hxe.symm.trans h')
  · intro a v v' h h'
    obtain ⟨x, hf, hxp⟩ := altCodec_p.mp h
    obtain rfl : x = o := by simpa using List.mem_of_find?_eq_some hf
    exact Option.some.inj (hxp.symm.trans h')

/-! ## Wrappers preserve the member

§6's last "Hold" row, `μ(w(c)) = μ(c)` for `w ∈ {held, refine, legacy, optional,

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
theorem optional_μ (t : Term) : (fieldSem (.optional t)).codec.μ = (denote t).μ := rfl

/-! ## `union` is associative

§6's row, stated outright. Both forms take the first admitter in the same order, so the
write and read halves are equal (`altCodec_nest_e`, `altCodec_nest_p`), and the row carries
no condition. -/

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

/-! ### Nesting is flattening

A nested union consults the head, then the inner union's first admitter; the flat union
consults the same options in the same order. So both halves are equal, with no side
condition. -/

/-- `select` over no option answers nothing. -/
theorem select_nil_eq {A B : Type} (adm : OptionSem → A → Bool) (run : OptionSem → A → Option B)
    (x : A) : select [] adm run x = none := rfl

/-- `select` at a cons: the head answers where it admits. -/
theorem select_cons {A B : Type} (o : OptionSem) (os : List OptionSem)
    (adm : OptionSem → A → Bool) (run : OptionSem → A → Option B) (x : A) :
    select (o :: os) adm run x = if adm o x then run o x else select os adm run x := by
  unfold select; cases h : adm o x <;> simp [List.find?, h]

theorem altCodec_nest_e (o₁ o₂ o₃ : OptionSem) (μ μ' μf : Option Member) (v : Value) :
    (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] μ')] μ).e v = (altCodec [o₁, o₂, o₃] μf).e v := by
  show select _ _ _ v = select _ _ _ v
  rw [select_cons, select_cons, select_cons, select_nil_eq]
  show (if _ then _ else if ((select [o₂, o₃] (·.admitV) (·.c.e) v).isSome) then
    select [o₂, o₃] (·.admitV) (·.c.e) v else none) = _
  cases select [o₂, o₃] (·.admitV) (·.c.e) v <;> simp

theorem altCodec_nest_p (o₁ o₂ o₃ : OptionSem) (μ μ' μf : Option Member) (a : Attr) :
    (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] μ')] μ).p a = (altCodec [o₁, o₂, o₃] μf).p a := by
  show select _ _ _ a = select _ _ _ a
  rw [select_cons, select_cons, select_cons, select_nil_eq]
  show (if _ then _ else if ((select [o₂, o₃] (·.admitA) (·.c.p) a).isSome) then
    select [o₂, o₃] (·.admitA) (·.c.p) a else none) = _
  cases select [o₂, o₃] (·.admitA) (·.c.p) a <;> simp

/-- The held sets coincide. Nesting a union changes how it *resolves*, never what it
    holds — which is why this half needs no side condition at all. -/
theorem altCodec_assoc_heldSet (o₁ o₂ o₃ : OptionSem) (μa μb : Option Member) (v : Value) :
    (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] μb)] μa).T v
      ↔ (altCodec [o₁, o₂, o₃] μa).T v := by
  constructor
  · rintro ⟨x, hx, hT⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨x, List.mem_cons_self, hT⟩
    · rcases List.mem_cons.mp hx' with rfl | hx''
      · obtain ⟨y, hy, hTy⟩ := hT
        exact ⟨y, List.mem_cons_of_mem _ hy, hTy⟩
      · exact absurd hx'' (by simp)
  · rintro ⟨x, hx, hT⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨x, List.mem_cons_self, hT⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self), ⟨x, hx', hT⟩⟩

/-- §6: `union(c₁, union(c₂, c₃)) ≡ union(c₁, c₂, c₃)` — with no side condition. -/
theorem equiv_altCodec_assoc (o₁ o₂ o₃ : OptionSem) :
    Codec.Equiv
      (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] (unanimous [o₂.c.μ, o₃.c.μ]))]
        (unanimous [o₁.c.μ, unanimous [o₂.c.μ, o₃.c.μ]]))
      (altCodec [o₁, o₂, o₃] (unanimous [o₁.c.μ, o₂.c.μ, o₃.c.μ])) := by
  refine ⟨altCodec_assoc_heldSet o₁ o₂ o₃ _ _, unanimous_pair_assoc _ _ _, ?_, ?_⟩
  · intro v a a' hn hf
    rw [altCodec_nest_e (μf := unanimous [o₁.c.μ, o₂.c.μ, o₃.c.μ])] at hn
    exact Option.some.inj (hn.symm.trans hf)
  · intro a v v' hn hf
    rw [altCodec_nest_p (μf := unanimous [o₁.c.μ, o₂.c.μ, o₃.c.μ])] at hn
    exact Option.some.inj (hn.symm.trans hf)

/-! ## §6's Hold rows, at term level

Each row's twin, stated where a reader of the specification's §6 would look for it: about a
`Term`, the way `Refutations.lean`'s "Do not hold" rows already are. Every one is its
combinator row through the bridge above, so they cost a line each and buy the property
the representation audit asked for — both halves of §6 in one language. -/

section Terms

/-- §6: `held(c, P, id, id) ≡ refine(c, P)`. The identity transform leaves the caller-side
    restriction, and that restriction is a `refine` by the admission of `P`. -/
theorem equiv_denote_held_id (t P : Term) :
    Codec.Equiv (denote (.held t P id id))
      (denote (.refine t (.closure fun v => ((denote P).e v).isSome))) := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩
  · intro v a a' h h'
    exact Option.some.inj ((through_e.mp (restrict_e.mp h).2).symm.trans (restrict_e.mp h').2)
  · intro a v v' h h'
    obtain ⟨w, hw, rfl⟩ := through_p.mp (restrict_p.mp h).1
    exact Option.some.inj (hw.symm.trans (restrict_p.mp h').1)

/-- §6: `held(held(c, P, f, g), P′, f′, g′) ≡ refine(held(c, P′, f ∘ f′, g′ ∘ g), P ∘ f′)`.
    The transforms compose, and the inner caller-side restriction pulls back along `f′`. The
    pullback is a predicate and no term, so the right side carries it as a `refine`. -/
theorem equiv_denote_held_comp (t P P' : Term) (f g f' g' : Value → Value) :
    Codec.Equiv (denote (.held (.held t P f g) P' f' g'))
      (denote (.refine (.held t P' (f ∘ f') (g' ∘ g))
        (.closure fun v => ((denote P).e (f' v)).isSome))) := by
  refine ⟨fun _ => ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h3⟩, h2⟩, fun ⟨⟨h1, h3⟩, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩,
    rfl, ?_, ?_⟩
  · intro v a a' h h'
    have hl := (restrict_e.mp (through_e.mp (restrict_e.mp h).2)).2
    have hr := (restrict_e.mp (restrict_e.mp h').2).2
    exact Option.some.inj ((through_e.mp hl).symm.trans hr)
  · intro a v v' h h'
    obtain ⟨w, hw, rfl⟩ := through_p.mp (restrict_p.mp h).1
    obtain ⟨x, hx, rfl⟩ := through_p.mp (restrict_p.mp hw).1
    obtain ⟨y, hy, rfl⟩ := through_p.mp (restrict_p.mp (restrict_p.mp h').1).1
    rw [hx] at hy
    cases hy
    rfl

/-- §6: `refine(refine(c, q), q′) ≡ refine(c, q ∩ q′)`.

    **The meet is a `closure`, and that is what `Pred` costs.** The equation is about codecs
    and it holds: `equiv_restrict_meet` is unchanged, because `restrict` still takes a
    `Value → Bool` and `denote` hands it `p.eval`. What the reified predicate cannot do is
    keep the *shape*. Two `members` meet in a term the classifier no longer reads, so `Orth`
    declines the right-hand side where it certifies the left. That is the sound direction: a
    declined certificate is a missing proof, never a wrong one.

    For the reader who reaches for a fourth constructor: two `members` at one base meet in a
    `members` over the intersection, where the intersection is nonempty. A discharger that
    needs that reduction states it as a lemma about `Pred`, and `Pred` stays one to one with
    the host's three cases, which is the whole reason it has three. -/
theorem equiv_denote_refine_meet (t : Term) (p p' : Pred) :
    Codec.Equiv (denote (.refine (.refine t p) p'))
      (denote (.refine t (.closure (fun v => p.eval v && p'.eval v)))) :=
  equiv_restrict_meet _ _ _

/-- §6: `refine(c, T) ≡ c` for `⊢ c : T ⇝ μ`. The premise is the row's, read off the
    denotation rather than the judgement — `typed_TSub` is what connects the two. -/
theorem equiv_denote_refine_full (t : Term) (p : Pred)
    (hq : ∀ v, (denote t).T v ↔ p.eval v = true) :
    Codec.Equiv (denote (.refine t p)) (denote t) := equiv_restrict_full _ _ hq

/-- §6: `μ(w(c)) = μ(c)` for the three codec wrappers. The two field wrappers are
    `optional_μ` and `optional_μ`, which are already stated over a denotation. -/
theorem denote_held_μ (t P : Term) (f g : Value → Value) :
    (denote (.held t P f g)).μ = (denote t).μ := rfl

theorem denote_refine_μ (t : Term) (p : Pred) :
    (denote (.refine t p)).μ = (denote t).μ := rfl

end Terms

end Calculus
