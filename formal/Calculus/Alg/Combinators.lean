import Mathlib.Data.List.Forall2
import Calculus.Alg.Codec

/-!
# The combinators and the join, over any carriers

The side conditions of §3, the wrappers `held`, `refine` and `alternate reader`, the point codec
of a pair of prisms, and the union by the first admitter. Each one reads only the pair and the
member, so each one takes the carriers as parameters: `V` the caller's values, `A` the stored
attributes, and `M` the members. The laws of each combinator follow from the laws of its
arguments, and `member : A → M` is the one fact of the store that (W) reads.
-/

namespace Calculus.Alg

variable {V A M : Type}

/-! ## §3's side conditions, named

Three rules carry premises about the pair rather than about the index, and §3 names each
of them in prose. Naming them here too is what keeps `Obligations` readable and stops
every use site restating the proposition: a case that consumes one of these says which
condition it is consuming. -/

/-- §3 `(held)`: the iso cancels **on the carriers** — `T ≃ I`, in the domain-restricted
    form the laws actually need. `g ∘ f = id` where `f` lands writable, `f ∘ g = id` on
    the writable values themselves. -/
def IsoCancels (c : Codec V A M) (f g : V → V) : Prop :=
  (∀ v, (c.e (f v)).isSome → g (f v) = v) ∧
  (∀ v, (c.e v).isSome → f (g v) = v)

/-- §3 `(alternate reader)`: `ran(r) ⊆ dom(e)` — a migration lands on writable values — and
    coherence, the legacy reading agreeing with the current one on their overlap. -/
def ReadsCoherently (c : Codec V A M) (r : A → Option V) : Prop :=
  (∀ a v, r a = some v → (c.e v).isSome) ∧
  (∀ a v, r a = some v → ∀ v', c.p a = some v' → v = v')

/-- §3 types the pair *on the held set*: `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T`. `Lawful` never
    mentions `T`, because retract, canon and writes relate `e` and `p` to each other and not to
    the index. So this is the separate claim that the index is honest, and it is what makes `T` a
    checked part of the judgement rather than a decoration. -/
structure Carrier (c : Codec V A M) : Prop where
  /-- `e : T ⇀ 𝔸` — nothing outside the held set is written. -/
  domE : ∀ {v a}, c.e v = some a → c.T v
  /-- `p : 𝔸 ⇀ T` — nothing outside the held set is read. -/
  ranP : ∀ {a v}, c.p a = some v → c.T v

/-- The empty codec is on its (empty) carrier, vacuously. -/
theorem Carrier.empty : Carrier (Codec.empty : Codec V A M) := by
  refine ⟨?_, ?_⟩ <;> intro _ _ h <;> exact nomatch h

/-- `Can(c)` is §2's `e[T]` — and it takes `Carrier` to say so: without `domE` a codec could
    write from a value it does not hold, making `Can` larger than the image. -/
theorem can_iff_image {c : Codec V A M} (h : Carrier c) {a : A} :
    Can c a ↔ ∃ v, c.T v ∧ c.e v = some a := by
  constructor
  · rintro ⟨v, hv⟩; exact ⟨v, h.domE hv, hv⟩
  · rintro ⟨v, -, hv⟩; exact ⟨v, hv⟩

/-! ## §1's store, as a premise

§2 composes `e` and `p` directly. In use there is a store between them and it is not the
identity on attributes. This is the premise itself, for every store. -/

/-- **`η ⊆ ker p`** — §1's concession, as a proposition. Quantified over `Can(c)` because
    `η` only ever sees what `e` wrote. Buys `retract_through_store`: (R) through the store. -/
def SurvivesStore (c : Codec V A M) (η : A → A) : Prop :=
  ∀ a, Can c a → c.Ker (η a) a

variable {member : A → M}

/-- **(R), through the store.** `η ⊆ ker p` is exactly what makes a codec survive a round
    trip that passes through the store rather than through `Option` — and it is all it takes,
    which is why §1 could answer the whole problem by narrowing one held set. -/
theorem Lawful.retract_through_store {c : Codec V A M} (h : Lawful member c) {η : A → A}
    (hη : SurvivesStore c η) {t a} (he : c.e t = some a) : c.p (η a) = some t := by
  have hk : c.p (η a) = c.p a := hη a ⟨t, he⟩
  rw [hk, h.retract he]

/-! ## Constructors as prisms -/

/-- A constructor, as a partial iso onto its image. -/
structure Ctor (α β : Type) where
  /-- Build. -/
  into : α → β
  /-- Match, partially. -/
  out : β → Option α
  /-- Matching what was built returns it. -/
  out_into : ∀ x, out (into x) = some x
  /-- Anything that matches was built. -/
  into_out : ∀ {b x}, out b = some x → b = into x

/-- **A prism at each absolute side**: `pV` into the values, and `pA` into the attributes. -/
def Ctor.side {α : Type} (pV : Ctor α V) (pA : Ctor α A) : (s : Bool) → Ctor α (Side V A s)
  | false => pV
  | true => pA

/-- **The point ground codecs of §3**, as one construction: a payload carried between a
    value constructor `pV` and an attribute constructor `pA`, both prisms.

    The prism laws are exactly §2's laws in disguise — `out_into` is the round trip **(R)**
    and `into_out` is canonizability **(C)** — which is why `lawful_pointCodec` needs no
    hypothesis about either side beyond the member it stamps. One formula serves each
    orientation: match with the prism of the caller side, and build with the prism of the stored
    side. -/
def pointCodec {α : Type} (pV : Ctor α V) (pA : Ctor α A) (μ₀ : M) : Codec V A M where
  T v := ∃ x, v = pV.into x
  μ := some μ₀
  f o x := ((Ctor.side pV pA o.c).out x).map (Ctor.side pV pA o.s).into

/-! ## Wrappers -/

/-- `held`: an iso on the value side; the stored side is untouched. The iso acts at the values
    only, so the write and the read are two formulas. One formula over the orientation would
    only hide that case split. -/
def Codec.through (c : Codec V A M) (f g : V → V) : Codec V A M :=
  Codec.ofEP (T := fun v => c.T (f v))
    (μ := c.μ)
    (e := fun v => c.e (f v))
    (p := fun a => (c.p a).map g)

/-- **The two-sided restriction** `[qA] ∘ c ∘ [qV]`: `qV` restricts the values, and `qA`
    restricts the attributes. One formula serves each orientation: the predicate at the caller
    side of the orientation gates the input, and the predicate at the stored side gates the
    output. -/
def refine2 (c : Codec V A M) (qV : V → Bool) (qA : A → Bool) : Codec V A M where
  T v := c.T v ∧ qV v
  μ := c.μ
  f o x := if Side.elim qV qA o.c x then
      (c.f o x).bind fun y => if Side.elim qV qA o.s y then some y else none
    else none

/-- `refine`: the prism. It is the two-sided restriction whose stored predicate admits every
    attribute. -/
def Codec.restrict (c : Codec V A M) (q : V → Bool) : Codec V A M :=
  refine2 c q fun _ => true

/-- What the two-sided restriction sends: the input passes the predicate of the caller side,
    the base sends the input, and the output passes the predicate of the stored side. -/
theorem refine2_f {c : Codec V A M} {qV : V → Bool} {qA : A → Bool} {o : Orient}
    {x : Side V A o.c} {y : Side V A o.s} :
    (refine2 c qV qA).f o x = some y ↔
      Side.elim qV qA o.c x = true ∧ c.f o x = some y ∧ Side.elim qV qA o.s y = true := by
  simp only [refine2]
  cases Side.elim qV qA o.c x
  · simp
  · cases c.f o x with
    | none => simp
    | some y' =>
      cases hq : Side.elim qV qA o.s y' <;> simp [hq] <;> intro hh <;> subst hh <;> assumption

/-- The write of the two-sided restriction, for a rewrite. -/
theorem refine2_e_def (c : Codec V A M) (qV : V → Bool) (qA : A → Bool) :
    (refine2 c qV qA).e =
      fun v => if qV v then (c.e v).bind (fun a => if qA a then some a else none) else none := rfl

/-- The read of the two-sided restriction, for a rewrite. -/
theorem refine2_p_def (c : Codec V A M) (qV : V → Bool) (qA : A → Bool) :
    (refine2 c qV qA).p =
      fun a => if qA a then (c.p a).bind (fun v => if qV v then some v else none) else none := rfl

/-- The write of a restriction: the predicate guards the write of the base. -/
theorem restrict_e_def (c : Codec V A M) (q : V → Bool) :
    (c.restrict q).e = fun v => if q v then c.e v else none := by
  simp only [Codec.restrict, refine2_e_def, if_true, Option.bind_fun_some]

/-- The read of a restriction: the predicate guards the value that the base reads. -/
theorem restrict_p_def (c : Codec V A M) (q : V → Bool) :
    (c.restrict q).p = fun a => (c.p a).bind fun v => if q v then some v else none := rfl

/-- **The combinator `held` and `refine` both are.** A partial iso either side of the
    pair: `f` in front of the writing, `g` behind the reading, both allowed to refuse.

    §3 keeps the two apart and says why — "the literature collapses them … which is
    exactly the merged combinator", separated for a reason *outside* the calculus, since a
    total `g` lets a generator for `I` be pushed forward while a partial one leaves only
    rejection sampling. This is that merged combinator, so the claim is checked rather
    than asserted: `through` is `adapt` with both halves total, `refine` is `adapt` with a
    partial identity on both halves, and the four theorems below are the whole of it.

    The `Codec` is not redefined in its terms. `T` agrees only propositionally — `adapt`'s
    is `∃ w, f v = some w ∧ c.T w` where `through`'s is `c.T (f v)` — so a merge at the
    definition would cost every `rfl` over the two wrappers, and that trade is not worth
    taking blind. The pair is what the claim is about, and the
    pair agrees on the nose.

    The adapter acts at the values only, so the write and the read are two formulas. One
    formula over the orientation would only hide that case split. -/
def Codec.adapt (c : Codec V A M) (f g : V → Option V) : Codec V A M :=
  Codec.ofEP (T := fun v => ∃ w, f v = some w ∧ c.T w)
    (μ := c.μ)
    (e := fun v => (f v).bind c.e)
    (p := fun a => (c.p a).bind g)

/-- The partial identity on a predicate — `refine`'s adapter, on both halves. -/
def partialId (q : V → Bool) : V → Option V := fun v => if q v then some v else none

/-- `held` writes as `adapt` with a total adapter. -/
theorem through_e_adapt {c : Codec V A M} (f g : V → V) :
    (c.through f g).e = (c.adapt (some ∘ f) (some ∘ g)).e := rfl

/-- …and reads as one. -/
theorem through_p_adapt {c : Codec V A M} (f g : V → V) :
    (c.through f g).p = (c.adapt (some ∘ f) (some ∘ g)).p := by
  funext a; simp only [Codec.through, Codec.adapt, Codec.ofEP_p]; cases c.p a <;> rfl

/-- `refine` writes as `adapt` with a partial identity — the *same* combinator, weaker
    adapter. This is the sense in which it is sugar. -/
theorem restrict_e_adapt {c : Codec V A M} (q : V → Bool) :
    (c.restrict q).e = (c.adapt (partialId q) (partialId q)).e := by
  funext v
  simp only [restrict_e_def, Codec.adapt, Codec.ofEP_e, partialId]
  cases q v <;> rfl

/-- …and reads as one. -/
theorem restrict_p_adapt {c : Codec V A M} (q : V → Bool) :
    (c.restrict q).p = (c.adapt (partialId q) (partialId q)).p := rfl

/-! ### The converse, and the two-sided restriction

`conv c` swaps the two halves of a codec. -/

/-- **The converse of a codec**: the read is the write, and the write is the read. The member
    names nothing on the stored side of the converse, so it is `Unit`. -/
def conv (c : Codec V A M) : Codec A V Unit :=
  Codec.ofEP (T := fun _ => True) (μ := c.μ.map (fun _ => ())) (e := c.p) (p := c.e)

/-- **The stored-side gate**: the partial map sends the input, and the predicate admits the
    output. The gate of the write reads the write, and the gate of the read reads the read. -/
def gate {X Y : Type} (m : X → Option Y) (q : Y → Bool) (x : X) : Bool :=
  match m x with
  | some y => q y
  | none => false

/-- The gate of the truth predicate is the domain of the map. -/
theorem gate_true {X Y : Type} (m : X → Option Y) (x : X) :
    gate m (fun _ => true) x = (m x).isSome := by
  unfold gate
  cases m x <;> rfl

/-- **The domain of the two-sided restriction at an orientation**: the predicate of the caller
    side, and the gate of the predicate of the stored side. -/
theorem refine2_f_isSome (c : Codec V A M) (qV : V → Bool) (qA : A → Bool) (o : Orient)
    (x : Side V A o.c) :
    ((refine2 c qV qA).f o x).isSome =
      (Side.elim qV qA o.c x && gate (c.f o) (Side.elim qV qA o.s) x) := by
  simp only [refine2, gate]
  cases Side.elim qV qA o.c x
  · rfl
  · cases c.f o x with
    | none => rfl
    | some y => cases h : Side.elim qV qA o.s y <;> simp [h]

/-- The write domain of the two-sided restriction: the domain at the host. -/
theorem refine2_e_isSome (c : Codec V A M) (qV : V → Bool) (qA : A → Bool) (v : V) :
    ((refine2 c qV qA).e v).isSome = (qV v && gate c.e qA v) :=
  refine2_f_isSome c qV qA .host v

/-- The read domain of the two-sided restriction: the domain at the dual. -/
theorem refine2_p_isSome (c : Codec V A M) (qV : V → Bool) (qA : A → Bool) (a : A) :
    ((refine2 c qV qA).p a).isSome = (qA a && gate c.p qV a) :=
  refine2_f_isSome c qV qA .dual a

/-- A refinement writes where the gate passes and the base writes, so a row can read off a
    refinement without unfolding it. -/
@[simp] theorem restrict_e_isSome {c : Codec V A M} {q : V → Bool} (v : V) :
    ((c.restrict q).e v).isSome = (q v && (c.e v).isSome) := by
  rw [Codec.restrict, refine2_e_isSome, gate_true]

/-- `alternate reader`: extend the reading. With §3's coherence premise this presentation equals
    the order-free `p ∪ r`. The migration extends the read only, so the write and the read are
    two formulas. -/
def Codec.extendRead (c : Codec V A M) (r : A → Option V) : Codec V A M :=
  Codec.ofEP (T := c.T)
    (μ := c.μ)
    (e := c.e)
    (p := fun a => match c.p a with | some v => some v | none => r a)

/-! ### What the wrappers write and read

Each wrapper is one line of definition and touches exactly one half of the pair; stating
that as an `iff` is what keeps the proofs below — and §6's wrapper rows — from unfolding
the definitions again. `held` and `alternate reader` are transparent on the side they do not
touch, which is why two of the eight are `Iff.rfl`. -/

section WrapperInversion
variable {c : Codec V A M}

/-- `held` writes what its base writes, at the transported value. -/
theorem through_e {f g : V → V} {v a} :
    (c.through f g).e v = some a ↔ c.e (f v) = some a := Iff.rfl

/-- …and reads what its base reads, transported back. -/
theorem through_p {f g : V → V} {a v} :
    (c.through f g).p a = some v ↔ ∃ w, c.p a = some w ∧ v = g w := by
  simp [Codec.through, Option.map_eq_some_iff, eq_comm (a := v)]

/-- The read side of `restrict_e_isSome`, and its absence is why every literal row unfolded
    `Codec.restrict` by hand. §4c asks for one codec stated once for both sides; the write half
    was `@[simp]` and the read half was not there. -/
@[simp] theorem restrict_p_isSome {c : Codec V A M} {q : V → Bool} (a : A) :
    ((c.restrict q).p a).isSome = ((c.p a).elim false q) := by
  rw [Codec.restrict, refine2_p_isSome, Bool.true_and]
  simp only [gate]; cases c.p a <;> rfl

/-- `alternate reader` does not touch the writing at all — §5's whole point. -/
theorem extendRead_e {r : A → Option V} {v a} :
    (c.extendRead r).e v = some a ↔ c.e v = some a := Iff.rfl

/-- It reads through the base where the base reads, and through the migration exactly
    where the base does not. That "exactly" is where canonical reads go. -/
theorem extendRead_p {r : A → Option V} {a v} :
    (c.extendRead r).p a = some v ↔ c.p a = some v ∨ (c.p a = none ∧ r a = some v) := by
  show (match c.p a with | some w => some w | none => r a) = some v ↔ _
  cases hp : c.p a <;> simp

end WrapperInversion

/-- Lawfulness sees only the pair and the member, so it transfers to any codec agreeing on
    those three. This is how a ground codec inherits from the wrapper it turns out to be,
    without disturbing its definition — which matters, since the definitions are unfolded
    all over the development. -/
theorem Lawful.congr {c d : Codec V A M} (he : c.e = d.e) (hp : c.p = d.p) (hμ : c.μ = d.μ)
    (h : Lawful member d) : Lawful member c where
  inv {o _ _} hx := by
    have hf := Orient.both (P := fun o => c.f o = d.f o) he hp
    rw [hf o] at hx; rw [hf o.op]; exact h.inv hx
  writes hm _ _ hx := by rw [hμ] at hm; rw [he] at hx; exact h.writes hm hx

/-- The carrier transfers too, given the held set is no smaller. -/
theorem Carrier.congr {c d : Codec V A M} (he : c.e = d.e) (hp : c.p = d.p)
    (hT : ∀ v, d.T v → c.T v) (h : Carrier d) : Carrier c := by
  refine ⟨?_, ?_⟩
  · intro v a hx; rw [he] at hx; exact hT v (h.domE hx)
  · intro a v hx; rw [hp] at hx; exact hT v (h.ranP hx)

/-! ## Sums (§5) -/

/-- A list no two of whose entries stand in any relation holds at most one entry. -/
theorem length_le_one_of_pairwise_false {α : Type} {l : List α}
    (h : List.Pairwise (fun _ _ : α => False) l) : l.length ≤ 1 := by
  cases l with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp
    | cons y ys => exact absurd ((List.pairwise_cons.mp h).1 y (by simp)) id

/-- **No value and no attribute is admitted by two options.** The certificate implies it
    (`admitsAtMostOne_of_separated`). -/
def AdmitsAtMostOne (os : List (Codec V A M)) : Prop :=
  (∀ t, (os.filter (fun c => (c.e t).isSome)).length ≤ 1) ∧
  (∀ a, (os.filter (fun c => (c.p a).isSome)).length ≤ 1)

/-- **The first option that acts.** A sum at each orientation is this: act through the first
    option that admits by the admission of that orientation. -/
def select {X Y : Type} (os : List (Codec V A M)) (run : Codec V A M → X → Option Y) (x : X) :
    Option Y :=
  (os.find? (fun c => (run c x).isSome)).bind (run · x)

/-- `union`: the sum, resolved by the first admitter. Over lawful, pairwise compatible options
    the order is unobservable (`altCodec_perm`). -/
def altCodec (os : List (Codec V A M)) (μA : Option M) : Codec V A M where
  T v := ∃ o ∈ os, o.T v
  μ := μA
  f o := select os (·.f o)

/-! ### How a union resolves

At each orientation, the first option that acts answers. -/

/-- **What a selection produces**: the first option that acts answered. -/
theorem select_eq_some {X Y : Type} {os : List (Codec V A M)} {run : Codec V A M → X → Option Y}
    {x : X} {y : Y} :
    select os run x = some y ↔
      ∃ o, os.find? (fun c => (run c x).isSome) = some o ∧ run o x = some y := by
  unfold select
  cases os.find? (fun c => (run c x).isSome) <;> simp

/-- …and it routes through an option that acts. -/
theorem select_admits {X Y : Type} {os : List (Codec V A M)} {run : Codec V A M → X → Option Y}
    {x : X} {y : Y} (h : select os run x = some y) :
    ∃ o ∈ os, (run o x).isSome = true ∧ run o x = some y := by
  obtain ⟨o, hf, hr⟩ := select_eq_some.mp h
  exact ⟨o, List.mem_of_find?_eq_some hf, List.find?_some (p := fun c => (run c x).isSome) hf, hr⟩

/-- **What a union sends**: the first option that acts at the input sent the input. -/
theorem altCodec_f {os : List (Codec V A M)} {μA : Option M} {o : Orient} {x : Side V A o.c}
    {y : Side V A o.s} :
    (altCodec os μA).f o x = some y ↔
      ∃ c, os.find? (fun c => (c.f o x).isSome) = some c ∧ c.f o x = some y := select_eq_some

/-- The map of a union at an orientation, for a rewrite. The lemma rewrites the write and the
    read, because `e` and `p` reduce to `f`. -/
theorem altCodec_f_def (os : List (Codec V A M)) (μA : Option M) (o : Orient) :
    (altCodec os μA).f o = select os (·.f o) := rfl

/-- A sum routes through an option that acts, at each orientation. -/
theorem altCodec_admits {os : List (Codec V A M)} {μA : Option M} {o : Orient}
    {x : Side V A o.c} {y : Side V A o.s} (h : (altCodec os μA).f o x = some y) :
    ∃ c ∈ os, (c.f o x).isSome = true ∧ c.f o x = some y := select_admits h

/-! ## Carriers — the pair is on `T` -/

/-- The carrier, likewise: `e` only writes what `pV` matched, `p` only reads what `pV`
    built. -/
theorem carrier_pointCodec {α : Type} {pV : Ctor α V} {pA : Ctor α A} {μ₀ : M} :
    Carrier (pointCodec pV pA μ₀) := by
  refine ⟨?_, ?_⟩
  · intro v a h
    obtain ⟨x, hx, _⟩ := Option.map_eq_some_iff.mp h
    exact ⟨x, pV.into_out hx⟩
  · intro a v h
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨x, rfl⟩

theorem carrier_through {c : Codec V A M} {f g : V → V} (hc : Carrier c)
    (hlaw : LawfulCore member c) (hfg : ∀ v, (c.e v).isSome → f (g v) = v) :
    Carrier (c.through f g) where
  domE he := hc.domE (through_e.mp he)
  ranP hp := by
    obtain ⟨w, hw, rfl⟩ := through_p.mp hp
    show c.T (f (g w))
    rw [hfg w (hlaw.canon hw)]
    exact hc.ranP hw

/-- The two-sided restriction is on its carrier when the inner codec is. -/
theorem carrier_refine2 {c : Codec V A M} (h : Carrier c) (qV : V → Bool) (qA : A → Bool) :
    Carrier (refine2 c qV qA) where
  domE he := let ⟨hq, he', _⟩ := refine2_f.mp he; ⟨h.domE he', hq⟩
  ranP hp := let ⟨_, hp', hq⟩ := refine2_f.mp hp; ⟨h.ranP hp', hq⟩

theorem carrier_restrict {c : Codec V A M} (hc : Carrier c) (q : V → Bool) :
    Carrier (c.restrict q) :=
  carrier_refine2 hc q _

/-- `alternate reader`: the migration lands in `T` because §3's `ran(r) ⊆ dom(e)` puts it in
    `dom(e)`, and `e`'s domain is `T`. The doc writes `r : 𝔸 ⇀ T` directly; this is the
    same premise arrived at through the one the proof already needs. -/
theorem carrier_extendRead {c : Codec V A M} {r : A → Option V} (hc : Carrier c)
    (hran : ∀ a v, r a = some v → (c.e v).isSome) :
    Carrier (c.extendRead r) where
  domE he := hc.domE (extendRead_e.mp he)
  ranP hp := by
    rcases extendRead_p.mp hp with hcv | ⟨-, hrv⟩
    · exact hc.ranP hcv
    · obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hran _ _ hrv)
      exact hc.domE ha'

theorem carrier_altCodec {os : List (Codec V A M)} {μA : Option M}
    (h : ∀ o ∈ os, Carrier o) : Carrier (altCodec os μA) := by
  refine ⟨?_, ?_⟩
  · intro v a he
    obtain ⟨o, ho, -, hoe⟩ := altCodec_admits he
    exact ⟨o, ho, (h o ho).domE hoe⟩
  · intro a v hp
    obtain ⟨o, ho, -, hop⟩ := altCodec_admits hp
    exact ⟨o, ho, (h o ho).ranP hop⟩

/-! ## Lawfulness — proved -/

/-- §2's laws for any pair of prisms. The one premise a prism pair does not already supply is
    which member the attribute side stamps. Everything else is `out_into` and `into_out`. -/
theorem lawful_pointCodec {α : Type} {pV : Ctor α V} {pA : Ctor α A} {μ₀ : M}
    (hμ : ∀ x, member (pA.into x) = μ₀) :
    Lawful member (pointCodec pV pA μ₀) where
  -- match, rebuild, match again: `out_into` at the stored side, `into_out` at the caller side
  inv {o x y} h := by
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (congrArg (Option.map (Ctor.side pV pA o.c).into)
      ((Ctor.side pV pA o.s).out_into z)).trans
      (congrArg some ((Ctor.side pV pA o.c).into_out hz).symm)
  -- everything written is `pA.into` of something
  writes hm _ _ he := by
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp he
    cases hm; exact hμ x

theorem LawfulCore.through {c : Codec V A M} (h : LawfulCore member c) {f g : V → V}
    (hiso : IsoCancels c f g) :
    LawfulCore member (c.through f g) where
  retract he := through_p.mpr ⟨_, h.retract (through_e.mp he),
    (hiso.1 _ (by rw [through_e.mp he]; rfl)).symm⟩
  canon hp := by
    obtain ⟨w, hw, rfl⟩ := through_p.mp hp
    show (c.e (f (g w))).isSome
    rw [hiso.2 w (h.canon hw)]
    exact h.canon hw
  writes := by intro μ hμ t a he; exact h.writes hμ (through_e.mp he)

/-- `held` preserves the laws: the core lemma, plus canonical reads through the iso. -/
theorem Lawful.through {c : Codec V A M} (h : Lawful member c) {f g : V → V}
    (hiso : IsoCancels c f g) :
    Lawful member (c.through f g) :=
  .ofRC (LawfulCore.through h.core hiso).retract
    (by
      intro a t hp
      obtain ⟨w, hw, rfl⟩ := through_p.mp hp
      rw [through_e, hiso.2 w (h.defined hw)]; exact h.canon hw)
    (LawfulCore.through h.core hiso).writes

/-- The two-sided restriction keeps the laws, and owes nothing. One proof serves each
    orientation. -/
theorem Lawful.refine2 {c : Codec V A M} (hc : Lawful member c) (qV : V → Bool)
    (qA : A → Bool) : Lawful member (refine2 c qV qA) where
  inv h := let ⟨hq, h', hq'⟩ := refine2_f.mp h; refine2_f.mpr ⟨hq', hc.inv h', hq⟩
  writes hμ _ _ he := hc.writes hμ (refine2_f.mp he).2.1

theorem Lawful.restrict {c : Codec V A M} (h : Lawful member c) (q : V → Bool) :
    Lawful member (c.restrict q) :=
  h.refine2 q _

theorem LawfulCore.extendRead {c : Codec V A M} (h : LawfulCore member c) {r : A → Option V}
    (hran : ∀ a v, r a = some v → (c.e v).isSome) :
    LawfulCore member (c.extendRead r) where
  retract he := extendRead_p.mpr (.inl (h.retract (extendRead_e.mp he)))
  canon hp := (extendRead_p.mp hp).elim h.canon fun ⟨_, hr⟩ => hran _ _ hr
  writes := by intro μ hμ t a he; exact h.writes hμ (extendRead_e.mp he)

end Calculus.Alg
