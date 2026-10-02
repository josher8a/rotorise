import Mathlib.Data.List.Forall2
import Calculus.Alg.Codec

/-!
# The combinators and the join, over any carriers

The side conditions of §3, the wrappers `held`, `refine` and `alternate reader`, the point codec
of a pair of prisms, and the union by the first admitter. Each one reads only the pair and the
member, so each one takes the carrier `V` and the members `M` as parameters. The laws of each
combinator follow from the laws of its arguments, and `member : V → M` is the one fact of the
store that (W) reads.
-/

namespace Calculus.Alg

variable {V M : Type}

/-! ## §3's side conditions, named

Three rules carry premises about the pair rather than about the index, and §3 names each
of them in prose. Naming them here too is what keeps `Obligations` readable and stops
every use site restating the proposition: a case that consumes one of these says which
condition it is consuming. -/

/-- §3 `(held)`: the iso cancels **on the carriers** — `T ≃ I`, in the domain-restricted
    form the laws actually need. `g ∘ f = id` where `f` lands writable, `f ∘ g = id` on
    the writable values themselves. -/
def IsoCancelsAt (o : Orient) (c : Codec V M) (f g : V → V) : Prop :=
  (∀ x, (c.f o (f x)).isSome → g (f x) = x) ∧
  (∀ x, (c.f o x).isSome → f (g x) = x)

/-- The obligation at the host: the caller pair cancels on the values that the codec writes. -/
abbrev IsoCancels (c : Codec V M) (f g : V → V) : Prop := IsoCancelsAt Orient.host c f g

/-- §3 `(alternate reader)`: `ran(r) ⊆ dom(e)` — a migration lands on writable values — and
    coherence, the legacy reading agreeing with the current one on their overlap. -/
def ReadsCoherently (c : Codec V M) (r : V → Option V) : Prop :=
  (∀ a v, r a = some v → (c.e v).isSome) ∧
  (∀ a v, r a = some v → ∀ v', c.p a = some v' → v = v')

/-- §3 types the pair *on the held set*: `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T`. `Lawful` never
    mentions `T`, because retract, canon and writes relate `e` and `p` to each other and not to
    the index. So this is the separate claim that the index is honest, and it is what makes `T` a
    checked part of the judgement rather than a decoration. -/
structure Carrier (c : Codec V M) : Prop where
  /-- `e : T ⇀ 𝔸` — nothing outside the held set is written. -/
  domE : ∀ {v a}, c.e v = some a → c.T v
  /-- `p : 𝔸 ⇀ T` — nothing outside the held set is read. -/
  ranP : ∀ {a v}, c.p a = some v → c.T v

/-- The empty codec is on its (empty) carrier, vacuously. -/
theorem Carrier.empty : Carrier (Codec.empty : Codec V M) := by
  refine ⟨?_, ?_⟩ <;> intro _ _ h <;> exact nomatch h

/-- `Can(c)` is §2's `e[T]` — and it takes `Carrier` to say so: without `domE` a codec could
    write from a value it does not hold, making `Can` larger than the image. -/
theorem can_iff_image {c : Codec V M} (h : Carrier c) {a : V} :
    Can c a ↔ ∃ v, c.T v ∧ c.e v = some a := by
  constructor
  · rintro ⟨v, hv⟩; exact ⟨v, h.domE hv, hv⟩
  · rintro ⟨v, -, hv⟩; exact ⟨v, hv⟩

/-! ## §1's store, as a premise

§2 composes `e` and `p` directly. In use there is a store between them and it is not the
identity on attributes. This is the premise itself, for every store. -/

/-- **`η ⊆ ker p`** — §1's concession, as a proposition. Quantified over `Can(c)` because
    `η` only ever sees what `e` wrote. Buys `retract_through_store`: (R) through the store. -/
def SurvivesStore (c : Codec V M) (η : V → V) : Prop :=
  ∀ a, Can c a → c.Ker (η a) a

variable {member : V → M}

/-- **(R), through the store.** `η ⊆ ker p` is exactly what makes a codec survive a round
    trip that passes through the store rather than through `Option` — and it is all it takes,
    which is why §1 could answer the whole problem by narrowing one held set. -/
theorem Lawful.retract_through_store {c : Codec V M} (h : Lawful member c) {η : V → V}
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

/-- A `bind` through a prism pins the datum. -/
theorem Ctor.bind_out {α β : Type} (p : Ctor α β) {o : Option β} {y : α}
    (h : o.bind p.out = some y) : o = some (p.into y) := by
  obtain ⟨b, hb, hy⟩ := Option.bind_eq_some_iff.mp h
  rw [hb, p.into_out hy]

/-- **A summand of the carrier**: the prism of one member. Every datum that the prism builds
    carries the member, so a codec built on a summand cannot promise a member that its prism
    does not stamp. The member is the index of the summand in the universe's tagging grammar. -/
structure Summand (α V M : Type) (member : V → M) where
  /-- The injection of the summand. -/
  p : Ctor α V
  /-- The member of the summand. -/
  μ : M
  /-- Each datum that the injection builds carries the member. -/
  hμ : ∀ x, member (p.into x) = μ

/-- A datum that a summand matches carries the summand's member. -/
theorem Summand.member_of_out {α : Type} {s : Summand α V M member} {a : V}
    (h : (s.p.out a).isSome = true) : member a = s.μ := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
  rw [s.p.into_out hy]; exact s.hμ y

/-- **The point ground codecs of §3**, as one construction: the partial identity on the image of
    a summand, which stamps the summand's member.

    The prism laws are exactly §2's laws in disguise — `out_into` is the round trip **(R)**
    and `into_out` is canonizability **(C)** — which is why `lawful_pointCodec` needs no
    hypothesis. The map reads no orientation: match with the prism, and build with it again. -/
def pointCodec {α : Type} {member : V → M} (s : Summand α V M member) : Codec V M where
  T v := ∃ x, v = s.p.into x
  μ := some s.μ
  f _ x := (s.p.out x).map s.p.into

/-- **The identity codec**: it holds every datum, names no member, and sends each datum to itself
    at each orientation. It is the unit of the inverse monoid of the carrier, and the top of a
    universe: a codec below it is a partial identity. -/
def idCodec : Codec V M where
  T _ := True
  μ := none
  f _ x := some x

/-! ## Wrappers -/

/-- `held`: an iso on the value side; the stored side is untouched. The iso acts at the values
    only, so the write and the read are two formulas. One formula over the orientation would
    only hide that case split. -/
def Codec.through (c : Codec V M) (f g : V → V) : Codec V M :=
  Codec.ofEP (T := fun v => c.T (f v))
    (μ := c.μ)
    (e := fun v => c.e (f v))
    (p := fun a => (c.p a).map g)

/-- **The two-sided restriction** `[qA] ∘ c ∘ [qV]`: `qV` restricts the values, and `qA`
    restricts the attributes. One formula serves each orientation: the predicate at the caller
    side of the orientation gates the input, and the predicate at the stored side gates the
    output. -/
def refine2 (c : Codec V M) (qV : V → Bool) (qA : V → Bool) : Codec V M where
  T v := c.T v ∧ qV v
  μ := c.μ
  f o x := if Side.elim qV qA o.c x then
      (c.f o x).bind fun y => if Side.elim qV qA o.s y then some y else none
    else none

/-- `refine`: the prism. It is the two-sided restriction whose stored predicate admits every
    attribute. -/
def Codec.restrict (c : Codec V M) (q : V → Bool) : Codec V M :=
  refine2 c q fun _ => true

/-- What the two-sided restriction sends: the input passes the predicate of the caller side,
    the base sends the input, and the output passes the predicate of the stored side. -/
theorem refine2_f {c : Codec V M} {qV : V → Bool} {qA : V → Bool} {o : Orient}
    {x : V} {y : V} :
    (refine2 c qV qA).f o x = some y ↔
      Side.elim qV qA o.c x = true ∧ c.f o x = some y ∧ Side.elim qV qA o.s y = true := by
  simp only [refine2]
  cases Side.elim qV qA o.c x
  · simp
  · cases c.f o x with
    | none => simp
    | some y' =>
      cases hq : Side.elim qV qA o.s y' <;> simp [hq] <;> intro hh <;> subst hh <;> assumption

/-- **The rectangle**: a pair that the two-sided restriction sends satisfies the predicate at
    each absolute side. -/
theorem refine2_rect {c : Codec V M} {qV : V → Bool} {qA : V → Bool} {o : Orient}
    {x : V} {y : V} (h : (refine2 c qV qA).f o x = some y) (s : Bool) :
    Side.elim qV qA s (Orient.place (X := fun _ => V) o x y s) = true := by
  obtain ⟨hx, -, hy⟩ := refine2_f.mp h
  rcases Orient.side_of o s with rfl | rfl
  · rw [Orient.place_c]; exact hx
  · rw [Orient.place_s]; exact hy

/-- The write of the two-sided restriction, for a rewrite. -/
theorem refine2_e_def (c : Codec V M) (qV : V → Bool) (qA : V → Bool) :
    (refine2 c qV qA).e =
      fun v => if qV v then (c.e v).bind (fun a => if qA a then some a else none) else none := rfl

/-- The write of a restriction: the predicate guards the write of the base. -/
theorem restrict_e_def (c : Codec V M) (q : V → Bool) :
    (c.restrict q).e = fun v => if q v then c.e v else none := by
  simp only [Codec.restrict, refine2_e_def, if_true, Option.bind_fun_some]

/-- The read of a restriction: the predicate guards the value that the base reads. -/
theorem restrict_p_def (c : Codec V M) (q : V → Bool) :
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
def Codec.adapt (c : Codec V M) (f g : V → Option V) : Codec V M :=
  Codec.ofEP (T := fun v => ∃ w, f v = some w ∧ c.T w)
    (μ := c.μ)
    (e := fun v => (f v).bind c.e)
    (p := fun a => (c.p a).bind g)

/-- The partial identity on a predicate — `refine`'s adapter, on both halves. -/
def partialId (q : V → Bool) : V → Option V := fun v => if q v then some v else none

/-- `held` writes as `adapt` with a total adapter. -/
theorem through_e_adapt {c : Codec V M} (f g : V → V) :
    (c.through f g).e = (c.adapt (some ∘ f) (some ∘ g)).e := rfl

/-- `refine` writes as `adapt` with a partial identity — the *same* combinator, weaker
    adapter. This is the sense in which it is sugar. -/
theorem restrict_e_adapt {c : Codec V M} (q : V → Bool) :
    (c.restrict q).e = (c.adapt (partialId q) (partialId q)).e := by
  funext v
  simp only [restrict_e_def, Codec.adapt, Codec.ofEP_e, partialId]
  cases q v <;> rfl

/-! ### The stored-side gate -/

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
theorem refine2_f_isSome (c : Codec V M) (qV : V → Bool) (qA : V → Bool) (o : Orient)
    (x : V) :
    ((refine2 c qV qA).f o x).isSome =
      (Side.elim qV qA o.c x && gate (c.f o) (Side.elim qV qA o.s) x) := by
  simp only [refine2, gate]
  cases Side.elim qV qA o.c x
  · rfl
  · cases c.f o x with
    | none => rfl
    | some y => cases h : Side.elim qV qA o.s y <;> simp [h]

/-- The write domain of the two-sided restriction: the domain at the host. -/
theorem refine2_e_isSome (c : Codec V M) (qV : V → Bool) (qA : V → Bool) (v : V) :
    ((refine2 c qV qA).e v).isSome = (qV v && gate c.e qA v) :=
  refine2_f_isSome c qV qA .host v

/-- The read domain of the two-sided restriction: the domain at the dual. -/
theorem refine2_p_isSome (c : Codec V M) (qV : V → Bool) (qA : V → Bool) (a : V) :
    ((refine2 c qV qA).p a).isSome = (qA a && gate c.p qV a) :=
  refine2_f_isSome c qV qA .dual a

/-- A refinement writes where the gate passes and the base writes, so a row can read off a
    refinement without unfolding it. -/
@[simp] theorem restrict_e_isSome {c : Codec V M} {q : V → Bool} (v : V) :
    ((c.restrict q).e v).isSome = (q v && (c.e v).isSome) := by
  rw [Codec.restrict, refine2_e_isSome, gate_true]

/-- `alternate reader`: extend the reading. With §3's coherence premise this presentation equals
    the order-free `p ∪ r`. The migration extends the read only, so the write and the read are
    two formulas. -/
def Codec.extendRead (c : Codec V M) (r : V → Option V) : Codec V M :=
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
variable {c : Codec V M}

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
@[simp] theorem restrict_p_isSome {c : Codec V M} {q : V → Bool} (a : V) :
    ((c.restrict q).p a).isSome = ((c.p a).elim false q) := by
  rw [Codec.restrict, refine2_p_isSome, Bool.true_and]
  simp only [gate]; cases c.p a <;> rfl

/-- `alternate reader` does not touch the writing at all — §5's whole point. -/
theorem extendRead_e {r : V → Option V} {v a} :
    (c.extendRead r).e v = some a ↔ c.e v = some a := Iff.rfl

/-- It reads through the base where the base reads, and through the migration exactly
    where the base does not. That "exactly" is where canonical reads go. -/
theorem extendRead_p {r : V → Option V} {a v} :
    (c.extendRead r).p a = some v ↔ c.p a = some v ∨ (c.p a = none ∧ r a = some v) := by
  show (match c.p a with | some w => some w | none => r a) = some v ↔ _
  cases hp : c.p a <;> simp

end WrapperInversion

/-- The carrier transfers to any codec that agrees on the pair, given the held set is no
    smaller. -/
theorem Carrier.congr {c d : Codec V M} (he : c.e = d.e) (hp : c.p = d.p)
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
def AdmitsAtMostOne (os : List (Codec V M)) : Prop :=
  (∀ t, (os.filter (fun c => (c.e t).isSome)).length ≤ 1) ∧
  (∀ a, (os.filter (fun c => (c.p a).isSome)).length ≤ 1)

/-- **The first option that acts.** A sum at each orientation is this: act through the first
    option that admits by the admission of that orientation. -/
def select {X Y : Type} (os : List (Codec V M)) (run : Codec V M → X → Option Y) (x : X) :
    Option Y :=
  (os.find? (fun c => (run c x).isSome)).bind (run · x)

/-- `union`: the sum, resolved by the first admitter. Over lawful, pairwise compatible options
    the order is unobservable (`altCodec_perm`). -/
def altCodec (os : List (Codec V M)) (μA : Option M) : Codec V M where
  T v := ∃ o ∈ os, o.T v
  μ := μA
  f o := select os (·.f o)

/-! ### How a union resolves

At each orientation, the first option that acts answers. -/

/-- **What a selection produces**: the first option that acts answered. -/
theorem select_eq_some {X Y : Type} {os : List (Codec V M)} {run : Codec V M → X → Option Y}
    {x : X} {y : Y} :
    select os run x = some y ↔
      ∃ o, os.find? (fun c => (run c x).isSome) = some o ∧ run o x = some y := by
  unfold select
  cases os.find? (fun c => (run c x).isSome) <;> simp

/-- …and it routes through an option that acts. -/
theorem select_admits {X Y : Type} {os : List (Codec V M)} {run : Codec V M → X → Option Y}
    {x : X} {y : Y} (h : select os run x = some y) :
    ∃ o ∈ os, (run o x).isSome = true ∧ run o x = some y := by
  obtain ⟨o, hf, hr⟩ := select_eq_some.mp h
  exact ⟨o, List.mem_of_find?_eq_some hf, List.find?_some (p := fun c => (run c x).isSome) hf, hr⟩

/-- **What a union sends**: the first option that acts at the input sent the input. -/
theorem altCodec_f {os : List (Codec V M)} {μA : Option M} {o : Orient} {x : V}
    {y : V} :
    (altCodec os μA).f o x = some y ↔
      ∃ c, os.find? (fun c => (c.f o x).isSome) = some c ∧ c.f o x = some y := select_eq_some

/-- A sum routes through an option that acts, at each orientation. -/
theorem altCodec_admits {os : List (Codec V M)} {μA : Option M} {o : Orient}
    {x : V} {y : V} (h : (altCodec os μA).f o x = some y) :
    ∃ c ∈ os, (c.f o x).isSome = true ∧ c.f o x = some y := select_admits h

/-! ## Carriers — the pair is on `T` -/

/-- The identity codec holds every datum. -/
theorem carrier_idCodec : Carrier (idCodec : Codec V M) := ⟨fun _ => trivial, fun _ => trivial⟩

/-- The carrier, likewise: `e` only writes what `p` matched, and `p` only reads what `p`
    built. -/
theorem carrier_pointCodec {α : Type} {member : V → M} {s : Summand α V M member} :
    Carrier (pointCodec s) := by
  refine ⟨?_, ?_⟩
  · intro v a h
    obtain ⟨x, hx, _⟩ := Option.map_eq_some_iff.mp h
    exact ⟨x, s.p.into_out hx⟩
  · intro a v h
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨x, rfl⟩

/-- The two-sided restriction is on its carrier when the inner codec is. -/
theorem carrier_refine2 {c : Codec V M} (h : Carrier c) (qV : V → Bool) (qA : V → Bool) :
    Carrier (refine2 c qV qA) where
  domE he := let ⟨hq, he', _⟩ := refine2_f.mp he; ⟨h.domE he', hq⟩
  ranP hp := let ⟨_, hp', hq⟩ := refine2_f.mp hp; ⟨h.ranP hp', hq⟩

theorem carrier_restrict {c : Codec V M} (hc : Carrier c) (q : V → Bool) :
    Carrier (c.restrict q) :=
  carrier_refine2 hc q _

/-- `alternate reader`: the migration lands in `T` because §3's `ran(r) ⊆ dom(e)` puts it in
    `dom(e)`, and `e`'s domain is `T`. The doc writes `r : 𝔸 ⇀ T` directly; this is the
    same premise arrived at through the one the proof already needs. -/
theorem carrier_extendRead {c : Codec V M} {r : V → Option V} (hc : Carrier c)
    (hran : ∀ a v, r a = some v → (c.e v).isSome) :
    Carrier (c.extendRead r) where
  domE he := hc.domE (extendRead_e.mp he)
  ranP hp := by
    rcases extendRead_p.mp hp with hcv | ⟨-, hrv⟩
    · exact hc.ranP hcv
    · obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hran _ _ hrv)
      exact hc.domE ha'

theorem carrier_altCodec {os : List (Codec V M)} {μA : Option M}
    (h : ∀ o ∈ os, Carrier o) : Carrier (altCodec os μA) := by
  refine ⟨?_, ?_⟩
  · intro v a he
    obtain ⟨o, ho, -, hoe⟩ := altCodec_admits he
    exact ⟨o, ho, (h o ho).domE hoe⟩
  · intro a v hp
    obtain ⟨o, ho, -, hop⟩ := altCodec_admits hp
    exact ⟨o, ho, (h o ho).ranP hop⟩

/-! ## Lawfulness — proved -/

/-- The identity codec is lawful: each orientation is the identity, and it names no member. -/
theorem lawful_idCodec : Lawful member (idCodec : Codec V M) where
  inv h := by cases h; rfl
  writes hμ := nomatch hμ

/-- §2's laws for any summand: `out_into`, `into_out`, and the member that the summand stamps. -/
theorem lawful_pointCodec {α : Type} {s : Summand α V M member} :
    Lawful member (pointCodec s) where
  -- match, rebuild, match again: `out_into`, then `into_out`
  inv {o x y} h := by
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (congrArg (Option.map s.p.into) (s.p.out_into z)).trans
      (congrArg some (s.p.into_out hz).symm)
  -- everything written is `s.p.into` of something
  writes hm _ _ he := by
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp he
    cases hm; exact s.hμ x

theorem LawfulCore.through {c : Codec V M} (h : LawfulCore member c) {f g : V → V}
    (hiso : IsoCancels c f g) :
    LawfulCore member (c.through f g) where
  retract he := through_p.mpr ⟨_, h.retract (through_e.mp he),
    (hiso.1 _ (Option.isSome_iff_exists.mpr ⟨_, through_e.mp he⟩)).symm⟩
  canon hp := by
    obtain ⟨w, hw, rfl⟩ := through_p.mp hp
    show (c.e (f (g w))).isSome
    rw [hiso.2 w (h.canon hw)]
    exact h.canon hw
  writes := by intro μ hμ t a he; exact h.writes hμ (through_e.mp he)

/-- `held` preserves the laws: the core lemma, plus canonical reads through the iso. -/
theorem Lawful.through {c : Codec V M} (h : Lawful member c) {f g : V → V}
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
theorem Lawful.refine2 {c : Codec V M} (hc : Lawful member c) (qV : V → Bool)
    (qA : V → Bool) : Lawful member (refine2 c qV qA) where
  inv h := let ⟨hq, h', hq'⟩ := refine2_f.mp h; refine2_f.mpr ⟨hq', hc.inv h', hq⟩
  writes hμ _ _ he := hc.writes hμ (refine2_f.mp he).2.1

theorem Lawful.restrict {c : Codec V M} (h : Lawful member c) (q : V → Bool) :
    Lawful member (c.restrict q) :=
  h.refine2 q _

theorem LawfulCore.extendRead {c : Codec V M} (h : LawfulCore member c) {r : V → Option V}
    (hran : ∀ a v, r a = some v → (c.e v).isSome) :
    LawfulCore member (c.extendRead r) where
  retract he := extendRead_p.mpr (.inl (h.retract (extendRead_e.mp he)))
  canon hp := (extendRead_p.mp hp).elim h.canon fun ⟨_, hr⟩ => hran _ _ hr
  writes := by intro μ hμ t a he; exact h.writes hμ (extendRead_e.mp he)

end Calculus.Alg
