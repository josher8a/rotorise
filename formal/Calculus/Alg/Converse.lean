import Calculus.Alg.Agree

/-!
# The adapter and the one-sided `held`

`adapt2` is the adapter with a pair at each absolute side. Each pair reads from its own side: the
first function acts on the value that enters from the side, and the second on the value that exits
to the side. `held1 s` is the one-sided `held`: the adapter with a pair at the side `s` and the
identity at the other side, restricted at `s` by an outer codec. A two-sided adapter is two nested
one-sided ones (`held1_nest`). `Obl1` is the obligation of the one-sided adapter: one `IsoCancelsAt`
at its side, and the member fact where its side holds the attributes. At the side `false`, the
one-sided `held` is the host form (`held1_host`).

The object codec reads the map payload at each orientation (`objectCodec_f`).
-/

namespace Calculus.Alg

variable {V M : Type}

/-! ## The adapter and the one-sided `held` -/

/-- **An adapter pair**: the entry function and the exit function. -/
abbrev PairAt (V : Type) : Type :=
  (V → V) × (V → V)

/-- **The pairs of a one-sided adapter**: the pair `w` at the side `s`, and the identity at the
    other side. -/
abbrev PairAt.one (s : Bool) (w : PairAt V) : Bool → PairAt V :=
  Orient.place (X := fun _ => PairAt V) (Orient.at s) w (id, id)

/-- The pair of a one-sided adapter at the other side is the identity. -/
theorem PairAt.one_ne (s : Bool) (w : PairAt V) : ∀ t, t ≠ s → PairAt.one s w t = (id, id)
  | false, h => by cases s; exact absurd rfl h; rfl
  | true, h => by cases s; rfl; exact absurd rfl h

/-- **The adapter**, with a pair at each absolute side. One formula serves each orientation: the
    entry function of the caller side acts on the input, and the exit function of the stored side
    acts on the output. -/
def adapt2 (c : Codec V M) (π : Bool → PairAt V) : Codec V M where
  T v := c.T ((π false).1 v)
  μ := c.μ
  f o x := (c.f o ((π o.c).1 x)).map (π o.s).2

/-- The map of the adapter at an orientation, for a rewrite. -/
theorem adapt2_f (c : Codec V M) (π : Bool → PairAt V) (o : Orient)
    (x : V) : (adapt2 c π).f o x = (c.f o ((π o.c).1 x)).map (π o.s).2 := rfl

/-- **The one-sided `held` at the side `s`**: the adapter with the pair `w` at `s` and the
    identity at the other side, restricted at `s` by the domain of the outer `P` at `s`. The other
    side has no restriction. -/
def held1 {M₁ : Type} (s : Bool) (c : Codec V M) (P : Codec V M₁) (w : PairAt V) :
    Codec V M :=
  refine2 (adapt2 c (PairAt.one s w)) (fun v => false != s || (P.e v).isSome)
    (fun a => true != s || (P.p a).isSome)

/-- **The adapter at the side `false` is `through`**: the pair at the side `true` is the
    identity. -/
theorem adapt2_host (c : Codec V M) (w : PairAt V) :
    adapt2 c (PairAt.one false w) = c.through w.1 w.2 := by
  exact Codec.ext rfl rfl (funext fun v => congrFun Option.map_id (c.e (w.1 v))) rfl

/-- **The one-sided `held` at the side `false` is the host `held`**: `through`, restricted by the
    write domain of the outer. -/
theorem held1_host {M₁ : Type} (c : Codec V M) (P : Codec V M₁) (w : PairAt V) :
    held1 false c P w = (c.through w.1 w.2).restrict fun v => (P.e v).isSome := by
  rw [held1, adapt2_host]; rfl

/-- **A two-sided adapter is two nested one-sided ones**: the side `false` inside, and the side
    `true` outside. The pairs of the two sides and the two outers stay apart. -/
theorem held1_nest {M₁ M₂ : Type} (c : Codec V M) (oV : Codec V M₁) (oA : Codec V M₂)
    (wV : PairAt V) (wA : PairAt V) :
    held1 true (held1 false c oV wV) oA wA =
      refine2 (adapt2 c (Orient.place (X := fun _ => PairAt V) .host wV wA))
        (fun v => (oV.e v).isSome) (fun a => (oA.p a).isSome) := by
  refine Codec.ext ?_ rfl ?_ ?_
  · funext v
    show ((c.T (wV.1 v) ∧ (oV.e v).isSome = true) ∧ true = true) =
      (c.T (wV.1 v) ∧ (oV.e v).isSome = true)
    simp
  · funext v
    show (if true = true then
        (Option.map wA.2 (if (oV.e v).isSome = true then
          (Option.map id (c.e (wV.1 v))).bind fun a => if true = true then some a else none
          else none)).bind fun a => if (oA.p a).isSome = true then some a else none
        else none) =
      if (oV.e v).isSome = true then
        (Option.map wA.2 (c.e (wV.1 v))).bind fun a => if (oA.p a).isSome = true then some a else none
      else none
    cases (oV.e v).isSome <;> cases c.e (wV.1 v) <;> simp
  · funext a
    show (if (oA.p a).isSome = true then
        (Option.map id (if true = true then
          (Option.map wV.2 (c.p (wA.1 a))).bind fun v => if (oV.e v).isSome = true then some v else none
          else none)).bind fun v => if true = true then some v else none
        else none) =
      if (oA.p a).isSome = true then
        (Option.map wV.2 (c.p (wA.1 a))).bind fun v => if (oV.e v).isSome = true then some v else none
      else none
    cases (oA.p a).isSome <;> cases c.p (wA.1 a) <;> simp

/-- A gate whose predicate admits every output is the domain of the map. -/
theorem gate_eq_isSome {X Y : Type} {m : X → Option Y} {q : Y → Bool} {x : X}
    (h : ∀ y, m x = some y → q y = true) : gate m q x = (m x).isSome := by
  unfold gate
  cases hx : m x with
  | none => rfl
  | some y => exact h y hx

/-- A gate that passes sees an output. -/
theorem gate_isSome {X Y : Type} {m : X → Option Y} {q : Y → Bool} {x : X}
    (h : gate m q x = true) : (m x).isSome = true := by
  revert h
  unfold gate
  cases m x <;> simp

/-- **The gate of the adapter at an orientation** is the gate of its inner codec, after the entry
    function of the caller side, and before the exit function of the stored side. -/
theorem adapt2_gate (c : Codec V M) (π : Bool → PairAt V) (o : Orient)
    (q : V → Bool) (x : V) :
    gate ((adapt2 c π).f o) q x = gate (c.f o) (q ∘ (π o.s).2) ((π o.c).1 x) := by
  simp only [gate, adapt2]
  cases c.f o ((π o.c).1 x) <;> rfl

/-- **The domain of the one-sided `held` at an orientation**: the outer admits the input where
    the side `s` is the caller side, and the inner codec sends the entry image to an output whose
    exit image the outer reads back where the side `s` is the stored side. -/
theorem held1_f_isSome {M₁ : Type} (s : Bool) (c : Codec V M) (P : Codec V M₁)
    (w : PairAt V) : ∀ (o : Orient) (x : V),
    ((held1 s c P w).f o x).isSome =
      ((o.c != s || (P.f o x).isSome) &&
        gate (c.f o) (fun y => o.s != s || (P.f o.op ((PairAt.one s w o.s).2 y)).isSome)
          ((PairAt.one s w o.c).1 x)) :=
  Orient.both (P := fun o => ∀ (x : V),
    ((held1 s c P w).f o x).isSome =
      ((o.c != s || (P.f o x).isSome) &&
        gate (c.f o) (fun y => o.s != s || (P.f o.op ((PairAt.one s w o.s).2 y)).isSome)
          ((PairAt.one s w o.c).1 x)))
    (fun v => by rw [held1, refine2_e_isSome, adapt2_gate]; rfl)
    (fun a => by rw [held1, refine2_p_isSome, adapt2_gate]; rfl)

/-- **One adapter over two agreeing inner codecs agrees.** -/
theorem agreeS_adapt2 {side : Bool} {c c' : Codec V M} {π : Bool → PairAt V}
    (h : AgreeS side c c') : AgreeS side (adapt2 c π) (adapt2 c' π) := by
  cases side
  · intro a t w ht hw
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp ht
    obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.mp hw
    rw [(h : Agree .dual c c') ((π true).1 a) u u' hu hu']
  · intro v a b ha hb
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
    rw [(h : Agree .host c c') ((π false).1 v) a' b' ha' hb']

/-- **One `held` over two agreeing inner codecs agrees**, whatever the outers. -/
theorem agreeS_held1 {side s : Bool} {M₁ M₁' : Type} {c c' : Codec V M}
    {P : Codec V M₁} {P' : Codec V M₁'} {w : PairAt V} (h : AgreeS side c c') :
    AgreeS side (held1 s c P w) (held1 s c' P' w) :=
  agree_sub_left (sub_refine2_self _ _ _)
    (agree_sub_right (sub_refine2_self _ _ _) (agreeS_adapt2 h))

/-- The stored exit function keeps the member of every written attribute. -/
def KeepsMember (member : V → M) (c : Codec V M) (k : V → V) : Prop :=
  ∀ v a, c.e v = some a → member (k a) = member a

/-- **The member fact of an exit function at an absolute side.** The attributes carry the
    members, so the fact binds at the side `true`, and the side `false` owes nothing. -/
def KeepsMemberAt (member : V → M) (c : Codec V M) :
    (s : Bool) → (V → V) → Prop
  | false, _ => True
  | true, k => KeepsMember member c k

/-- **The obligation of the one-sided adapter at the side `s`**: the pair cancels at the
    orientation whose caller side is `s`, and the exit function keeps the member where `s` is the
    side of the attributes. A `held` owes one obligation for one half, because the caller code is
    opaque: the model cannot derive the obligation of one half from the obligation of the other.
    A two-sided adapter is two nested `held`s, so it owes one obligation for each half. -/
def Obl1 (member : V → M) (c : Codec V M) (s : Bool) (w : PairAt V) : Prop :=
  IsoCancelsAt (Orient.at s) c w.1 w.2 ∧ KeepsMemberAt member c s w.2

/-- **The adapter keeps the laws**, from the cancellation of the pair at each side and the member
    fact of the exit function at the side `true`. -/
theorem Lawful.adapt2 {member : V → M} {c : Codec V M} (hc : Lawful member c)
    {π : Bool → PairAt V} (h : ∀ s, IsoCancelsAt (Orient.at s) c (π s).1 (π s).2)
    (hm : KeepsMember member c (π true).2) : Lawful member (adapt2 c π) := by
  obtain ⟨hV1, hV2⟩ := h false
  obtain ⟨hA1, hA2⟩ := h true
  refine .ofRC (fun {v a'} he => ?_) (fun {a' w} hp => ?_) (fun {μ} hμ {v a'} he => ?_)
  · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp he
    have hr := hc.retract ha
    have hk : (π true).1 ((π true).2 a) = a := hA2 a (Option.isSome_iff_exists.mpr ⟨_, hr⟩)
    simp only [adapt2_f, hk, hr, Option.map_some, hV1 v (Option.isSome_iff_exists.mpr ⟨_, ha⟩)]
  · obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hp
    have hcu := hc.canon hu
    have hfg : (π false).1 ((π false).2 u) = u := hV2 u (Option.isSome_iff_exists.mpr ⟨_, hcu⟩)
    simp only [adapt2_f, hfg, hcu, Option.map_some, hA1 a' (Option.isSome_iff_exists.mpr ⟨_, hu⟩)]
  · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp he
    rw [hm ((π false).1 v) a ha]
    exact hc.writes hμ ha

/-- **The one-sided `held` keeps the laws**, from its one obligation. The other side holds the
    identity, which cancels and keeps every member. -/
theorem Lawful.held1 {member : V → M} {M₁ : Type} {c : Codec V M} (hc : Lawful member c)
    {s : Bool} (P : Codec V M₁) {w : PairAt V} (h : Obl1 member c s w) :
    Lawful member (held1 s c P w) :=
  (hc.adapt2 (fun t => by
      cases s <;> cases t
      all_goals first | exact h.1 | exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
    (by cases s; exacts [fun _ _ _ => rfl, h.2])).refine2 _ _

/-- The adapter is on its carrier when the inner codec is, and the pair of the side `false`
    cancels on the written values. -/
theorem carrier_adapt2 {member : V → M} {c : Codec V M} (hc : Carrier c)
    (hlaw : LawfulCore member c) (π : Bool → PairAt V)
    (hfg : ∀ v, (c.e v).isSome → (π false).1 ((π false).2 v) = v) : Carrier (adapt2 c π) where
  domE he := let ⟨_, ha, _⟩ := Option.map_eq_some_iff.mp he; hc.domE ha
  ranP hp := by
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hp
    have hT : c.T w := hc.ranP hw
    rw [← hfg w (hlaw.canon hw)] at hT
    exact hT

/-- **The one-sided `held` is on its carrier**, from its one obligation. -/
theorem carrier_held1 {member : V → M} {M₁ : Type} {c : Codec V M} (hc : Carrier c)
    (hlaw : LawfulCore member c) {s : Bool} (P : Codec V M₁) {w : PairAt V}
    (h : Obl1 member c s w) : Carrier (held1 s c P w) :=
  carrier_refine2 (carrier_adapt2 hc hlaw _ (by cases s; exacts [h.1.2, fun _ _ => rfl])) _ _

/-! ## The object codec at an orientation -/

/-- **The object codec at an orientation**: read the prism, pass the presence guard, run each
    entry at the orientation, and build with the prism. -/
theorem objectCodec_f (m : Ctor (MapOf V) V) (μM : M)
    (sems : MapOf (FieldSem V M)) {rest : RestSem V M} :
    ∀ (o : Orient) (x : V), (objectCodec m μM sems rest).f o x =
      ((m.out x).bind fun q => if valPresentB sems q.1 = true then
        (funImage fun k => (entryCodec sems (rcOf rest) k.1).bind fun c => c.f o (q.2 k)).map
          (fun g => (⟨q.1, g⟩ : MapOf V)) else none).map m.into :=
  Orient.both (P := fun o => ∀ x, (objectCodec m μM sems rest).f o x =
      ((m.out x).bind fun q => if valPresentB sems q.1 = true then
        (funImage fun k => (entryCodec sems (rcOf rest) k.1).bind fun c => c.f o (q.2 k)).map
          (fun g => (⟨q.1, g⟩ : MapOf V)) else none).map m.into)
    (fun _ => rfl)
    (fun _ => rfl)

end Calculus.Alg
