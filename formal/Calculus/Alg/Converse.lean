import Calculus.Alg.Agree

/-!
# The converse of a codec, and the two-sided wrappers

`conv c` swaps the two halves of a codec. `R c' c` says that `c'` has the converse graph of `c`:
the write of `c'` is the read of `c`, and the read of `c'` is the write of `c`.

`refine2` and `adapt2` are the two-sided forms of `restrict` and `through`. Each side of a codec
holds one pair, and each pair reads from its own side: the first function acts on the value that
enters from the side, and the second on the value that exits to the side. So the converse swaps
the two halves and changes no pair (`R.refine2`, `R.adapt2`). At the top of the stored side, the
two-sided form is the one-sided form (`refine2_host`, `adapt2_host`).

Each constructor of the term language has a converse that is the same constructor over the
converses of its parts (`altCodec_R`, `muCodec_R`, `listCodec_R`, `objectCodec_R`).
-/

namespace Calculus.Alg

variable {V A M : Type}

/-! ## The converse -/

/-- **The converse of a codec**: the read is the write, and the write is the read. The member
    names nothing on the stored side of the converse, so it is `Unit`. -/
def conv (c : Codec V A M) : Codec A V Unit :=
  { T := fun _ => True, μ := c.μ.map (fun _ => ()), e := c.p, p := c.e }

/-- `c'` has the converse graph of `c`. -/
def R {X Y N N' : Type} (c' : Codec Y X N') (c : Codec X Y N) : Prop := c'.e = c.p ∧ c'.p = c.e

/-- The converse graph is symmetric. -/
theorem R.symm {X Y N N' : Type} {c' : Codec Y X N'} {c : Codec X Y N} (h : R c' c) : R c c' :=
  ⟨h.2.symm, h.1.symm⟩

/-- The converse has the converse graph. -/
theorem R_conv (c : Codec V A M) : R (conv c) c := ⟨rfl, rfl⟩

/-- The converse of a lawful codec is lawful, with the trivial member. -/
theorem Lawful.conv {member : A → M} {c : Codec V A M} (h : Lawful member c) :
    Lawful (fun _ : V => ()) (conv c) where
  retract := h.canon
  canon := h.retract
  writes _ _ _ _ := rfl

/-- The converse holds every value, so it is on its carrier. -/
theorem carrier_conv (c : Codec V A M) : Carrier (conv c) := ⟨fun _ => trivial, fun _ => trivial⟩

/-- The converse of a codec on the dual carriers, back on the original carriers. -/
def unconv (c : Codec A V Unit) : Codec V A M :=
  { T := fun _ => True, μ := none, e := c.p, p := c.e }

/-- The inverse converse of a lawful codec is lawful, and names no member. -/
theorem Lawful.unconv {member : A → M} {c : Codec A V Unit} (h : Lawful (fun _ : V => ()) c) :
    Lawful member (unconv c : Codec V A M) :=
  ⟨h.canon, h.retract, fun hμ => nomatch hμ⟩

/-- Agreement on one half of two codecs is agreement on the other half of their inverse
    converses. -/
theorem agreeS_unconv {side : Bool} {c d : Codec A V Unit} (h : AgreeS side c d) :
    AgreeS (!side) (unconv c : Codec V A M) (unconv d) := by
  cases side <;> exact h

/-- Agreement on one half of two codecs is agreement on the other half of their converses. -/
theorem agreeS_conv {side : Bool} {c d : Codec V A M} (h : AgreeS (!side) c d) :
    AgreeS side (conv c) (conv d) := by
  cases side <;> exact h

/-! ## The two-sided wrappers -/

/-- **The two-sided restriction** `[qA] ∘ c ∘ [qV]`: `qV` restricts the caller side, and `qA`
    restricts the stored side. -/
def refine2 (c : Codec V A M) (qV : V → Bool) (qA : A → Bool) : Codec V A M :=
  { T := fun v => c.T v ∧ qV v
    μ := c.μ
    e := fun v => if qV v then (c.e v).bind (fun a => if qA a then some a else none) else none
    p := fun a => if qA a then (c.p a).bind (fun v => if qV v then some v else none) else none }

/-- **The two-sided adapter.** The caller pair is `(fV, gV)`: `fV` on entry from `V`, `gV` on exit
    to `V`. The stored pair is `(hA, kA)`: `hA` on entry from `A`, `kA` on exit to `A`. -/
def adapt2 (c : Codec V A M) (fV gV : V → V) (hA kA : A → A) : Codec V A M :=
  { T := fun v => c.T (fV v)
    μ := c.μ
    e := fun v => (c.e (fV v)).map kA
    p := fun a => (c.p (hA a)).map gV }

/-- **The two-sided `held`**: the adapter, restricted on each side by an outer codec. The caller
    outer restricts by its write domain, and the stored outer by its read domain. -/
def held2 {M₁ M₂ : Type} (c : Codec V A M) (oV : Codec V A M₁) (oA : Codec V A M₂)
    (fV gV : V → V) (hA kA : A → A) : Codec V A M :=
  refine2 (adapt2 c fV gV hA kA) (fun v => (oV.e v).isSome) (fun a => (oA.p a).isSome)

/-- **The converse of the two-sided restriction swaps the halves**, over any codec with the
    converse graph. -/
theorem R.refine2 {N : Type} {c' : Codec A V N} {c : Codec V A M} (h : R c' c)
    (qV : V → Bool) (qA : A → Bool) : R (refine2 c' qA qV) (refine2 c qV qA) := by
  obtain ⟨T, μ, e, p⟩ := c'
  obtain ⟨h1, h2⟩ := h
  subst h1 h2
  exact ⟨rfl, rfl⟩

/-- **The converse of the two-sided adapter swaps the halves**, with no dagger. -/
theorem R.adapt2 {N : Type} {c' : Codec A V N} {c : Codec V A M} (h : R c' c)
    (fV gV : V → V) (hA kA : A → A) : R (adapt2 c' hA kA fV gV) (adapt2 c fV gV hA kA) := by
  obtain ⟨T, μ, e, p⟩ := c'
  obtain ⟨h1, h2⟩ := h
  subst h1 h2
  exact ⟨rfl, rfl⟩

/-- **The converse of the two-sided `held` swaps the halves, the outers included.** The caller
    outer of the dual is the converse of the stored outer, and its stored outer the converse of
    the caller outer. -/
theorem R.held2 {N M₁ M₂ N₁ N₂ : Type} {c' : Codec A V N} {c : Codec V A M}
    {oV : Codec V A M₁} {oA : Codec V A M₂} {oV' : Codec A V N₁} {oA' : Codec A V N₂}
    (h : R c' c) (hV : R oV' oA) (hA : R oA' oV) (fV gV : V → V) (hA' kA : A → A) :
    R (held2 c' oV' oA' hA' kA fV gV) (held2 c oV oA fV gV hA' kA) := by
  obtain ⟨_, _, e₁, p₁⟩ := oV'
  obtain ⟨_, _, e₂, p₂⟩ := oA'
  obtain ⟨h1, -⟩ := hV
  obtain ⟨-, h2⟩ := hA
  subst h1 h2
  exact R.refine2 (R.adapt2 h fV gV hA' kA) _ _

/-- **The host `refine` is the one-sided restriction**: the stored predicate admits every
    attribute. -/
theorem refine2_host (c : Codec V A M) (q : V → Bool) :
    refine2 c q (fun _ => true) = c.restrict q := by
  obtain ⟨T, μ, e, p⟩ := c
  simp only [refine2, Codec.restrict, Codec.mk.injEq, true_and]
  refine ⟨funext fun v => ?_, funext fun a => ?_⟩
  · cases e v <;> rfl
  · rfl

/-- **The host adapter is `through`**: the stored pair is the identity. -/
theorem adapt2_host (c : Codec V A M) (f g : V → V) : adapt2 c f g id id = c.through f g := by
  obtain ⟨T, μ, e, p⟩ := c
  simp only [adapt2, Codec.through, Codec.mk.injEq, true_and]
  refine ⟨funext fun v => ?_, rfl⟩
  cases e (f v) <;> rfl

/-- **The host `held` is the one-sided `held`** when the stored outer reads every attribute and
    the stored pair is the identity. -/
theorem held2_host {M₁ M₂ : Type} (c : Codec V A M) (o : Codec V A M₁) (oA : Codec V A M₂)
    (htop : ∀ a, (oA.p a).isSome = true) (f g : V → V) :
    held2 c o oA f g id id = (c.through f g).restrict fun v => (o.e v).isSome := by
  have : (fun a => (oA.p a).isSome) = fun _ => true := funext htop
  rw [held2, this, adapt2_host, refine2_host]

/-- The write of the two-sided restriction. -/
theorem refine2_e {c : Codec V A M} {qV : V → Bool} {qA : A → Bool} {v : V} {a : A} :
    (refine2 c qV qA).e v = some a ↔ qV v = true ∧ c.e v = some a ∧ qA a = true := by
  simp only [refine2]
  cases hq : qV v
  · simp
  · cases c.e v with
    | none => simp
    | some a' => cases hqa : qA a' <;> simp [hqa] <;> intro hh <;> subst hh <;> assumption

/-- The read of the two-sided restriction. -/
theorem refine2_p {c : Codec V A M} {qV : V → Bool} {qA : A → Bool} {v : V} {a : A} :
    (refine2 c qV qA).p a = some v ↔ qA a = true ∧ c.p a = some v ∧ qV v = true := by
  simp only [refine2]
  cases hq : qA a
  · simp
  · cases c.p a with
    | none => simp
    | some v' => cases hqv : qV v' <;> simp [hqv] <;> intro hh <;> subst hh <;> assumption

/-- The two-sided restriction keeps the laws, and owes nothing. -/
theorem Lawful.refine2 {member : A → M} {c : Codec V A M} (hc : Lawful member c)
    (qV : V → Bool) (qA : A → Bool) : Lawful member (refine2 c qV qA) where
  retract he :=
    let ⟨hq, he', hqa⟩ := refine2_e.mp he
    refine2_p.mpr ⟨hqa, hc.retract he', hq⟩
  canon hp :=
    let ⟨hqa, hp', hq⟩ := refine2_p.mp hp
    refine2_e.mpr ⟨hq, hc.canon hp', hqa⟩
  writes hμ _ _ he := hc.writes hμ (refine2_e.mp he).2.1

/-- **A two-sided restriction is below the codec that it restricts.** -/
theorem sub_refine2_self (c : Codec V A M) (qV : V → Bool) (qA : A → Bool) :
    Sub (refine2 c qV qA) c :=
  ⟨fun _ _ h => (refine2_e.mp h).2.1, fun _ _ h => (refine2_p.mp h).2.1⟩

/-- **The stored-side gate**: the codec writes, and the predicate admits the write. The gate of
    the converse reads, and the predicate admits the read. -/
def gate {X Y N : Type} (c : Codec X Y N) (q : Y → Bool) (x : X) : Bool :=
  match c.e x with
  | some y => q y
  | none => false

/-- The gate of the truth predicate is the write domain. -/
theorem gate_true {X Y N : Type} (c : Codec X Y N) (x : X) :
    gate c (fun _ => true) x = (c.e x).isSome := by
  unfold gate
  cases c.e x <;> rfl

/-- A gate whose predicate admits the write is the write domain. -/
theorem gate_eq_isSome {X Y N : Type} {c : Codec X Y N} {q : Y → Bool} {x : X}
    (h : ∀ y, c.e x = some y → q y = true) : gate c q x = (c.e x).isSome := by
  unfold gate
  cases hx : c.e x with
  | none => rfl
  | some y => exact h y hx

/-- A gate that passes sees a write. -/
theorem gate_isSome {X Y N : Type} {c : Codec X Y N} {q : Y → Bool} {x : X}
    (h : gate c q x = true) : (c.e x).isSome = true := by
  revert h
  unfold gate
  cases c.e x <;> simp

/-- The write domain of the two-sided restriction: the caller predicate, and the gate of the
    stored predicate. -/
theorem refine2_e_isSome (c : Codec V A M) (qV : V → Bool) (qA : A → Bool) (v : V) :
    ((refine2 c qV qA).e v).isSome = (qV v && gate c qA v) := by
  simp only [refine2, gate]
  cases qV v
  · rfl
  · cases c.e v with
    | none => rfl
    | some a => cases h : qA a <;> simp [h]

/-- The read domain of the two-sided restriction: the stored predicate, and the gate of the
    caller predicate on the converse. -/
theorem refine2_p_isSome (c : Codec V A M) (qV : V → Bool) (qA : A → Bool) (a : A) :
    ((refine2 c qV qA).p a).isSome = (qA a && gate (conv c) qV a) := by
  simp only [refine2, gate, conv]
  cases qA a
  · rfl
  · cases c.p a with
    | none => rfl
    | some v => cases h : qV v <;> simp [h]

/-- The gate of the two-sided adapter is the gate of its inner codec, through the two entry and
    exit functions. -/
theorem adapt2_gate (c : Codec V A M) (fV gV : V → V) (hA kA : A → A) (q : A → Bool) (v : V) :
    gate (adapt2 c fV gV hA kA) q v = gate c (q ∘ kA) (fV v) := by
  simp only [gate, adapt2]
  cases c.e (fV v) <;> rfl

/-- The gate of the converse of the two-sided adapter, on the read side. -/
theorem adapt2_gateA (c : Codec V A M) (fV gV : V → V) (hA kA : A → A) (q : V → Bool) (a : A) :
    gate (conv (adapt2 c fV gV hA kA)) q a = gate (conv c) (q ∘ gV) (hA a) := by
  simp only [gate, adapt2, conv]
  cases c.p (hA a) <;> rfl

/-- **One two-sided adapter over two agreeing inner codecs agrees.** -/
theorem agreeS_adapt2 {side : Bool} {c c' : Codec V A M} {fV gV : V → V} {hA kA : A → A}
    (h : AgreeS side c c') : AgreeS side (adapt2 c fV gV hA kA) (adapt2 c' fV gV hA kA) := by
  cases side
  · intro a t w ht hw
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp ht
    obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.mp hw
    rw [(h : AgreeP c c') (hA a) u u' hu hu']
  · intro v a b ha hb
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
    rw [(h : AgreeE c c') (fV v) a' b' ha' hb']

/-- **One adapter over two agreeing inner codecs agrees**, whatever the outers of each side. -/
theorem agreeS_held2 {side : Bool} {M₁ M₂ M₁' M₂' : Type} {c c' : Codec V A M}
    {oV : Codec V A M₁} {oA : Codec V A M₂} {oV' : Codec V A M₁'} {oA' : Codec V A M₂'}
    {fV gV : V → V} {hA kA : A → A} (h : AgreeS side c c') :
    AgreeS side (held2 c oV oA fV gV hA kA) (held2 c' oV' oA' fV gV hA kA) :=
  agreeS_sub_left (sub_refine2_self _ _ _)
    (agreeS_sub_right (sub_refine2_self _ _ _) (agreeS_adapt2 h))

/-- A `held` writes only where its caller outer writes. -/
theorem held2_e_dom {M₁ M₂ : Type} {c : Codec V A M} {oV : Codec V A M₁} {oA : Codec V A M₂}
    {fV gV : V → V} {hA kA : A → A} {v : V} {a : A}
    (h : (held2 c oV oA fV gV hA kA).e v = some a) : (oV.e v).isSome = true :=
  (refine2_e.mp h).1

/-- …and reads only where its stored outer reads. -/
theorem held2_p_domA {M₁ M₂ : Type} {c : Codec V A M} {oV : Codec V A M₁} {oA : Codec V A M₂}
    {fV gV : V → V} {hA kA : A → A} {a : A} {t : V}
    (h : (held2 c oV oA fV gV hA kA).p a = some t) : (oA.p a).isSome = true :=
  (refine2_p.mp h).1

/-- …and, with no stored entry function, only where its inner codec reads. -/
theorem held2_p_dom {M₁ M₂ : Type} {c : Codec V A M} {oV : Codec V A M₁} {oA : Codec V A M₂}
    {fV gV : V → V} {kA : A → A} {a : A} {t : V}
    (h : (held2 c oV oA fV gV id kA).p a = some t) : (c.p a).isSome = true := by
  obtain ⟨w, hw, _⟩ := Option.map_eq_some_iff.mp (refine2_p.mp h).2.1
  rw [id] at hw
  rw [hw]; rfl

/-- The stored exit function keeps the member of every written attribute. -/
def KeepsMember (member : A → M) (c : Codec V A M) (k : A → A) : Prop :=
  ∀ v a, c.e v = some a → member (k a) = member a

/-- **The obligation of the two-sided adapter**: one `IsoCancels` per half, and the member fact
    of the stored exit function. -/
def Obl2 (member : A → M) (c : Codec V A M) (fV gV : V → V) (hA kA : A → A) : Prop :=
  IsoCancels c fV gV ∧ IsoCancels (conv c) hA kA ∧ KeepsMember member c kA

/-- **The two-sided adapter keeps the laws**, from the obligation per half. -/
theorem Lawful.adapt2 {member : A → M} {c : Codec V A M} (hc : Lawful member c)
    {fV gV : V → V} {hA kA : A → A} (h : Obl2 member c fV gV hA kA) :
    Lawful member (adapt2 c fV gV hA kA) := by
  obtain ⟨⟨hV1, hV2⟩, ⟨hA1, hA2⟩, hm⟩ := h
  refine ⟨fun {v a'} he => ?_, fun {a' w} hp => ?_, fun {μ} hμ {v a'} he => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp he
    have hr := hc.retract ha
    have hk : hA (kA a) = a := hA2 a (by simp only [Alg.conv, hr, Option.isSome_some])
    simp only [Alg.adapt2, hk, hr, Option.map_some, hV1 v (by rw [ha]; rfl)]
  · obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hp
    have hcu := hc.canon hu
    have hfg : fV (gV u) = u := hV2 u (by rw [hcu]; rfl)
    simp only [Alg.adapt2, hfg, hcu, Option.map_some,
      hA1 a' (by simp only [Alg.conv, hu, Option.isSome_some])]
  · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp he
    rw [hm (fV v) a ha]
    exact hc.writes hμ ha

/-- **The host obligation is the one-sided obligation**: the stored pair is the identity. -/
theorem obl2_host (member : A → M) (c : Codec V A M) (f g : V → V) :
    Obl2 member c f g id id ↔ IsoCancels c f g :=
  ⟨fun h => h.1, fun h => ⟨h, ⟨fun _ _ => rfl, fun _ _ => rfl⟩, fun _ _ _ => rfl⟩⟩

/-- The two-sided restriction is on its carrier when the inner codec is. -/
theorem carrier_refine2 {c : Codec V A M} (h : Carrier c) (qV : V → Bool) (qA : A → Bool) :
    Carrier (refine2 c qV qA) where
  domE he := let ⟨hq, he', _⟩ := refine2_e.mp he; ⟨h.domE he', hq⟩
  ranP hp := let ⟨_, hp', hq⟩ := refine2_p.mp hp; ⟨h.ranP hp', hq⟩

/-- The two-sided adapter is on its carrier when the inner codec is, and the caller pair cancels
    on the written values. -/
theorem carrier_adapt2 {member : A → M} {c : Codec V A M} (hc : Carrier c)
    (hlaw : LawfulCore member c) {fV gV : V → V} (hA kA : A → A)
    (hfg : ∀ v, (c.e v).isSome → fV (gV v) = v) : Carrier (adapt2 c fV gV hA kA) where
  domE he := let ⟨_, ha, _⟩ := Option.map_eq_some_iff.mp he; hc.domE ha
  ranP hp := by
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hp
    have hT : c.T w := hc.ranP hw
    rw [← hfg w (hlaw.canon hw)] at hT
    exact hT

/-- The two-sided restriction keeps agreement below a depth. -/
theorem agreeLe_refine2 {dV : V → Nat} {dA : A → Nat} {d : Nat} {c₁ c₂ : Codec V A M}
    (h : AgreeLe dV dA d c₁ c₂) (qV : V → Bool) (qA : A → Bool) :
    AgreeLe dV dA d (refine2 c₁ qV qA) (refine2 c₂ qV qA) :=
  ⟨fun v hv => by simp only [refine2, h.e v hv], fun a ha => by simp only [refine2, h.p a ha]⟩

/-! ## The constructors that keep the converse

Each lemma says: the constructor over the converses of its parts is the converse of the
constructor over the parts. -/

/-- `select` on the write of the converses is `select` on the read of the originals. -/
theorem select_R_e {N' : Type} : ∀ {os' : List (Codec A V N')} {os : List (Codec V A M)},
    List.Forall₂ R os' os → ∀ a, select os' (·.e) a = select os (·.p) a
  | [], [], .nil, _ => rfl
  | o' :: os', o :: os, .cons h hs, a => by
      unfold select at *
      simp only [List.find?_cons, h.1]
      split
      · exact congrFun h.1 a
      · exact select_R_e hs a

/-- `select` on the read of the converses is `select` on the write of the originals. -/
theorem select_R_p {N' : Type} : ∀ {os' : List (Codec A V N')} {os : List (Codec V A M)},
    List.Forall₂ R os' os → ∀ v, select os' (·.p) v = select os (·.e) v
  | [], [], .nil, _ => rfl
  | o' :: os', o :: os, .cons h hs, v => by
      unfold select at *
      simp only [List.find?_cons, h.2]
      split
      · exact congrFun h.2 v
      · exact select_R_p hs v

/-- **The converse of a union is the union of the converses**, whatever the two members. -/
theorem altCodec_R {N' : Type} {os' : List (Codec A V N')} {os : List (Codec V A M)}
    (μ' : Option N') (μ : Option M) (h : List.Forall₂ R os' os) :
    R (altCodec os' μ') (altCodec os μ) :=
  ⟨funext (select_R_e h), funext (select_R_p h)⟩

/-- The stage of the converse body is the converse of the stage. -/
theorem muStage_R {N' : Type} (B : Codec V A M → Codec V A M) (B' : Codec A V N' → Codec A V N')
    (h : ∀ c' c, R c' c → R (B' c') (B c)) : ∀ n, R (muStage B' n) (muStage B n)
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => h _ _ (muStage_R B B' h n)

/-- **The converse of a fixed point is the fixed point of the converse body**, with the two
    depth functions swapped. -/
theorem muCodec_R {N' : Type} (dV : V → Nat) (dA : A → Nat) (B : Codec V A M → Codec V A M)
    (B' : Codec A V N' → Codec A V N') (h : ∀ c' c, R c' c → R (B' c') (B c)) :
    R (muCodec dA dV B') (muCodec dV dA B) :=
  ⟨funext fun a => by
      simp only [muCodec]
      rw [(muStage_R B B' h _).1],
   funext fun v => by
      simp only [muCodec]
      rw [(muStage_R B B' h _).2]⟩

/-- Two fields of one shape whose codecs have the converse graphs. -/
def FieldR {N' : Type} : FieldSem A V N' → FieldSem V A M → Prop
  | .req c', .req c => R c' c
  | .opt c', .opt c => R c' c
  | _, _ => False

/-- Two rest policies of one shape whose codecs have the converse graphs. -/
def RestR {N' : Type} : RestSem A V N' → RestSem V A M → Prop
  | .drop, .drop | .refuse, .refuse => True
  | .codec c', .codec c => R c' c
  | _, _ => False

/-- Two fields of one shape have one presence. -/
theorem FieldR.valPresentAt {N' : Type} {f' : FieldSem A V N'} {f : FieldSem V A M}
    (h : FieldR f' f) (names : Finset String) (k : String) :
    valPresentAt names k f' = valPresentAt names k f := by
  cases f' <;> cases f <;> first | rfl | exact h.elim

/-- The entry codec of a table of converse fields is the converse of the entry codec. -/
theorem entry_R {N' : Type} {keys : Finset String} {s' : {k // k ∈ keys} → FieldSem A V N'}
    {s : {k // k ∈ keys} → FieldSem V A M} (hF : ∀ k, FieldR (s' k) (s k))
    {rest' : RestSem A V N'} {rest : RestSem V A M} (hr : RestR rest' rest) (k : String) :
    Option.Rel R (entryCodec ⟨keys, s'⟩ (rcOf rest') k) (entryCodec ⟨keys, s⟩ (rcOf rest) k) := by
  have hat : Option.Rel FieldR ((⟨keys, s'⟩ : MapOf (FieldSem A V N')).at k)
      ((⟨keys, s⟩ : MapOf (FieldSem V A M)).at k) := by
    unfold MapOf.at
    split
    · exact .some (hF _)
    · exact .none
  unfold entryCodec
  revert hat
  generalize (⟨keys, s'⟩ : MapOf (FieldSem A V N')).at k = x'
  generalize (⟨keys, s⟩ : MapOf (FieldSem V A M)).at k = x
  intro hat
  cases hat with
  | some h =>
    rename_i f' f
    cases f' <;> cases f <;> first | exact h.elim | exact .some h
  | none =>
    revert hr
    cases rest' <;> cases rest <;> intro hr <;> first | exact hr.elim | exact .none | exact .some hr

/-- A map payload over a key set equal to another is the payload over that set. -/
theorem funImage_map_mk {β : Type} {s' s : Finset String} (h : s' = s)
    (G' : {k // k ∈ s'} → Option β) (G : {k // k ∈ s} → Option β)
    (hG : ∀ k (h₁ : k ∈ s') (h₂ : k ∈ s), G' ⟨k, h₁⟩ = G ⟨k, h₂⟩) :
    (funImage G').map (fun d => (⟨s', d⟩ : MapOf β)) = (funImage G).map (fun g => ⟨s, g⟩) := by
  subst h
  have : G' = G := funext fun k => hG k.1 k.2 k.2
  rw [this]

/-- The read of an object with no name filter is the write of the converse object. -/
theorem objRead_true {N' : Type} (s₁ : MapOf (FieldSem V A M)) (rc₁ : Option (Codec V A M))
    (s₂ : MapOf (FieldSem A V N')) (rc₂ : Option (Codec A V N'))
    (hg : ∀ names, reqPresentB s₁ names = valPresentB s₂ names)
    (he : ∀ k, Option.Rel R (entryCodec s₂ rc₂ k) (entryCodec s₁ rc₁ k)) (q : MapOf A) :
    objRead s₁ rc₁ (fun _ => true) q = objWrite s₂ rc₂ q := by
  unfold objRead objWrite
  rw [hg]
  split
  · -- the multiset form: `Finset.filter_true_of_mem` reaches `Classical.choice`
    refine funImage_map_mk (Finset.eq_of_veq (Multiset.filter_eq_self.mpr fun _ _ => rfl)) _ _
      fun k h₁ h₂ => ?_
    have hk := he k
    revert hk
    generalize entryCodec s₂ rc₂ k = x₂
    generalize entryCodec s₁ rc₁ k = x₁
    intro hk
    cases hk with
    | none => rfl
    | some hR => exact (congrFun hR.1 _).symm
  · rfl

/-- **The converse of an object is the object of the converse fields**, when the rest policy is
    not `drop`. The term language builds `refuse` or `codec`, never `drop`. -/
theorem objectCodec_R {N' : Type} (mV : Ctor (MapOf V) V) (mA : Ctor (MapOf A) A) (μ' : N')
    (μM : M) {keys : Finset String} {s' : {k // k ∈ keys} → FieldSem A V N'}
    {s : {k // k ∈ keys} → FieldSem V A M} (hF : ∀ k, FieldR (s' k) (s k))
    {rest' : RestSem A V N'} {rest : RestSem V A M} (hr : RestR rest' rest) (hd : rest ≠ .drop) :
    R (objectCodec mA mV μ' ⟨keys, s'⟩ rest') (objectCodec mV mA μM ⟨keys, s⟩ rest) := by
  have hd' : rest' ≠ .drop := by
    revert hr hd; cases rest' <;> cases rest <;> simp [RestR]
  simp only [objectCodec, objectCodecCore, keepB_of_ne_drop hd, keepB_of_ne_drop hd']
  have hpres : ∀ n, valPresentB ⟨keys, s'⟩ n = reqPresentB ⟨keys, s⟩ n := fun n =>
    decide_eq_decide.mpr (forall_congr' fun k => by rw [(hF k).valPresentAt n k.1])
  have hpres' : ∀ n, reqPresentB ⟨keys, s'⟩ n = valPresentB ⟨keys, s⟩ n := fun n =>
    decide_eq_decide.mpr (forall_congr' fun k => by rw [(hF k).valPresentAt n k.1])
  refine ⟨funext fun a => ?_, funext fun v => ?_⟩
  · simp only [carriedCodec]
    congr 2; funext q
    exact (objRead_true _ _ _ _ (fun n => (hpres n).symm) (entry_R hF hr) q).symm
  · simp only [carriedCodec]
    congr 2; funext q
    refine objRead_true _ _ _ _ hpres' (fun k => ?_) q
    have hk := entry_R hF hr k
    revert hk
    generalize entryCodec ⟨keys, s'⟩ (rcOf rest') k = x₂
    generalize entryCodec ⟨keys, s⟩ (rcOf rest) k = x₁
    intro hk
    cases hk with
    | none => exact .none
    | some hR => exact .some hR.symm

/-- `Option.map` keeps a relation that the two functions carry. -/
theorem rel_map {α β α' β' : Type} {r : α → β → Prop} {r' : α' → β' → Prop} {f : α → α'}
    {g : β → β'} (hfg : ∀ a b, r a b → r' (f a) (g b)) :
    ∀ {x : Option α} {y : Option β}, Option.Rel r x y → Option.Rel r' (x.map f) (y.map g)
  | _, _, .none => .none
  | _, _, .some h => .some (hfg _ _ h)

/-- The slots of the converse positions are the converses of the slots. -/
theorem slots_R {N' : Type} : ∀ {cs' : List (Codec A V N')} {cs : List (Codec V A M)}
    {t' : Option (Codec A V N')} {t : Option (Codec V A M)},
    List.Forall₂ R cs' cs → Option.Rel R t' t → ∀ n,
      Option.Rel (List.Forall₂ R) (slots cs' t' n) (slots cs t n)
  | [], [], none, none, .nil, .none, 0 => .some .nil
  | [], [], some _, some _, .nil, .some _, 0 => .some .nil
  | [], [], none, none, .nil, .none, _ + 1 => .none
  | [], [], some c', some c, .nil, .some h, n + 1 => by
      have ih := slots_R (.nil) (.some h) n
      simp only [slots]
      exact rel_map (fun _ _ hr => .cons h hr) ih
  | _ :: _, _ :: _, _, _, .cons _ _, _, 0 => .none
  | c' :: cs', c :: cs, _, _, .cons h hs, ht, n + 1 => by
      have ih := slots_R hs ht n
      simp only [slots]
      exact rel_map (fun _ _ hr => .cons h hr) ih

/-- The traversal of the converse positions by the write is the traversal by the read. -/
theorem trav_R_e {N' : Type} : ∀ {ds' : List (Codec A V N')} {ds : List (Codec V A M)},
    List.Forall₂ R ds' ds → ∀ xs : List A,
      traverse (fun ca : Codec A V N' × A => ca.1.e ca.2) (ds'.zip xs) =
        traverse (fun ca : Codec V A M × A => ca.1.p ca.2) (ds.zip xs)
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons _ _, [] => rfl
  | _ :: _, _ :: _, .cons h hs, x :: xs => by
      simp only [List.zip_cons_cons, traverse, h.1, trav_R_e hs xs]

/-- The traversal of the converse positions by the read is the traversal by the write. -/
theorem trav_R_p {N' : Type} : ∀ {ds' : List (Codec A V N')} {ds : List (Codec V A M)},
    List.Forall₂ R ds' ds → ∀ xs : List V,
      traverse (fun ca : Codec A V N' × V => ca.1.p ca.2) (ds'.zip xs) =
        traverse (fun ca : Codec V A M × V => ca.1.e ca.2) (ds.zip xs)
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons _ _, [] => rfl
  | _ :: _, _ :: _, .cons h hs, x :: xs => by
      simp only [List.zip_cons_cons, traverse, h.2, trav_R_p hs xs]

/-- A row of converse positions traverses by the write as the row traverses by the read. -/
theorem rowtrav_e {N' : Type} :
    ∀ {x : Option (List (Codec A V N'))} {y : Option (List (Codec V A M))},
    Option.Rel (List.Forall₂ R) x y → ∀ as : List A,
      (x.map (·.zip as)).bind (traverse fun ca : Codec A V N' × A => ca.1.e ca.2) =
        (y.map (·.zip as)).bind (traverse fun ca : Codec V A M × A => ca.1.p ca.2)
  | _, _, .none, _ => rfl
  | _, _, .some h, as => trav_R_e h as

/-- A row of converse positions traverses by the read as the row traverses by the write. -/
theorem rowtrav_p {N' : Type} :
    ∀ {x : Option (List (Codec A V N'))} {y : Option (List (Codec V A M))},
    Option.Rel (List.Forall₂ R) x y → ∀ vs : List V,
      (x.map (·.zip vs)).bind (traverse fun ca : Codec A V N' × V => ca.1.p ca.2) =
        (y.map (·.zip vs)).bind (traverse fun ca : Codec V A M × V => ca.1.e ca.2)
  | _, _, .none, _ => rfl
  | _, _, .some h, vs => trav_R_p h vs

/-- **The converse of a list is the list of the converse positions**, with the two prisms
    swapped. -/
theorem listCodec_R {N' : Type} (pV : Ctor (List V) V) (pA : Ctor (List A) A) (μL : M) (μ' : N')
    {pre' suf' : List (Codec A V N')} {sp' : Option (Codec A V N')}
    {pre suf : List (Codec V A M)} {sp : Option (Codec V A M)}
    (hpre : List.Forall₂ R pre' pre) (hsp : Option.Rel R sp' sp) (hsuf : List.Forall₂ R suf' suf) :
    R (listCodec pA pV μ' pre' sp' suf') (listCodec pV pA μL pre sp suf) := by
  have hrow : ∀ n, Option.Rel (List.Forall₂ R) (slotsL pre' sp' suf' n) (slotsL pre sp suf n) := by
    intro n
    unfold slotsL
    rw [hsuf.length_eq]
    split
    · exact .none
    · exact rel_map (fun _ _ hr => List.rel_append hr hsuf) (slots_R hpre hsp (n - suf.length))
  refine ⟨funext fun a => ?_, funext fun v => ?_⟩
  · simp only [listCodec, carriedCodec]
    congr 2; funext as
    unfold alignL
    exact rowtrav_e (hrow as.length) as
  · simp only [listCodec, carriedCodec]
    congr 2; funext vs
    unfold alignL
    exact rowtrav_p (hrow vs.length) vs

end Calculus.Alg
