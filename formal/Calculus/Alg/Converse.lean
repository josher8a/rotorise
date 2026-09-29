import Calculus.Alg.Agree

/-!
# The two-sided wrappers

`adapt2` is the two-sided form of `through`, and `held2` restricts `adapt2` on each side by an
outer codec. Each side of a codec holds one pair, and each pair reads from its own side: the
first function acts on the value that enters from the side, and the second on the value that
exits to the side. `Obl2` is the obligation of the two-sided adapter: one `IsoCancels` per half,
and the member fact of the stored exit function. Where the stored pair is the identity, the
two-sided form is the host form (`adapt2_host`, `held2_host`, `obl2_host`).

The object codec reads the map payload at each orientation (`objectCodec_f`).
-/

namespace Calculus.Alg

variable {V A M : Type}

/-! ## The two-sided wrappers -/

/-- **The two-sided adapter.** The caller pair is `(fV, gV)`: `fV` on entry from `V`, `gV` on exit
    to `V`. The stored pair is `(hA, kA)`: `hA` on entry from `A`, `kA` on exit to `A`. -/
def adapt2 (c : Codec V A M) (fV gV : V → V) (hA kA : A → A) : Codec V A M :=
  Codec.ofEP (T := fun v => c.T (fV v))
    (μ := c.μ)
    (e := fun v => (c.e (fV v)).map kA)
    (p := fun a => (c.p (hA a)).map gV)

/-- **The two-sided `held`**: the adapter, restricted on each side by an outer codec. The caller
    outer restricts by its write domain, and the stored outer by its read domain. -/
def held2 {M₁ M₂ : Type} (c : Codec V A M) (oV : Codec V A M₁) (oA : Codec V A M₂)
    (fV gV : V → V) (hA kA : A → A) : Codec V A M :=
  refine2 (adapt2 c fV gV hA kA) (fun v => (oV.e v).isSome) (fun a => (oA.p a).isSome)

/-- **The host adapter is `through`**: the stored pair is the identity. -/
theorem adapt2_host (c : Codec V A M) (f g : V → V) : adapt2 c f g id id = c.through f g := by
  refine Codec.ext rfl rfl (funext fun v => ?_) rfl
  simp only [adapt2, Codec.through, Codec.ofEP_e]
  cases c.e (f v) <;> rfl

/-- **The host `held` is the one-sided `held`** when the stored outer reads every attribute and
    the stored pair is the identity. -/
theorem held2_host {M₁ M₂ : Type} (c : Codec V A M) (o : Codec V A M₁) (oA : Codec V A M₂)
    (htop : ∀ a, (oA.p a).isSome = true) (f g : V → V) :
    held2 c o oA f g id id = (c.through f g).restrict fun v => (o.e v).isSome := by
  have : (fun a => (oA.p a).isSome) = fun _ => true := funext htop
  rw [held2, this, adapt2_host]; rfl

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

/-- The gate of the write of the two-sided adapter is the gate of the write of its inner codec,
    through the two entry and exit functions. -/
theorem adapt2_gate (c : Codec V A M) (fV gV : V → V) (hA kA : A → A) (q : A → Bool) (v : V) :
    gate (adapt2 c fV gV hA kA).e q v = gate c.e (q ∘ kA) (fV v) := by
  simp only [gate, adapt2, Codec.ofEP_e]
  cases c.e (fV v) <;> rfl

/-- …and the gate of its read, on the read side. -/
theorem adapt2_gateA (c : Codec V A M) (fV gV : V → V) (hA kA : A → A) (q : V → Bool) (a : A) :
    gate (adapt2 c fV gV hA kA).p q a = gate c.p (q ∘ gV) (hA a) := by
  simp only [gate, adapt2, Codec.ofEP_p]
  cases c.p (hA a) <;> rfl

/-- **One two-sided adapter over two agreeing inner codecs agrees.** -/
theorem agreeS_adapt2 {side : Bool} {c c' : Codec V A M} {fV gV : V → V} {hA kA : A → A}
    (h : AgreeS side c c') : AgreeS side (adapt2 c fV gV hA kA) (adapt2 c' fV gV hA kA) := by
  cases side
  · intro a t w ht hw
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp ht
    obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.mp hw
    rw [(h : Agree .dual c c') (hA a) u u' hu hu']
  · intro v a b ha hb
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
    rw [(h : Agree .host c c') (fV v) a' b' ha' hb']

/-- **One adapter over two agreeing inner codecs agrees**, whatever the outers of each side. -/
theorem agreeS_held2 {side : Bool} {M₁ M₂ M₁' M₂' : Type} {c c' : Codec V A M}
    {oV : Codec V A M₁} {oA : Codec V A M₂} {oV' : Codec V A M₁'} {oA' : Codec V A M₂'}
    {fV gV : V → V} {hA kA : A → A} (h : AgreeS side c c') :
    AgreeS side (held2 c oV oA fV gV hA kA) (held2 c' oV' oA' fV gV hA kA) :=
  agree_sub_left (sub_refine2_self _ _ _)
    (agree_sub_right (sub_refine2_self _ _ _) (agreeS_adapt2 h))

/-- The stored exit function keeps the member of every written attribute. -/
def KeepsMember (member : A → M) (c : Codec V A M) (k : A → A) : Prop :=
  ∀ v a, c.e v = some a → member (k a) = member a

/-- **The obligation of the two-sided adapter**: one `IsoCancels` per half, and the member fact
    of the stored exit function. -/
def Obl2 (member : A → M) (c : Codec V A M) (fV gV : V → V) (hA kA : A → A) : Prop :=
  IsoCancels c fV gV ∧ IsoCancelsAt Orient.dual c hA kA ∧ KeepsMember member c kA

/-- **The two-sided adapter keeps the laws**, from the obligation per half. -/
theorem Lawful.adapt2 {member : A → M} {c : Codec V A M} (hc : Lawful member c)
    {fV gV : V → V} {hA kA : A → A} (h : Obl2 member c fV gV hA kA) :
    Lawful member (adapt2 c fV gV hA kA) := by
  obtain ⟨⟨hV1, hV2⟩, ⟨hA1, hA2⟩, hm⟩ := h
  refine .ofRC (fun {v a'} he => ?_) (fun {a' w} hp => ?_) (fun {μ} hμ {v a'} he => ?_)
  · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp he
    have hr := hc.retract ha
    have hk : hA (kA a) = a := hA2 a (Option.isSome_iff_exists.mpr ⟨_, hr⟩)
    simp only [Alg.adapt2, Codec.ofEP_p, hk, hr, Option.map_some, hV1 v (Option.isSome_iff_exists.mpr ⟨_, ha⟩)]
  · obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hp
    have hcu := hc.canon hu
    have hfg : fV (gV u) = u := hV2 u (Option.isSome_iff_exists.mpr ⟨_, hcu⟩)
    simp only [Alg.adapt2, Codec.ofEP_e, hfg, hcu, Option.map_some,
      hA1 a' (Option.isSome_iff_exists.mpr ⟨_, hu⟩)]
  · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp he
    rw [hm (fV v) a ha]
    exact hc.writes hμ ha

/-- **The host obligation is the one-sided obligation**: the stored pair is the identity. -/
theorem obl2_host (member : A → M) (c : Codec V A M) (f g : V → V) :
    Obl2 member c f g id id ↔ IsoCancels c f g :=
  ⟨fun h => h.1, fun h => ⟨h, ⟨fun _ _ => rfl, fun _ _ => rfl⟩, fun _ _ _ => rfl⟩⟩

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

/-! ## The object codec at an orientation -/

/-- A map payload over a key set equal to another is the payload over that set. -/
theorem funImage_map_mk {β : Type} {s' s : Finset String} (h : s' = s)
    (G' : {k // k ∈ s'} → Option β) (G : {k // k ∈ s} → Option β)
    (hG : ∀ k (h₁ : k ∈ s') (h₂ : k ∈ s), G' ⟨k, h₁⟩ = G ⟨k, h₂⟩) :
    (funImage G').map (fun d => (⟨s', d⟩ : MapOf β)) = (funImage G).map (fun g => ⟨s, g⟩) := by
  subst h
  have : G' = G := funext fun k => hG k.1 k.2 k.2
  rw [this]

/-- **The object codec at an orientation**: read the caller prism, pass the presence guard, run
    each entry at the orientation, and build with the stored prism. The rest policy is not
    `drop`, so the read keeps every name. -/
theorem objectCodec_f (m : (s : Bool) → Ctor (MapOf (Side V A s)) (Side V A s)) (μM : M)
    (sems : MapOf (FieldSem V A M)) {rest : RestSem V A M} (hd : rest ≠ .drop) :
    ∀ (o : Orient) (x : Side V A o.c), (objectCodec (m false) (m true) μM sems rest).f o x =
      (((m o.c).out x).bind fun q => if valPresentB sems q.1 = true then
        (funImage fun k => (entryCodec sems (rcOf rest) k.1).bind fun c => c.f o (q.2 k)).map
          (fun g => (⟨q.1, g⟩ : MapOf (Side V A o.s))) else none).map (m o.s).into :=
  Orient.both (P := fun o => ∀ x, (objectCodec (m false) (m true) μM sems rest).f o x =
      (((m o.c).out x).bind fun q => if valPresentB sems q.1 = true then
        (funImage fun k => (entryCodec sems (rcOf rest) k.1).bind fun c => c.f o (q.2 k)).map
          (fun g => (⟨q.1, g⟩ : MapOf (Side V A o.s))) else none).map (m o.s).into)
    (fun _ => rfl)
    (fun a => by
      simp only [objectCodec, objectCodecCore, keepB_of_ne_drop hd, carriedCodec, Codec.ofEP_p]
      congr 2; funext q
      unfold objRead
      rw [show reqPresentB sems q.1 = valPresentB sems q.1 from rfl]
      cases valPresentB sems q.1
      · rfl
      · -- the multiset form: `Finset.filter_true_of_mem` reaches `Classical.choice`
        refine funImage_map_mk (Finset.eq_of_veq (Multiset.filter_eq_self.mpr fun _ _ => rfl)) _ _
          fun _ _ _ => rfl)

end Calculus.Alg
