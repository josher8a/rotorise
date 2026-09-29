import Calculus.Alg.Containers
import Calculus.Alg.Recursion

/-!
# Agreement of two codecs, one half at a time

Two partial bijections `s` and `t` are compatible when `s⁻¹t` and `st⁻¹` are idempotents
(Lawson). On codecs the two conditions are two halves of agreement. **Write agreement** says
that two writers of one value write one attribute. **Read agreement** says that two readers of
one attribute read one value. Over two lawful codecs, `Compat` is exactly the two halves
(`compat_iff_agree`), so `Compat` is symmetric there.

Each combinator keeps each half: a restriction on either side, a union option by option, a
recursive codec stage by stage, one adapter over two agreeing stored sides, and a list or an
object position by position. The decision `Term.compat` reads these lemmas, one per row.
-/

namespace Calculus.Alg

section Agree
variable {V A M : Type}

/-- **Write agreement**: two writers of one value write one attribute. -/
def AgreeE (c d : Codec V A M) : Prop := ∀ v a b, c.e v = some a → d.e v = some b → a = b

/-- **Read agreement**: two readers of one attribute read one value. -/
def AgreeP (c d : Codec V A M) : Prop := ∀ a t w, c.p a = some t → d.p a = some w → t = w

/-- One half, by the side flag: `true` is the write half. -/
def AgreeS : Bool → Codec V A M → Codec V A M → Prop
  | true, c, d => AgreeE c d
  | false, c, d => AgreeP c d

/-- The empty codec agrees with every codec on each half. -/
theorem agreeS_empty_left (side : Bool) (d : Codec V A M) : AgreeS side .empty d := by
  cases side
  · intro _ _ _ h; exact nomatch h
  · intro _ _ _ h; exact nomatch h

/-- …on the right as well. -/
theorem agreeS_empty_right (side : Bool) (c : Codec V A M) : AgreeS side c .empty := by
  cases side
  · intro _ _ _ _ h; exact nomatch h
  · intro _ _ _ _ h; exact nomatch h

/-- Agreement is antitone on the left. -/
theorem agreeS_sub_left {side : Bool} {c c' d : Codec V A M} (hs : Sub c c')
    (h : AgreeS side c' d) : AgreeS side c d := by
  cases side
  · intro a t w ht hw; exact (h : AgreeP c' d) a t w (hs.2 _ _ ht) hw
  · intro v a b ha hb; exact (h : AgreeE c' d) v a b (hs.1 _ _ ha) hb

/-- …and on the right. -/
theorem agreeS_sub_right {side : Bool} {c d d' : Codec V A M} (hs : Sub d d')
    (h : AgreeS side c d') : AgreeS side c d := by
  cases side
  · intro a t w ht hw; exact (h : AgreeP c d') a t w ht (hs.2 _ _ hw)
  · intro v a b ha hb; exact (h : AgreeE c d') v a b ha (hs.1 _ _ hb)

/-- Two codecs below one function agree. -/
theorem agreeS_bound {side : Bool} {c d u : Codec V A M} (hc : Sub c u) (hd : Sub d u) :
    AgreeS side c d := by
  cases side
  · intro a t w ht hw
    have h2 := hd.2 _ _ hw; rw [hc.2 _ _ ht] at h2; exact Option.some.inj h2
  · intro v a b ha hb
    have h2 := hd.1 _ _ hb; rw [hc.1 _ _ ha] at h2; exact Option.some.inj h2

/-- Two codecs with apart write domains agree on the write half. -/
theorem agreeE_apart {c d : Codec V A M} (h : ∀ v, ((c.e v).isSome && (d.e v).isSome) = false) :
    AgreeE c d := by
  intro v a b ha hb; have := h v; rw [ha, hb] at this; exact nomatch this

/-- …and with apart read domains, on the read half. -/
theorem agreeP_apart {c d : Codec V A M} (h : ∀ a, ((c.p a).isSome && (d.p a).isSome) = false) :
    AgreeP c d := by
  intro a t w ht hw; have := h a; rw [ht, hw] at this; exact nomatch this

/-- A union agrees with a partner where each option does. -/
theorem agreeS_alt_left {side : Bool} {os : List (Codec V A M)} {μ : Option M} {d : Codec V A M}
    (h : ∀ o ∈ os, AgreeS side o d) : AgreeS side (altCodec os μ) d := by
  cases side
  · intro a t w ht hw
    have ht' : select os (fun c => c.p) a = some t := ht
    obtain ⟨o, ho, -, hot⟩ := select_admits ht'
    exact (h o ho : AgreeP o d) a t w hot hw
  · intro v a b ha hb
    have ha' : select os (fun c => c.e) v = some a := ha
    obtain ⟨o, ho, -, hoa⟩ := select_admits ha'
    exact (h o ho : AgreeE o d) v a b hoa hb

/-- …and on the right. -/
theorem agreeS_alt_right {side : Bool} {os : List (Codec V A M)} {μ : Option M} {c : Codec V A M}
    (h : ∀ o ∈ os, AgreeS side c o) : AgreeS side c (altCodec os μ) := by
  cases side
  · intro a t w ht hw
    have hw' : select os (fun c => c.p) a = some w := hw
    obtain ⟨o, ho, -, how⟩ := select_admits hw'
    exact (h o ho : AgreeP c o) a t w ht how
  · intro v a b ha hb
    have hb' : select os (fun c => c.e) v = some b := hb
    obtain ⟨o, ho, -, hob⟩ := select_admits hb'
    exact (h o ho : AgreeE c o) v a b ha hob

/-- **Two recursive codecs agree where their stages agree**: each input reads the stage of its
    own depth on both sides. -/
theorem agreeS_mu {side : Bool} {dV : V → Nat} {dA : A → Nat} {B B' : Codec V A M → Codec V A M}
    (h : ∀ n, AgreeS side (muStage B n) (muStage B' n)) :
    AgreeS side (muCodec dV dA B) (muCodec dV dA B') := by
  cases side
  · intro a t w ht hw; exact (h (dA a) : AgreeP _ _) a t w ht hw
  · intro v a b ha hb; exact (h (dV v) : AgreeE _ _) v a b ha hb

/-- …and a recursive codec agrees with a partner that every stage agrees with. -/
theorem agreeS_mu_left {side : Bool} {dV : V → Nat} {dA : A → Nat} {B : Codec V A M → Codec V A M}
    {d : Codec V A M} (h : ∀ n, AgreeS side (muStage B n) d) : AgreeS side (muCodec dV dA B) d := by
  cases side
  · intro a t w ht hw; exact (h (dA a) : AgreeP _ _) a t w ht hw
  · intro v a b ha hb; exact (h (dV v) : AgreeE _ _) v a b ha hb

/-- …on the right. -/
theorem agreeS_mu_right {side : Bool} {dV : V → Nat} {dA : A → Nat} {B : Codec V A M → Codec V A M}
    {c : Codec V A M} (h : ∀ n, AgreeS side c (muStage B n)) : AgreeS side c (muCodec dV dA B) := by
  cases side
  · intro a t w ht hw; exact (h (dA a) : AgreeP _ _) a t w ht hw
  · intro v a b ha hb; exact (h (dV v) : AgreeE _ _) v a b ha hb

/-- Two carried codecs over one prism pair agree where their payload pairs agree. -/
theorem agreeE_carried {γ δ : Type} {pV : Ctor γ V} {pA : Ctor δ A} {μ₀ : M}
    {P₁ P₂ : γ → Prop} {E₁ E₂ : γ → Option δ} {D₁ D₂ : δ → Option γ}
    (h : ∀ x d₁ d₂, E₁ x = some d₁ → E₂ x = some d₂ → d₁ = d₂) :
    AgreeE (carriedCodec pV pA μ₀ P₁ E₁ D₁) (carriedCodec pV pA μ₀ P₂ E₂ D₂) := by
  intro v a b ha hb
  simp only [carriedCodec, Option.map_eq_some_iff, Option.bind_eq_some_iff, Codec.ofEP_e] at ha hb
  obtain ⟨d₁, ⟨x, hx, h1⟩, rfl⟩ := ha
  obtain ⟨d₂, ⟨x', hx', h2⟩, rfl⟩ := hb
  rw [hx] at hx'; cases hx'
  rw [h x d₁ d₂ h1 h2]

/-- …and on the read half where their payload readers agree. -/
theorem agreeP_carried {γ δ : Type} {pV : Ctor γ V} {pA : Ctor δ A} {μ₀ : M}
    {P₁ P₂ : γ → Prop} {E₁ E₂ : γ → Option δ} {D₁ D₂ : δ → Option γ}
    (h : ∀ x d₁ d₂, D₁ x = some d₁ → D₂ x = some d₂ → d₁ = d₂) :
    AgreeP (carriedCodec pV pA μ₀ P₁ E₁ D₁) (carriedCodec pV pA μ₀ P₂ E₂ D₂) := by
  intro a t w ht hw
  simp only [carriedCodec, Option.map_eq_some_iff, Option.bind_eq_some_iff, Codec.ofEP_p] at ht hw
  obtain ⟨d₁, ⟨x, hx, h1⟩, rfl⟩ := ht
  obtain ⟨d₂, ⟨x', hx', h2⟩, rfl⟩ := hw
  rw [hx] at hx'; cases hx'
  rw [h x d₁ d₂ h1 h2]

/-- Two rows over one list, every codec of one agreeing with every codec of the other, traverse
    to one list. -/
theorem zip_agree {X Y : Type} (run : Codec V A M → X → Option Y) (R : Codec V A M → Codec V A M → Prop)
    (hR : ∀ c d, R c d → ∀ x y y', run c x = some y → run d x = some y' → y = y') :
    ∀ (xs : List X) (ds₁ ds₂ : List (Codec V A M)) (ys₁ ys₂ : List Y),
      ds₁.length = xs.length → ds₂.length = xs.length → (∀ c ∈ ds₁, ∀ d ∈ ds₂, R c d) →
      traverse (fun cx : Codec V A M × X => run cx.1 cx.2) (ds₁.zip xs) = some ys₁ →
      traverse (fun cx : Codec V A M × X => run cx.1 cx.2) (ds₂.zip xs) = some ys₂ → ys₁ = ys₂
  | [], [], [], ys₁, ys₂, _, _, _, h1, h2 => by
      simp only [List.zip_nil_right, traverse_nil, Option.some.injEq] at h1 h2; rw [← h1, ← h2]
  | x :: xs, c :: cs, d :: ds, ys₁, ys₂, hl1, hl2, hall, h1, h2 => by
      simp only [List.zip_cons_cons, traverse_cons, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at h1 h2
      obtain ⟨y1, hy1, t1, ht1, rfl⟩ := h1
      obtain ⟨y2, hy2, t2, ht2, rfl⟩ := h2
      rw [hR c d (hall c (by simp) d (by simp)) x y1 y2 hy1 hy2,
        zip_agree run R hR xs cs ds t1 t2 (Nat.succ.inj hl1) (Nat.succ.inj hl2)
          (fun c' hc' d' hd' => hall c' (by simp [hc']) d' (by simp [hd'])) ht1 ht2]
  | [], _ :: _, _, _, _, hl1, _, _, _, _ => absurd hl1 (Nat.succ_ne_zero _)
  | [], [], _ :: _, _, _, _, hl2, _, _, _ => absurd hl2 (Nat.succ_ne_zero _)
  | _ :: _, [], _, _, _, hl1, _, _, _, _ => absurd hl1 (Nat.succ_ne_zero _).symm
  | _ :: _, _ :: _, [], _, _, _, hl2, _, _, _ => absurd hl2 (Nat.succ_ne_zero _).symm

/-- **Two lists agree where every codec of one row agrees with every codec of the other.** -/
theorem agreeS_list {side : Bool} {pV : Ctor (List V) V} {pA : Ctor (List A) A} {μL : M}
    {pre suf pre' suf' : List (Codec V A M)} {sp sp' : Option (Codec V A M)}
    (h : ∀ c, (c ∈ pre ∨ sp = some c ∨ c ∈ suf) → ∀ d, (d ∈ pre' ∨ sp' = some d ∨ d ∈ suf') →
      AgreeS side c d) :
    AgreeS side (listCodec pV pA μL pre sp suf) (listCodec pV pA μL pre' sp' suf') := by
  cases side
  · refine agreeP_carried fun as d₁ d₂ h1 h2 => ?_
    obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp h1
    obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
    obtain ⟨ps', hal', htr'⟩ := Option.bind_eq_some_iff.mp h2
    obtain ⟨ds', hs', hlen', rfl⟩ := alignL_eq_some.mp hal'
    exact zip_agree (fun c a => c.p a) AgreeP (fun c d hcd a y y' hy hy' => hcd a y y' hy hy')
      as ds ds' d₁ d₂ hlen hlen'
      (fun c hc d hd => h c (slotsL_mem _ _ _ _ _ hs c hc) d (slotsL_mem _ _ _ _ _ hs' d hd))
      htr htr'
  · refine agreeE_carried fun vs d₁ d₂ h1 h2 => ?_
    obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp h1
    obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
    obtain ⟨ps', hal', htr'⟩ := Option.bind_eq_some_iff.mp h2
    obtain ⟨ds', hs', hlen', rfl⟩ := alignL_eq_some.mp hal'
    exact zip_agree (fun c v => c.e v) AgreeE (fun c d hcd v y y' hy hy' => hcd v y y' hy hy')
      vs ds ds' d₁ d₂ hlen hlen'
      (fun c hc d hd => h c (slotsL_mem _ _ _ _ _ hs c hc) d (slotsL_mem _ _ _ _ _ hs' d hd))
      htr htr'

/-- The name filter of a rest policy that is not `drop` keeps every name. -/
theorem keepB_of_ne_drop {rest : RestSem V A M} (h : rest ≠ .drop) (sems : MapOf (FieldSem V A M)) :
    keepB rest sems = fun _ => true := by
  cases rest with
  | drop => exact absurd rfl h
  | refuse => rfl
  | codec _ => rfl

/-- **Two objects agree where the two codecs of each name agree.** -/
theorem agreeS_object {side : Bool} {mV : Ctor (MapOf V) V} {mA : Ctor (MapOf A) A} {μM : M}
    {sems₁ sems₂ : MapOf (FieldSem V A M)} {rest₁ rest₂ : RestSem V A M}
    (hd₁ : rest₁ ≠ .drop) (hd₂ : rest₂ ≠ .drop)
    (h : ∀ k c₁ c₂, entryCodec sems₁ (rcOf rest₁) k = some c₁ →
      entryCodec sems₂ (rcOf rest₂) k = some c₂ → AgreeS side c₁ c₂) :
    AgreeS side (objectCodec mV mA μM sems₁ rest₁) (objectCodec mV mA μM sems₂ rest₂) := by
  simp only [objectCodec, objectCodecCore, keepB_of_ne_drop hd₁, keepB_of_ne_drop hd₂]
  cases side
  · refine agreeP_carried fun m d₁ d₂ h1 h2 => ?_
    unfold objRead at h1 h2
    split at h1 <;> [skip; exact nomatch h1]
    split at h2 <;> [skip; exact nomatch h2]
    obtain ⟨G1, hG1, rfl⟩ := Option.map_eq_some_iff.mp h1
    obtain ⟨G2, hG2, rfl⟩ := Option.map_eq_some_iff.mp h2
    have : G1 = G2 := funext fun k => by
      have e1 := funImage_some hG1 k
      have e2 := funImage_some hG2 k
      obtain ⟨c₁, hc₁, hr₁⟩ := Option.bind_eq_some_iff.mp e1
      obtain ⟨c₂, hc₂, hr₂⟩ := Option.bind_eq_some_iff.mp e2
      exact (h k.1 c₁ c₂ hc₁ hc₂ : AgreeP c₁ c₂) _ _ _ hr₁ hr₂
    rw [this]
  · refine agreeE_carried fun m d₁ d₂ h1 h2 => ?_
    unfold objWrite at h1 h2
    split at h1 <;> [skip; exact nomatch h1]
    split at h2 <;> [skip; exact nomatch h2]
    obtain ⟨G1, hG1, rfl⟩ := Option.map_eq_some_iff.mp h1
    obtain ⟨G2, hG2, rfl⟩ := Option.map_eq_some_iff.mp h2
    have : G1 = G2 := funext fun k => by
      have e1 := funImage_some hG1 k
      have e2 := funImage_some hG2 k
      obtain ⟨c₁, hc₁, hr₁⟩ := Option.bind_eq_some_iff.mp e1
      obtain ⟨c₂, hc₂, hr₂⟩ := Option.bind_eq_some_iff.mp e2
      exact (h k.1 c₁ c₂ hc₁ hc₂ : AgreeE c₁ c₂) _ _ _ hr₁ hr₂
    rw [this]

/-- **The codec lemma.** Over two lawful codecs, the tree's `Compat` is exactly agreement on
    both halves. So `Compat` is symmetric there, and it is Lawson's compatibility of two partial
    bijections: `s⁻¹t` and `st⁻¹` are idempotents. -/
theorem compat_iff_agree {member : A → M} {c d : Codec V A M}
    (hc : Lawful member c) (hd : Lawful member d) :
    Compat c d ↔ (AgreeE c d ∧ AgreeP c d) := by
  constructor
  · intro h
    refine ⟨fun v a b ha hb => (h.e_agree hc.core (fun _ _ hp => hd.canon hp) ha hb).symm,
      fun a t w ht hw => (h.p_agree ht hw).symm⟩
  · rintro ⟨hE, hP⟩
    exact compat_of_agree (fun _ _ hp => hc.canon hp) hd hE (fun a t w ht hw => (hP a t w ht hw).symm)

/-- …so `Compat` is symmetric over two lawful codecs. -/
theorem compat_symm {member : A → M} {c d : Codec V A M}
    (hc : Lawful member c) (hd : Lawful member d) (h : Compat c d) : Compat d c := by
  obtain ⟨hE, hP⟩ := (compat_iff_agree hc hd).mp h
  exact (compat_iff_agree hd hc).mpr
    ⟨fun v a b ha hb => (hE v b a hb ha).symm, fun a t w ht hw => (hP a w t hw ht).symm⟩

end Agree

end Calculus.Alg
