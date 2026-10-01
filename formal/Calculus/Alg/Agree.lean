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
variable {V M : Type}

/-- **Agreement at an orientation**: two maps at `o` that answer at one input give one output.
    At the host, two writers of one value write one attribute. At the dual, two readers of one
    attribute read one value. -/
def Agree (o : Orient) (c d : Codec V M) : Prop :=
  ∀ (x : V) (y z : V), c.f o x = some y → d.f o x = some z → y = z

/-- One half, by the side flag: `true` is the write half, at the host. -/
abbrev AgreeS (side : Bool) : Codec V M → Codec V M → Prop :=
  Agree (bif side then Orient.host else Orient.dual)

/-- **A congruence of agreement on each half is a congruence at every orientation.** A lemma
    that reads the asymmetric write and read of a combinator states the two halves apart. -/
theorem agree_of_agreeS {c d c' d' : Codec V M}
    (h : ∀ side, AgreeS side c d → AgreeS side c' d') : ∀ o, Agree o c d → Agree o c' d' :=
  Orient.both (P := fun o => Agree o c d → Agree o c' d') (h true) (h false)

/-- **Agreement at an orientation and at its dual is agreement at every orientation.** -/
theorem agree_all {c d : Codec V M} :
    ∀ {o : Orient}, Agree o c d → Agree o.op c d → ∀ o', Agree o' c d
  | ⟨(false, true), _⟩, h, h', o' => Orient.both (P := fun o' => Agree o' c d) h h' o'
  | ⟨(true, false), _⟩, h, h', o' => Orient.both (P := fun o' => Agree o' c d) h' h o'
  | ⟨(false, false), hn⟩, _, _, _ => absurd rfl hn
  | ⟨(true, true), hn⟩, _, _, _ => absurd rfl hn

/-- The empty codec agrees with every codec at each orientation. -/
theorem agree_empty_left (o : Orient) (d : Codec V M) : Agree o .empty d :=
  fun _ _ _ h => nomatch h

/-- …on the right as well. -/
theorem agree_empty_right (o : Orient) (c : Codec V M) : Agree o c .empty :=
  fun _ _ _ _ h => nomatch h

/-- Agreement is antitone on the left. -/
theorem agree_sub_left {o : Orient} {c c' d : Codec V M} (hs : Sub c c')
    (h : Agree o c' d) : Agree o c d :=
  fun x y z hy hz => h x y z (hs o x y hy) hz

/-- …and on the right. -/
theorem agree_sub_right {o : Orient} {c d d' : Codec V M} (hs : Sub d d')
    (h : Agree o c d') : Agree o c d :=
  fun x y z hy hz => h x y z hy (hs o x z hz)

/-- Two codecs below one function agree. -/
theorem agree_bound {o : Orient} {c d u : Codec V M} (hc : Sub c u) (hd : Sub d u) :
    Agree o c d := by
  intro x y z hy hz
  have h2 := hd o x z hz; rw [hc o x y hy] at h2; exact Option.some.inj h2

/-- Two codecs with apart domains at an orientation agree there. -/
theorem agree_apart {o : Orient} {c d : Codec V M}
    (h : ∀ x, ((c.f o x).isSome && (d.f o x).isSome) = false) : Agree o c d := by
  intro x y z hy hz; have := h x; rw [hy, hz] at this; exact nomatch this

/-- A union agrees with a partner where each option does. -/
theorem agree_alt_left {o : Orient} {os : List (Codec V M)} {μ : Option M} {d : Codec V M}
    (h : ∀ c ∈ os, Agree o c d) : Agree o (altCodec os μ) d := fun x y z hy hz =>
  let ⟨c, hc, _, hcy⟩ := altCodec_admits hy
  h c hc x y z hcy hz

/-- …and on the right. -/
theorem agree_alt_right {o : Orient} {os : List (Codec V M)} {μ : Option M} {c : Codec V M}
    (h : ∀ d ∈ os, Agree o c d) : Agree o c (altCodec os μ) := fun x y z hy hz =>
  let ⟨d, hd, _, hdz⟩ := altCodec_admits hz
  h d hd x y z hy hdz

/-- **Two recursive codecs agree where their stages agree**: each input reads the stage of its
    own depth, at each orientation. -/
theorem agree_mu {o : Orient} {depth : V → Nat} {B B' : Codec V M → Codec V M}
    (h : ∀ n, Agree o (muStage B n) (muStage B' n)) :
    Agree o (muCodec depth B) (muCodec depth B') :=
  fun x => h (depth x) x

/-- …and a recursive codec agrees with a partner that every stage agrees with. -/
theorem agree_mu_left {o : Orient} {depth : V → Nat} {B : Codec V M → Codec V M}
    {d : Codec V M} (h : ∀ n, Agree o (muStage B n) d) : Agree o (muCodec depth B) d :=
  fun x => h (depth x) x

/-- …on the right. -/
theorem agree_mu_right {o : Orient} {depth : V → Nat} {B : Codec V M → Codec V M}
    {c : Codec V M} (h : ∀ n, Agree o c (muStage B n)) : Agree o c (muCodec depth B) :=
  fun x => h (depth x) x

/-- Two carried codecs over one prism agree at an orientation where their payload maps agree
    there. -/
theorem agree_carried {o : Orient} {γ : Type} {p : Ctor γ V} {μ₀ : M}
    {P₁ P₂ : γ → Prop} {F₁ F₂ : Orient → γ → Option γ}
    (h : ∀ x d₁ d₂, F₁ o x = some d₁ → F₂ o x = some d₂ → d₁ = d₂) :
    Agree o (carriedCodec p μ₀ P₁ F₁) (carriedCodec p μ₀ P₂ F₂) := by
  intro v a b ha hb
  obtain ⟨x, d₁, hx, h1, rfl⟩ := carried_f.mp ha
  obtain ⟨x', d₂, hx', h2, rfl⟩ := carried_f.mp hb
  rw [hx] at hx'; cases hx'
  rw [h x d₁ d₂ h1 h2]

/-- Two rows over one list, every codec of one agreeing with every codec of the other, traverse
    to one list. -/
theorem zip_agree {X Y : Type} (run : Codec V M → X → Option Y) (R : Codec V M → Codec V M → Prop)
    (hR : ∀ c d, R c d → ∀ x y y', run c x = some y → run d x = some y' → y = y') :
    ∀ (xs : List X) (ds₁ ds₂ : List (Codec V M)) (ys₁ ys₂ : List Y),
      ds₁.length = xs.length → ds₂.length = xs.length → (∀ c ∈ ds₁, ∀ d ∈ ds₂, R c d) →
      traverse (fun cx : Codec V M × X => run cx.1 cx.2) (ds₁.zip xs) = some ys₁ →
      traverse (fun cx : Codec V M × X => run cx.1 cx.2) (ds₂.zip xs) = some ys₂ → ys₁ = ys₂
  | [], [], [], ys₁, ys₂, _, _, _, h1, h2 => by
      simp only [List.zip_nil_right, traverse_nil, Option.some.injEq] at h1 h2; rw [← h1, ← h2]
  | x :: xs, c :: cs, d :: ds, ys₁, ys₂, hl1, hl2, hall, h1, h2 => by
      simp only [List.zip_cons_cons, traverse_cons, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h1 h2
      obtain ⟨y1, hy1, t1, ht1, rfl⟩ := h1
      obtain ⟨y2, hy2, t2, ht2, rfl⟩ := h2
      rw [hR c d (hall c (by simp) d (by simp)) x y1 y2 hy1 hy2,
        zip_agree run R hR xs cs ds t1 t2 (Nat.succ.inj hl1) (Nat.succ.inj hl2)
          (fun c' hc' d' hd' => hall c' (by simp [hc']) d' (by simp [hd'])) ht1 ht2]
  | [], _ :: _, _, _, _, hl1, _, _, _, _ => absurd hl1 (Nat.succ_ne_zero _)
  | [], [], _ :: _, _, _, _, hl2, _, _, _ => absurd hl2 (Nat.succ_ne_zero _)
  | _ :: _, [], _, _, _, hl1, _, _, _, _ => absurd hl1 (Nat.succ_ne_zero _).symm
  | _ :: _, _ :: _, [], _, _, _, hl2, _, _, _ => absurd hl2 (Nat.succ_ne_zero _).symm

/-- **Two lists agree where every codec of one row agrees with every codec of the other**, at
    each orientation. -/
theorem agree_list {o : Orient} {pL : Ctor (List V) V} {μL : M}
    {pre suf pre' suf' : List (Codec V M)} {sp sp' : Option (Codec V M)}
    (h : ∀ c, (c ∈ pre ∨ sp = some c ∨ c ∈ suf) → ∀ d, (d ∈ pre' ∨ sp' = some d ∨ d ∈ suf') →
      Agree o c d) :
    Agree o (listCodec pL μL pre sp suf) (listCodec pL μL pre' sp' suf') := by
  refine agree_carried fun vs d₁ d₂ h1 h2 => ?_
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp h1
  obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
  obtain ⟨ps', hal', htr'⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨ds', hs', hlen', rfl⟩ := alignL_eq_some.mp hal'
  exact zip_agree (fun c v => c.f o v) (Agree o) (fun c d hcd v y y' hy hy' => hcd v y y' hy hy')
    vs ds ds' d₁ d₂ hlen hlen'
    (fun c hc d hd => h c (slotsL_mem _ _ _ _ _ hs c hc) d (slotsL_mem _ _ _ _ _ hs' d hd))
    htr htr'

/-- **Two objects agree where the two codecs of each name agree**, at each orientation. -/
theorem agree_object {o : Orient} {pM : Ctor (MapOf V) V} {μM : M}
    {sems₁ sems₂ : MapOf (FieldSem V M)} {rest₁ rest₂ : RestSem V M}
    (h : ∀ k c₁ c₂, entryCodec sems₁ (rcOf rest₁) k = some c₁ →
      entryCodec sems₂ (rcOf rest₂) k = some c₂ → Agree o c₁ c₂) :
    Agree o (objectCodec pM μM sems₁ rest₁) (objectCodec pM μM sems₂ rest₂) := by
  refine agree_carried fun m d₁ d₂ h1 h2 => ?_
  unfold objAt at h1 h2
  split at h1 <;> [skip; exact nomatch h1]
  split at h2 <;> [skip; exact nomatch h2]
  obtain ⟨G1, hG1, rfl⟩ := Option.map_eq_some_iff.mp h1
  obtain ⟨G2, hG2, rfl⟩ := Option.map_eq_some_iff.mp h2
  have : G1 = G2 := funext fun k => by
    have e1 := funImage_some hG1 k
    have e2 := funImage_some hG2 k
    obtain ⟨c₁, hc₁, hr₁⟩ := Option.bind_eq_some_iff.mp e1
    obtain ⟨c₂, hc₂, hr₂⟩ := Option.bind_eq_some_iff.mp e2
    exact (h k.1 c₁ c₂ hc₁ hc₂ : Agree o c₁ c₂) _ _ _ hr₁ hr₂
  rw [this]

/-- **The codec lemma.** Over two lawful codecs, the tree's `Compat` is exactly agreement on
    both halves. So `Compat` is symmetric there, and it is Lawson's compatibility of two partial
    bijections: `s⁻¹t` and `st⁻¹` are idempotents. -/
theorem compat_iff_agree {member : V → M} {c d : Codec V M}
    (hc : Lawful member c) (hd : Lawful member d) :
    Compat c d ↔ (Agree .host c d ∧ Agree .dual c d) := by
  constructor
  · intro h
    refine ⟨fun v a b ha hb => (h.e_agree hc.core (fun _ _ hp => hd.canon hp) ha hb).symm,
      fun a t w ht hw => (h.p_agree ht hw).symm⟩
  · rintro ⟨hE, hP⟩
    exact compat_of_agree (fun _ _ hp => hc.canon hp) hd hE (fun a t w ht hw => (hP a t w ht hw).symm)

/-- …so `Compat` is symmetric over two lawful codecs. -/
theorem compat_symm {member : V → M} {c d : Codec V M}
    (hc : Lawful member c) (hd : Lawful member d) (h : Compat c d) : Compat d c := by
  obtain ⟨hE, hP⟩ := (compat_iff_agree hc hd).mp h
  exact (compat_iff_agree hd hc).mpr
    ⟨fun v a b ha hb => (hE v b a hb ha).symm, fun a t w ht hw => (hP a w t hw ht).symm⟩

end Agree

end Calculus.Alg
