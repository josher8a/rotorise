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
object position by position. The soundness of the decision `Scoped.compatPair` reads these lemmas, one per row.
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
theorem agree_carried {o : Orient} {γ : Type} {member : V → M} {s : Summand γ V M member}
    {P₁ P₂ : γ → Prop} {F₁ F₂ : Orient → γ → Option γ}
    (h : ∀ x d₁ d₂, F₁ o x = some d₁ → F₂ o x = some d₂ → d₁ = d₂) :
    Agree o (carriedCodec s P₁ F₁) (carriedCodec s P₂ F₂) := by
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
theorem agree_list {o : Orient} {member : V → M} {sL : Summand (List V) V M member}
    {pre suf pre' suf' : List (Codec V M)} {sp sp' : Option (Codec V M)}
    (h : ∀ c, (c ∈ pre ∨ sp = some c ∨ c ∈ suf) → ∀ d, (d ∈ pre' ∨ sp' = some d ∨ d ∈ suf') →
      Agree o c d) :
    Agree o (listCodec sL pre sp suf) (listCodec sL pre' sp' suf') := by
  refine agree_carried fun vs d₁ d₂ h1 h2 => ?_
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp h1
  obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
  obtain ⟨ps', hal', htr'⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨ds', hs', hlen', rfl⟩ := alignL_eq_some.mp hal'
  exact zip_agree (fun c v => c.f o v) (Agree o) (fun c d hcd v y y' hy hy' => hcd v y y' hy hy')
    vs ds ds' d₁ d₂ hlen hlen'
    (fun c hc d hd => h c (slotsL_mem _ _ _ _ _ hs c hc) d (slotsL_mem _ _ _ _ _ hs' d hd))
    htr htr'

/-- **Two objects agree where the two codecs of each name agree**, and where the two slots of each
    name answer alike at absence, at each orientation. -/
theorem agree_object {o : Orient} {member : V → M} {sM : Summand (MapOf V) V M member}
    {sems₁ sems₂ : MapOf (FieldSem V M)} {rest₁ rest₂ : RestSem V M}
    (h : ∀ k c₁ c₂, entryCodec sems₁ (rcOf rest₁) k = some c₁ →
      entryCodec sems₂ (rcOf rest₂) k = some c₂ → Agree o c₁ c₂)
    (hA : ∀ k y₁ y₂, absentOf o (sems₁.at k) = some y₁ → absentOf o (sems₂.at k) = some y₂ →
      y₁ = y₂) :
    Agree o (objectCodec sM sems₁ rest₁) (objectCodec sM sems₂ rest₂) := by
  refine agree_carried fun m d₁ d₂ h1 h2 => MapOf.ext_at fun k => ?_
  have e1 := objAt_at h1 k
  have e2 := objAt_at h2 k
  rcases (m.at k).eq_none_or_eq_some with hm | ⟨v, hm⟩
  · rw [hm] at e1 e2
    exact hA k _ _ e1 e2
  · rw [hm] at e1 e2
    simp only [liftTable, Option.map_eq_some_iff] at e1 e2
    obtain ⟨a₁, ha₁, he₁⟩ := e1
    obtain ⟨a₂, ha₂, he₂⟩ := e2
    obtain ⟨c₁, hc₁, hr₁⟩ := Option.bind_eq_some_iff.mp ha₁
    obtain ⟨c₂, hc₂, hr₂⟩ := Option.bind_eq_some_iff.mp ha₂
    rw [← he₁, ← he₂, (h k c₁ c₂ hc₁ hc₂ : Agree o c₁ c₂) _ _ _ hr₁ hr₂]

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

/-! ### The union is the join

The meaning of a union is the join of its options: the union sends `x` to `y` exactly where some
option does. The join is defined where the options agree, and the first admitter is how the
host computes it. So under agreement no order of the options is observable, and no lawfulness
is needed. -/

/-- Pairwise agreement of a family at one orientation. -/
def PAgree (o : Orient) (os : List (Codec V M)) : Prop := ∀ c ∈ os, ∀ d ∈ os, Agree o c d

/-- **The join** of a family: `j` sends `x` to `y` exactly where some option does. -/
def IsJoin (os : List (Codec V M)) (j : Codec V M) : Prop :=
  ∀ o x y, j.f o x = some y ↔ ∃ c ∈ os, c.f o x = some y

/-- Under agreement at `o`, the first admitter answers what any admitter answers. -/
theorem select_eq_join {o : Orient} {os : List (Codec V M)} (h : PAgree o os) (x y : V) :
    select os (·.f o) x = some y ↔ ∃ c ∈ os, c.f o x = some y :=
  ⟨fun hs => let ⟨c, hc, _, hy⟩ := select_admits hs; ⟨c, hc, hy⟩, fun ⟨c, hc, hy⟩ =>
    let ⟨c', hf⟩ := find?_attempt o hc hy
    let ⟨y', hy'⟩ := Option.isSome_iff_exists.mp (acts_of_find? o hf)
    (h c hc c' (List.mem_of_find?_eq_some hf) x y y' hy hy') ▸ select_eq_some.mpr ⟨c', hf, hy'⟩⟩

/-- **Order is unobservable** at `o` under agreement at `o`. -/
theorem select_perm {o : Orient} {os os' : List (Codec V M)} (hp : os.Perm os')
    (h : PAgree o os) (x : V) : select os (·.f o) x = select os' (·.f o) x := by
  have h' : PAgree o os' := fun c hc d hd => h c (hp.mem_iff.mpr hc) d (hp.mem_iff.mpr hd)
  refine option_eq_of_some_iff fun y => ?_
  rw [select_eq_join h x y, select_eq_join h' x y]
  exact ⟨fun ⟨c, hc, hy⟩ => ⟨c, hp.mem_iff.mp hc, hy⟩,
    fun ⟨c, hc, hy⟩ => ⟨c, hp.mem_iff.mpr hc, hy⟩⟩

/-- **The union is the join**, at both orientations that `altCodec` reads. -/
theorem altCodec_eq_join {os : List (Codec V M)} (μ : Option M)
    (hh : PAgree .host os) (hd : PAgree .dual os) : IsJoin os (altCodec os μ) :=
  Orient.both (P := fun o => ∀ x y, (altCodec os μ).f o x = some y ↔ ∃ c ∈ os, c.f o x = some y)
    (select_eq_join hh) (select_eq_join hd)

/-- A join is unique at the maps. -/
theorem join_unique {os : List (Codec V M)} {j j' : Codec V M} (h : IsJoin os j)
    (h' : IsJoin os j') : j.f = j'.f :=
  funext fun o => funext fun x => option_eq_of_some_iff fun y => (h o x y).trans (h' o x y).symm

/-- **The join is monotone**: grow each option inside an agreeing family, and the union grows. -/
theorem altCodec_mono {o : Orient} {os os' : List (Codec V M)} {μ μ' : Option M}
    (hs : ∀ c ∈ os, ∃ c' ∈ os', ∀ x y, c.f o x = some y → c'.f o x = some y)
    (h' : PAgree o os') {x y : V} (hy : (altCodec os μ).f o x = some y) :
    (altCodec os' μ').f o x = some y :=
  let ⟨c, hc, _, hcy⟩ := altCodec_admits hy
  let ⟨c', hc', hsub⟩ := hs c hc
  (select_eq_join h' x y).mpr ⟨c', hc', hsub x y hcy⟩

/-- `union(c₁ … cₙ) = union(c_σ(1) … c_σ(n))`, **on the nose**, over pairwise agreeing options. -/
theorem altCodec_perm {os os' : List (Codec V M)} (h : os.Perm os') (μA : Option M)
    (hh : PAgree .host os) (hd : PAgree .dual os) : altCodec os μA = altCodec os' μA :=
  Codec.ext (funext fun _ => propext ⟨fun ⟨o, ho, hT⟩ => ⟨o, h.mem_iff.mp ho, hT⟩,
      fun ⟨o, ho, hT⟩ => ⟨o, h.mem_iff.mpr ho, hT⟩⟩) rfl
    (funext (select_perm h hh)) (funext (select_perm h hd))

/-- The row as the table states it, in `≡`: `Codec.Equiv.refl` transported along the equality. -/
theorem equiv_altCodec_perm {os os' : List (Codec V M)} (h : os.Perm os') (μA : Option M)
    (hh : PAgree .host os) (hd : PAgree .dual os) :
    Codec.Equiv (altCodec os μA) (altCodec os' μA) :=
  altCodec_perm h μA hh hd ▸ Codec.Equiv.refl _

/-- `union(c₁, c₂, …) ≡ union(c₂, c₁, …)`, the general theorem at `List.Perm.swap`. -/
theorem equiv_altCodec_swap (o₁ o₂ : Codec V M) (os : List (Codec V M)) (μA : Option M)
    (hh : PAgree .host (o₁ :: o₂ :: os)) (hd : PAgree .dual (o₁ :: o₂ :: os)) :
    Codec.Equiv (altCodec (o₁ :: o₂ :: os) μA) (altCodec (o₂ :: o₁ :: os) μA) :=
  equiv_altCodec_perm (List.Perm.swap o₂ o₁ os) μA hh hd

end Agree

end Calculus.Alg
