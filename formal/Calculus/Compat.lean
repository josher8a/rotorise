import Calculus.Confluence

/-!
# Compatibility of the options of a union

`Compat c d` holds when each reading of `c` is a reading of `d` wherever `d` acts at the
attribute or at the value. A union of pairwise compatible lawful options is lawful where the
union acts (`uAtAct_of_compat`). The rule needs no certificate and no `HF` premise. Two codecs
below one canonical codec are compatible (`compat_of_common_bound`). Every held-free term is
below `opaque`, so held-free lawful terms are pairwise compatible (`compat_of_HF`).

Compatibility is sufficient for `UAtAct`, and compatibility is not necessary. The options of
`boolean | flipBool` disagree at every attribute, and the union meets `UAtAct` because each filter
holds both options or none (`uAtAct_not_imp_compat`). `Lawful` alone does not make a common
bound give compatibility: the bound must also be `Canon` (`common_bound_lawful_insufficient`).
-/

namespace Calculus

/-- The compatibility that the count selector needs. `c` reads `a` as `t`. If `d` acts at `a`
    or at `t`, then `d` reads `a` as `t`. -/
def Compat (c d : Codec) : Prop :=
  ∀ a t, c.p a = some t → ((d.p a).isSome = true ∨ (d.e t).isSome = true) → d.p a = some t

/-! ## Compat and the two classical halves -/

/-- **Read agreement**: two compatible readings of one attribute give one value. -/
theorem Compat.p_agree {c d : Codec} (h : Compat c d) {a t w}
    (hc : c.p a = some t) (hd : d.p a = some w) : w = t := by
  have := h a t hc (Or.inl (by rw [hd]; rfl))
  rw [hd] at this; exact Option.some.inj this

/-- **The cross half**: `d` reads back from the attribute of `c` a value that both write. -/
theorem Compat.cross {c d : Codec} (hc : Lawful c) (h : Compat c d) {v a}
    (he : c.e v = some a) (hd : (d.e v).isSome = true) : d.p a = some v :=
  h a v (hc.retract he) (Or.inr hd)

/-- **Write agreement and read agreement give `Compat`** under canonical reads of `c`. So
    `Compat` is the classical compatibility on partial bijections. -/
theorem compat_of_agree {c d : Codec} (hcan : ∀ a t, c.p a = some t → c.e t = some a)
    (hd : Lawful d)
    (hE : ∀ v a b, c.e v = some a → d.e v = some b → a = b)
    (hP : ∀ a t w, c.p a = some t → d.p a = some w → w = t) : Compat c d := by
  intro a t hct hact
  rcases hact with hq | he
  · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hq
    rw [hw, hP a t w hct hw]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp he
    cases hE t a b (hcan a t hct) hb
    exact hd.retract hb

/-! ## Pairwise Compat gives UAtAct -/

/-- **A compatible lawful option acts at the attribute exactly when it acts at the value**,
    at each reading of the other option. -/
theorem acts_iff_of_compat {c d : Codec} (hd : Lawful d) (h : Compat c d) {a t}
    (hp : c.p a = some t) : (d.p a).isSome = (d.e t).isSome := by
  cases hq : d.p a with
  | some w =>
      have hw := h a t hp (Or.inl (by rw [hq]; rfl))
      rw [hq] at hw; cases hw
      exact (hd.canon hq).symm
  | none =>
      cases he : d.e t with
      | none => rfl
      | some b =>
          have := h a t hp (Or.inr (by rw [he]; rfl))
          rw [hq] at this; exact nomatch this

/-- **Pairwise `Compat` of lawful option semantics gives `UniqueBothWays`**: at each reading,
    the filter on the attribute and the filter on the value are one list. -/
theorem ubw_of_compat (os : List OptionSem)
    (hf : ∀ o ∈ os, Lawful o.c ∧ (∀ v, o.admitV v = (o.c.e v).isSome) ∧
      (∀ a, o.admitA a = (o.c.p a).isSome))
    (hc : ∀ o ∈ os, ∀ d ∈ os, Compat o.c d.c) : UniqueBothWays os := by
  have key : ∀ o ∈ os, ∀ a t, o.c.p a = some t →
      os.filter (·.admitA a) = os.filter (·.admitV t) := by
    intro o ho a t hp
    refine List.filter_congr (fun d hd => ?_)
    obtain ⟨hl, hV, hA⟩ := hf d hd
    rw [hV, hA]
    exact acts_iff_of_compat hl (hc o ho d hd) hp
  refine ⟨?_, ?_⟩
  · intro o ho t a hsel he
    rw [key o ho a t ((hf o ho).1.retract he)]; exact hsel
  · intro o ho a t _ hsel hp _
    rw [← key o ho a t hp]; exact hsel

/-- **Pairwise `Compat` of lawful options gives `UAtAct`.** No certificate, no `HF`. -/
theorem uAtAct_of_compat {opts : List Term} (hl : ∀ t ∈ opts, Lawful (denote t))
    (hc : ∀ s ∈ opts, ∀ t ∈ opts, Compat (denote s) (denote t)) : UAtAct opts := by
  refine ubw_of_compat _ (fun o ho => ?_) (fun o ho d hd => ?_)
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ho
    exact ⟨hl t ht, fun _ => rfl, fun _ => rfl⟩
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ho
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hd
    exact hc s hs t ht

/-! ## The common bound -/

/-- Canonical reads: the codec writes each value that the codec reads at the attribute that
    the codec read. -/
def Canon (u : Codec) : Prop := ∀ a t, u.p a = some t → u.e t = some a

/-- **Two codecs below one canonical bound are `Compat`.** The premises are minimal: the read
    half of `Sub c u`, both halves of `Sub d u`, `Canon u`, and `retract` of `d`. -/
theorem compat_of_common_bound {c d u : Codec}
    (hcp : ∀ a v, c.p a = some v → u.p a = some v) (hd : Sub d u) (hu : Canon u)
    (hdr : ∀ {t a}, d.e t = some a → d.p a = some t) : Compat c d := by
  intro a t hp hact
  have hup : u.p a = some t := hcp _ _ hp
  rcases hact with hq | he
  · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hq
    have := hd.2 _ _ hw
    rw [hup] at this; cases this; exact hw
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp he
    have := hd.1 _ _ hb
    rw [hu a t hup] at this; cases this
    exact hdr hb

/-- **`compat_of_common_bound` with `Sub` on both sides and a lawful `d`.** -/
theorem compat_of_common_bound' {c d u : Codec} (hc : Sub c u) (hd : Sub d u)
    (hu : Canon u) (hdl : Lawful d) : Compat c d :=
  compat_of_common_bound hc.2 hd hu hdl.retract

/-- **Held-free lawful terms are pairwise `Compat`**: the common bound is `Ω`. -/
theorem compat_of_HF {s t : Term} (hs : HF s) (ht : HF t) (hlt : Lawful (denote t)) :
    Compat (denote s) (denote t) :=
  compat_of_common_bound' (sub_denote s hs) (sub_denote t ht) (fun _ _ h => Ω_canon h) hlt

/-! ## Where `Canon` comes from -/

/-- **A restriction keeps `Canon`.** -/
theorem canon_restrict {c : Codec} (h : Canon c) (q : Value → Bool) : Canon (c.restrict q) := by
  intro a t hp
  obtain ⟨hc, hq⟩ := restrict_p.mp hp
  exact restrict_e.mpr ⟨hq, h a t hc⟩

/-- **An adapter keeps `Canon`** under `IsoCancels` alone. -/
theorem canon_through {c : Codec} (h : Canon c) {f g : Value → Value}
    (hiso : IsoCancels c f g) : Canon (c.through f g) := by
  intro a t hp
  obtain ⟨w, hw, rfl⟩ := through_p.mp hp
  have he := h a w hw
  show c.e (f (g w)) = some a
  rw [hiso.2 w (by rw [he]; rfl)]; exact he

/-- **A lawful codec below `Ω` is `Canon`.** -/
theorem canon_of_sub_Ω {c : Codec} (hl : Lawful c) (h : Sub c Ω) : Canon c := by
  intro a t hp
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hl.canon hp)
  have h1 := h.1 _ _ hb
  rw [Ω_canon (h.2 _ _ hp)] at h1
  cases h1; exact hb

/-- **A lawful `held` over a held-free inner is a canonical bound.** -/
theorem canon_held {t P : Term} {f g : Value → Value} (ht : HF t) (hl : Lawful (denote t))
    (hiso : IsoCancels (denote t) f g) : Canon (denote (.held t P f g)) :=
  canon_restrict (canon_through (canon_of_sub_Ω hl (sub_denote t ht)) hiso) _

/-- **A restriction is below the codec that it restricts.** -/
theorem sub_restrict_self (c : Codec) (q : Value → Bool) : Sub (c.restrict q) c :=
  ⟨fun _ _ h => (restrict_e.mp h).2, fun _ _ h => (restrict_p.mp h).1⟩

/-- **`refine x Q` is below `x`.** -/
theorem sub_denote_refine (x : Term) (Q : Pred) : Sub (denote (.refine x Q)) (denote x) :=
  sub_restrict_self _ _

/-- **`held (refine t R) P f g` is below `held t P f g`.** -/
theorem sub_held_refine (t P : Term) (R : Pred) (f g : Value → Value) :
    Sub (denote (.held (.refine t R) P f g)) (denote (.held t P f g)) := by
  refine ⟨fun v a h => ?_, fun a v h => ?_⟩
  · obtain ⟨hq, he⟩ := restrict_e.mp h
    exact restrict_e.mpr ⟨hq, (restrict_e.mp (show (denote (.refine t R)).e (f v) = some a from he)).2⟩
  · obtain ⟨hp, hq⟩ := restrict_p.mp h
    obtain ⟨w, hw, rfl⟩ := through_p.mp hp
    exact restrict_p.mpr ⟨through_p.mpr ⟨w, (restrict_p.mp hw).1, rfl⟩, hq⟩

/-! ## A lawful bound that is not canonical

`nonCanon` reads `"A"` and `"B"` to `"x"`, and writes `"x"` as `"B"`. The read is not
injective, so the codec is not a partial bijection, and a restriction of the codec is not
compatible with the codec. -/

/-- A lawful codec that reads `"A"` and `"B"` to `"x"`, and writes `"x"` as `"B"`. -/
def nonCanon : Codec where
  T := fun _ => True
  μ := none
  e := fun v => match v with
    | .str s => if s = "x" then some (.s "B") else none
    | _ => none
  p := fun a => match a with
    | .s s => if s = "A" ∨ s = "B" then some (.str "x") else none
    | _ => none

/-- The restriction of `nonCanon` that reads only `"B"`. -/
def nonCanonB : Codec where
  T := fun _ => True
  μ := none
  e := nonCanon.e
  p := fun a => match a with
    | .s s => if s = "B" then some (.str "x") else none
    | _ => none

/-- **`nonCanon` is lawful.** -/
theorem lawful_nonCanon : Lawful nonCanon where
  retract := by
    intro t a he
    cases t with
    | str s =>
        simp only [nonCanon] at he; split at he
        · cases he; subst_vars; rfl
        · exact nomatch he
    | _ => exact nomatch he
  canon := by
    intro a t hp
    cases a with
    | s s =>
        simp only [nonCanon] at hp; split at hp
        · cases hp; rfl
        · exact nomatch hp
    | _ => exact nomatch hp
  writes := by intro μ hμ; exact nomatch hμ
  agree := by
    intro a t a' hp he
    cases a with
    | s s =>
        cases t with
        | str r =>
            simp only [nonCanon] at he; split at he
            · cases he; exact .s _ _
            · exact nomatch he
        | _ => exact nomatch he
    | _ => exact nomatch hp

/-- **`nonCanonB` is lawful.** -/
theorem lawful_nonCanonB : Lawful nonCanonB where
  retract := by
    intro t a he
    cases t with
    | str s =>
        simp only [nonCanonB, nonCanon] at he; split at he
        · cases he; subst_vars; rfl
        · exact nomatch he
    | _ => exact nomatch he
  canon := by
    intro a t hp
    cases a with
    | s s =>
        simp only [nonCanonB] at hp; split at hp
        · cases hp; rfl
        · exact nomatch hp
    | _ => exact nomatch hp
  writes := by intro μ hμ; exact nomatch hμ
  agree := by
    intro a t a' hp he
    cases a with
    | s s =>
        cases t with
        | str r =>
            simp only [nonCanonB, nonCanon] at he; split at he
            · cases he; exact .s _ _
            · exact nomatch he
        | _ => exact nomatch he
    | _ => exact nomatch hp

/-- **`nonCanonB` is below `nonCanon`.** -/
theorem sub_nonCanonB : Sub nonCanonB nonCanon := by
  refine ⟨fun v a h => h, fun a v h => ?_⟩
  cases a with
  | s s =>
      simp only [nonCanonB] at h; split at h
      · cases h; subst_vars; rfl
      · exact nomatch h
  | _ => exact nomatch h

/-- **`Sub` is reflexive.** -/
theorem sub_refl (c : Codec) : Sub c c := ⟨fun _ _ h => h, fun _ _ h => h⟩

/-- **`nonCanon` is not `Canon`**: the codec reads `"A"` and writes the value as `"B"`. -/
theorem not_canon_nonCanon : ¬ Canon nonCanon := by
  intro h
  have := h (.s "A") (.str "x") rfl
  simp [nonCanon] at this

/-- **A lawful common bound does not give `Compat`**: `nonCanon` and `nonCanonB` are lawful
    and below the lawful `nonCanon`, and the pair is not `Compat`. -/
theorem common_bound_lawful_insufficient :
    Sub nonCanon nonCanon ∧ Sub nonCanonB nonCanon ∧ Lawful nonCanon ∧ Lawful nonCanonB ∧
      ¬ Compat nonCanon nonCanonB := by
  refine ⟨sub_refl _, sub_nonCanonB, lawful_nonCanon, lawful_nonCanonB, fun h => ?_⟩
  have := h (.s "A") (.str "x") rfl (Or.inr rfl)
  exact nomatch this

/-! ## An incompatible pair: `shout | string('X')`

The held holds `"x"` and stores `"X"`, beside the literal `"X"`. The adapter swaps `"x"` and
`"X"`, so the adapter is an involution. -/

/-- The adapter that swaps `"x"` and `"X"`, and fixes every other value. -/
def swX : Value → Value := fun v =>
  match v with
  | .str s => if s = "x" then .str "X" else if s = "X" then .str "x" else v
  | _ => v

/-- **`swX` is an involution.** -/
theorem swX_invol (v : Value) : swX (swX v) = v := by
  cases v with
  | str s =>
      simp only [swX]
      split_ifs <;> simp_all
  | _ => rfl

/-- The held that holds `"x"` and stores `"X"`. -/
def shout : Term := .held (.literal .string "X") (.literal .string "x") swX swX

/-- The literal `"X"`. -/
def litX : Term := .literal .string "X"

/-- **`shout` reads `"X"` as `"x"`.** -/
theorem shout_p : (denote shout).p (.s "X") = some (.str "x") := rfl
/-- **`litX` reads `"X"` as `"X"`.** -/
theorem litX_p : (denote litX).p (.s "X") = some (.str "X") := rfl
/-- **`shout` writes `"x"` as `"X"`.** -/
theorem shout_e : (denote shout).e (.str "x") = some (.s "X") := rfl
/-- **`litX` declines `"x"`.** -/
theorem litX_e : (denote litX).e (.str "x") = none := rfl

/-- **The `shout` adapter cancels over the literal.** -/
theorem iso_shout : IsoCancels (denote (.literal .string "X")) swX swX :=
  ⟨fun v _ => swX_invol v, fun v _ => swX_invol v⟩

/-- **`shout` is lawful.** -/
theorem lawful_shout : Lawful (denote shout) :=
  (Lawful.through (lawful_literal _ _) iso_shout).restrict _

/-- **The shout pair is not `Compat`**: the two options read `"X"` to two values. -/
theorem not_compat_shout : ¬ Compat (denote shout) (denote litX) := by
  intro h
  have := Value.str.inj (h.p_agree shout_p litX_p)
  exact absurd this (by decide)

/-- **The shout pair fails `UAtAct`** at `"x"`. -/
theorem not_uAtAct_shout : ¬ UAtAct [shout, litX] := by
  intro h
  have h1 := h.1 (optionSemOf (denote shout) (specOf shout)) (by simp [semsOf])
    (.str "x") (.s "X")
  simp [semsOf, optionSemOf, List.filter, shout_e, litX_e, shout_p, litX_p] at h1
  exact h1 shout_e

/-! ## `UAtAct` without `Compat`: `boolean | flipBool` -/

/-- Boolean negation, and the identity on every other value. -/
def notV : Value → Value := fun v =>
  match v with
  | .bool b => .bool (!b)
  | _ => v

/-- The held that stores the negation of a boolean. -/
def flipBool : Term := .held .boolean .boolean notV notV

/-- **The `flipBool` adapter cancels over `boolean`.** -/
theorem iso_flip : IsoCancels (denote .boolean) notV notV := by
  refine ⟨fun v _ => ?_, fun v _ => ?_⟩ <;> cases v <;> simp [notV]

/-- **`flipBool` is lawful.** -/
theorem lawful_flip : Lawful (denote flipBool) :=
  (Lawful.through lawful_boolean iso_flip).restrict _

/-- **`flipBool` writes the values that `boolean` writes.** -/
theorem flip_e_acts (v : Value) :
    ((denote flipBool).e v).isSome = ((denote .boolean).e v).isSome := by
  cases v <;> rfl

/-- **`flipBool` reads the attributes that `boolean` reads.** -/
theorem flip_p_acts (a : Attr) :
    ((denote flipBool).p a).isSome = ((denote .boolean).p a).isSome := by
  cases a <;> rfl

/-- **Two options that act at the same values and attributes give `UniqueBothWays`**: each
    filter holds both options or none, so no filter is a singleton. -/
theorem ubw_pair_same_acts (o₁ o₂ : OptionSem)
    (hV : ∀ v, o₁.admitV v = o₂.admitV v) (hA : ∀ a, o₁.admitA a = o₂.admitA a) :
    UniqueBothWays [o₁, o₂] := by
  refine ⟨fun o _ t _ hsel _ => ?_, fun o _ a _ _ hsel _ _ => ?_⟩
  · have := congrArg List.length hsel
    simp only [List.filter, hV t] at this
    cases hv : o₂.admitV t <;> simp [hv] at this
  · have := congrArg List.length hsel
    simp only [List.filter, hA a] at this
    cases hv : o₂.admitA a <;> simp [hv] at this

/-- **`boolean | flipBool` meets `UAtAct`.** The union declines every input. -/
theorem uAtAct_flip : UAtAct [.boolean, flipBool] :=
  ubw_pair_same_acts _ _ (fun v => (flip_e_acts v).symm) (fun a => (flip_p_acts a).symm)

/-- **`boolean` and `flipBool` are not `Compat`**: the two read `true` to two values. -/
theorem not_compat_flip : ¬ Compat (denote .boolean) (denote flipBool) := by
  intro h
  have hb : (denote .boolean).p (.bool true) = some (.bool true) := rfl
  have hf : (denote flipBool).p (.bool true) = some (.bool false) := rfl
  exact absurd (Value.bool.inj (h.p_agree hb hf)) (by decide)

/-- **`UAtAct` does not imply pairwise `Compat`, under `Lawful`.** -/
theorem uAtAct_not_imp_compat :
    ¬ (∀ opts : List Term, (∀ t ∈ opts, Lawful (denote t)) → UAtAct opts →
        ∀ s ∈ opts, ∀ t ∈ opts, Compat (denote s) (denote t)) := by
  intro h
  refine not_compat_flip (h [.boolean, flipBool] ?_ uAtAct_flip .boolean (by simp) flipBool (by simp))
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact lawful_boolean
  · exact lawful_flip

/-! ## Compatible, `UAtAct`, and refused by `certPair`

Two overlapping `refine`s of one `held` swap sit below one canonical bound. -/

/-- The adapter: `string` stored, `string` held, `"x"` and `"X"` swapped. -/
def swap : Term := .held .string .string swX swX

/-- The members `"x"` and `"y"`. -/
def q1 : Pred := .members .string (NEFinset.of "x" {"y"})
/-- The members `"x"` and `"z"`. -/
def q2 : Pred := .members .string (NEFinset.of "x" {"z"})

/-- `swap` refined to `q1`. -/
def sw1 : Term := .refine swap q1
/-- `swap` refined to `q2`. -/
def sw2 : Term := .refine swap q2

/-- **The `swap` adapter cancels over `string`.** -/
theorem iso_swap : IsoCancels (denote .string) swX swX :=
  ⟨fun v _ => swX_invol v, fun v _ => swX_invol v⟩

/-- **`swap` is lawful.** -/
theorem lawful_swap : Lawful (denote swap) :=
  (Lawful.through lawful_string iso_swap).restrict _

/-- **`swap` is a canonical bound.** -/
theorem canon_swap : Canon (denote swap) := canon_held trivial lawful_string iso_swap

/-- **The two restrictions overlap at `"x"`**: both read the stored `"X"` to `"x"`. -/
theorem sw_overlap : (denote sw1).p (.s "X") = some (.str "x") ∧
    (denote sw2).p (.s "X") = some (.str "x") := ⟨rfl, rfl⟩

/-- **`sw1` and `sw2` are pairwise `Compat`**, through the common bound `swap`. -/
theorem compat_sw (x y : Term) (hx : x = sw1 ∨ x = sw2) (hy : y = sw1 ∨ y = sw2) :
    Compat (denote x) (denote y) := by
  have hsub : ∀ z, z = sw1 ∨ z = sw2 → Sub (denote z) (denote swap) := by
    rintro z (rfl | rfl) <;> exact sub_denote_refine _ _
  have hlaw : ∀ z, z = sw1 ∨ z = sw2 → Lawful (denote z) := by
    rintro z (rfl | rfl) <;> exact lawful_swap.restrict _
  exact compat_of_common_bound' (hsub x hx) (hsub y hy) canon_swap (hlaw y hy)

/-- **The pair meets `UAtAct`** through the common bound, with no certificate. -/
theorem uAtAct_sw : UAtAct [sw1, sw2] := by
  have hm : ∀ z ∈ [sw1, sw2], z = sw1 ∨ z = sw2 := by simp
  refine uAtAct_of_compat (fun t ht => ?_) (fun s hs t ht => compat_sw s t (hm s hs) (hm t ht))
  rcases hm t ht with rfl | rfl <;> exact lawful_swap.restrict _

/-- **The certificate refuses the pair.** -/
theorem certPair_sw : certPair sw1 sw2 = false := by decide

end Calculus
