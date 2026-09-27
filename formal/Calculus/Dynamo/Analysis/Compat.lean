import Calculus.Dynamo.Analysis.Confluence

/-!
# Compatibility of the options of a union

`Compat c d` holds when each reading of `c` is a reading of `d` wherever `d`
acts at the attribute or at the value. A union of pairwise compatible lawful options is lawful
(`lawful_altCodec`). Two codecs below one canonical codec are compatible
(`compat_of_common_bound`). Every held-free term is below `opaque`, so held-free lawful terms are
pairwise compatible (`compat_of_HF`). Without compatibility, the order of the options is
observable (`flip_order_observable`).
-/

namespace Calculus

/-- **Held-free lawful terms are pairwise `Compat`**: the common bound is `Ω`. -/
theorem compat_of_HF {s t : Term} (hs : HF s) (ht : HF t) (hlt : Lawful (denote t)) :
    Compat (denote s) (denote t) :=
  Alg.compat_of_HF (fun _ _ h => Ω_canon h) hs ht hlt

/-- **A held-free union of lawful options meets its obligation**, with no certificate. -/
theorem pairwiseCompat_of_HF {opts : List Term} (h : HFL opts)
    (hl : ∀ t ∈ opts, Lawful (denote t)) : PairwiseCompat opts :=
  fun s hs t ht => compat_of_HF (HFL_mem h s hs) (HFL_mem h t ht) (hl t ht)

/-- **A `held` is monotone in both of its terms**: the same adapter over a smaller stored side and
    a smaller held side is a smaller codec. -/
theorem sub_held {i i' P P' : Term} {f g : Value → Value} (h : Sub (denote i) (denote i'))
    (hP : Sub (denote P) (denote P')) :
    Sub (denote (.held i P f g)) (denote (.held i' P' f g)) :=
  ⟨fun _ _ he =>
    let ⟨hq, he'⟩ := restrict_e.mp he
    let ⟨a, ha⟩ := Option.isSome_iff_exists.mp hq
    restrict_e.mpr ⟨Option.isSome_iff_exists.mpr ⟨a, hP.1 _ _ ha⟩, h.1 _ _ he'⟩,
   fun _ _ hp =>
    let ⟨w, hw, hv⟩ := through_p.mp (restrict_p.mp hp).1
    let ⟨a, ha⟩ := Option.isSome_iff_exists.mp (restrict_p.mp hp).2
    restrict_p.mpr ⟨through_p.mpr ⟨w, h.2 _ _ hw, hv⟩,
      Option.isSome_iff_exists.mpr ⟨a, hP.1 _ _ ha⟩⟩⟩

/-- **A union of options below one codec is below it**, because the join answers through one
    option. -/
theorem sub_union_of {os : List Term} {u : Codec} (h : ∀ o ∈ os, Sub (denote o) u) :
    Sub (denote (.union os)) u :=
  have hs : ∀ o ∈ denoteList os, Sub o u := fun _ ho =>
    let ⟨t, ht, hto⟩ := List.mem_map.mp ((denoteList_eq os) ▸ ho)
    hto ▸ h t ht
  ⟨fun _ _ he => let ⟨o, ho, he⟩ := select_some he; (hs o ho).1 _ _ he,
   fun _ _ hp => let ⟨o, ho, hp⟩ := select_some hp; (hs o ho).2 _ _ hp⟩

/-- **A codec below one option of a held-free union is below the union.** Each option is below
    `Ω`, so the option that the union writes or reads through gives the answer of `o`. -/
theorem sub_union_mem {x o : Term} {os : List Term} (h : Sub (denote x) (denote o)) (ho : o ∈ os)
    (hf : HFL os) : Sub (denote x) (denote (.union os)) :=
  have hΩ : ∀ c ∈ denoteList os, Sub c Ω := (denoteList_eq os) ▸
    List.forall_mem_map.mpr fun t ht => sub_denote t (HFL_mem hf t ht)
  have hm : denote o ∈ denoteList os := (denoteList_eq os) ▸ List.mem_map_of_mem ho
  ⟨fun _ _ he =>
    let hoe := h.1 _ _ he
    let ⟨o', hf'⟩ := find?_attempt_V hm hoe
    let ⟨_, hb⟩ := Option.isSome_iff_exists.mp (acts_of_find?_V hf')
    altCodec_e.mpr ⟨o', hf', ((hΩ _ hm).1 _ _ hoe).symm.trans
      ((hΩ _ (List.mem_of_find?_eq_some hf')).1 _ _ hb) ▸ hb⟩,
   fun _ _ hp =>
    let hop := h.2 _ _ hp
    let ⟨o', hf'⟩ := find?_attempt_A hm hop
    let ⟨_, hw⟩ := Option.isSome_iff_exists.mp (acts_of_find?_A hf')
    altCodec_p.mpr ⟨o', hf', ((hΩ _ hm).2 _ _ hop).symm.trans
      ((hΩ _ (List.mem_of_find?_eq_some hf')).2 _ _ hw) ▸ hw⟩⟩

/-- **A literal is below its base.** -/
theorem sub_literal_base (k : GroundKind) (x : k.Carrier) :
    Sub (denote (.literal k x)) (baseCodec k) :=
  ⟨fun _ _ h => (restrict_e.mp h).2, fun _ _ h => (restrict_p.mp h).1⟩

/-- **Two lawful options, one below the other, meet their obligation** (Lawson, Lemma 4.8): the
    wider option is the common bound, and it reads canonically because it is lawful. -/
theorem pairwiseCompat_of_sub {x y : Term} (h : Sub (denote x) (denote y))
    (hl : ∀ t ∈ [x, y], Lawful (denote t)) : PairwiseCompat [x, y] :=
  have hb : ∀ s ∈ [x, y], Sub (denote s) (denote y) :=
    forall_mem_pair h ⟨fun _ _ h => h, fun _ _ h => h⟩
  fun s hs t ht => compat_of_common_bound' (hb s hs) (hb t ht)
    (fun _ _ hp => (hl y (List.mem_cons_of_mem x List.mem_cons_self)).canon hp) (hl t ht)

/-- **…and with the wider option first.** -/
theorem pairwiseCompat_of_sub' {x y : Term} (h : Sub (denote y) (denote x))
    (hl : ∀ t ∈ [x, y], Lawful (denote t)) : PairwiseCompat [x, y] :=
  have hb : ∀ s ∈ [x, y], Sub (denote s) (denote x) :=
    forall_mem_pair ⟨fun _ _ h => h, fun _ _ h => h⟩ h
  fun s hs t ht => compat_of_common_bound' (hb s hs) (hb t ht)
    (fun _ _ hp => (hl x List.mem_cons_self).canon hp) (hl t ht)

/-- **A schema people write, discharged with no certificate.**
    In `union(array(literal "A"), array(literal "B"))` both options write `[]`. Both write it
    as the same attribute, so the options are compatible. -/
theorem pairwiseCompat_array_literals :
    PairwiseCompat [Term.array (.literal .string "A"), Term.array (.literal .string "B")] :=
  pairwiseCompat_of_HF rfl (forall_mem_pair
    (denote_array _ ▸ lawful_arrayCodec (lawful_literal _ _))
    (denote_array _ ▸ lawful_arrayCodec (lawful_literal _ _)))

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
  (Alg.Lawful.through (lawful_literal _ _) iso_shout).restrict _

/-- **The shout pair is not `Compat`**: the two options read `"X"` to two values. -/
theorem not_compat_shout : ¬ Compat (denote shout) (denote litX) := by
  intro h
  have := Value.str.inj (h.p_agree shout_p litX_p)
  exact absurd this (by decide)

/-! ## An incompatible pair: `boolean | flipBool` -/

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
  (Alg.Lawful.through (lawful_base .boolean) iso_flip).restrict _

/-- **`boolean` and `flipBool` are not `Compat`**: the two read `true` to two values. -/
theorem not_compat_flip : ¬ Compat (denote .boolean) (denote flipBool) := by
  intro h
  have hb : (denote .boolean).p (.bool true) = some (.bool true) := rfl
  have hf : (denote flipBool).p (.bool true) = some (.bool false) := rfl
  exact absurd (Value.bool.inj (h.p_agree hb hf)) (by decide)

/-- **Without `Compat`, the order of the options is observable**: the union writes `true`
    through the first option that writes it. -/
theorem flip_order_observable :
    (altCodec [denote .boolean, denote flipBool] none).e (.bool true)
      ≠ (altCodec [denote flipBool, denote .boolean] none).e (.bool true) := by
  show some (Attr.bool true) ≠ some (Attr.bool false); simp

/-! ## Compatible, and refused by `certPair`

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
  (Alg.Lawful.through (lawful_base .string) iso_swap).restrict _

/-- **`swap` is a canonical bound.** -/
theorem canon_swap : Canon (denote swap) := fun _ _ hp => lawful_swap.canon hp

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

/-- **The pair meets the union's obligation** through the common bound, with no certificate. -/
theorem pairwiseCompat_sw : PairwiseCompat [sw1, sw2] := by
  have hm : ∀ z ∈ [sw1, sw2], z = sw1 ∨ z = sw2 := by simp
  exact fun s hs t ht => compat_sw s t (hm s hs) (hm t ht)

/-- **The certificate refuses the pair.** -/
theorem certPair_sw : certPair sw1 sw2 = false := by decide

end Calculus
