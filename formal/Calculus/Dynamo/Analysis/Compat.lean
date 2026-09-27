import Calculus.Dynamo.Analysis.Confluence
import Calculus.Lang.Compat

variable {α : Calculus.Table}

/-!
# Compatibility of the options of a union

`Compat c d` holds when each reading of `c` is a reading of `d` wherever `d`
acts at the attribute or at the value. A union of pairwise compatible lawful options is lawful
(`lawful_altCodec`). Two codecs below one canonical codec are compatible
(`compat_of_common_bound`). Every held-free term is below `opaque`, so held-free lawful terms are
pairwise compatible (`Alg.compat_of_HF`). Without compatibility, the order of the options is
observable (`flip_order_observable`).

The decision `Alg.Term.compat` states the union's law at every universe. `dynOracle` is its
DynamoDB oracle: the caller-side views decide write orthogonality, and the stored-side views
decide read orthogonality. `pairwiseCompat_of_compatPair` discharges the union's obligation of
two lawful closed options through the decision.
-/

namespace Calculus

/-- **The DynamoDB oracles**: the caller-side views decide write orthogonality, the stored-side
    views decide read orthogonality, and no adapter pair is known to be another. -/
def dynOracle : Alg.CompatOracle dynSyn :=
  ⟨fun x y => Alg.Term.disjoint pair0 (writeView x) (writeView y),
   fun x y => Alg.Term.disjoint pair0 (readView x) (readView y), fun _ _ => false⟩

/-- **The DynamoDB oracles are sound**: each view admits what its term admits, so disjoint views
    give apart domains. -/
theorem dynOracle_sound : Alg.OracleSound dynOracle where
  e x y h v := by
    rw [← Alg.Adm_eq_isSome, ← Alg.Adm_eq_isSome]
    exact Alg.apart_of_imp (writeLe_of x v) (Alg.apart_of_imp' (writeLe_of y v)
      (Alg.disjoint_sound pair0 _ _ h [] [] (fun _ _ _ hp => nomatch hp) v))
  p x y h a := by
    rw [← Alg.AdmA_eq_isSome, ← Alg.AdmA_eq_isSome]
    exact Alg.apart_of_imp (readLe_of x a) (Alg.apart_of_imp' (readLe_of y a)
      (Alg.disjoint_soundA pair0 _ _ h [] [] (fun _ _ _ hp => nomatch hp) a))
  same _ _ h := nomatch h

/-- **The decision discharges the union's obligation** of two lawful closed options. -/
theorem pairwiseCompat_of_compatPair {x y : Term} (h : Alg.compatPair dynOracle x y = true)
    (hl : ∀ t ∈ [x, y], Lawful (denote α t)) : PairwiseCompat α [x, y] :=
  Alg.pairwiseCompat_of_compatPair dynOracle_sound h hl

/-- **A `held` is monotone in both of its terms**: the same adapter over a smaller stored side and
    a smaller held side is a smaller codec. -/
theorem sub_held {i i' P P' : Term} {k : Word} (h : Sub (denote α i) (denote α i'))
    (hP : Sub (denote α P) (denote α P')) :
    Sub (denote α (.held i P k)) (denote α (.held i' P' k)) :=
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
theorem sub_union_of {os : List Term} {u : Codec} (h : ∀ o ∈ os, Sub (denote α o) u) :
    Sub (denote α (.union os)) u :=
  have hs : ∀ o ∈ denoteList α os, Sub o u := fun _ ho =>
    let ⟨t, ht, hto⟩ := List.mem_map.mp ((denoteList_eq os) ▸ ho)
    hto ▸ h t ht
  ⟨fun _ _ he => let ⟨o, ho, he⟩ := select_some he; (hs o ho).1 _ _ he,
   fun _ _ hp => let ⟨o, ho, hp⟩ := select_some hp; (hs o ho).2 _ _ hp⟩

/-- **A codec below one option of a held-free union is below the union.** Each option is below
    `Ω`, so the option that the union writes or reads through gives the answer of `o`. -/
theorem sub_union_mem {x o : Term} {os : List Term} (h : Sub (denote α x) (denote α o)) (ho : o ∈ os)
    (hf : HFL os) : Sub (denote α x) (denote α (.union os)) :=
  have hΩ : ∀ c ∈ denoteList α os, Sub c Ω := (denoteList_eq (α := α) os) ▸
    List.forall_mem_map.mpr fun t ht => sub_denote t (HFL_mem hf t ht)
  have hm : denote α o ∈ denoteList α os := (denoteList_eq (α := α) os) ▸ List.mem_map_of_mem ho
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
    Sub (denote α (.literal k x)) (baseCodec k) :=
  ⟨fun _ _ h => (restrict_e.mp h).2, fun _ _ h => (restrict_p.mp h).1⟩

/-- **Two lawful options, one below the other, meet their obligation** (Lawson, Lemma 4.8): the
    wider option is the common bound, and it reads canonically because it is lawful. -/
theorem pairwiseCompat_of_sub {x y : Term} (h : Sub (denote α x) (denote α y))
    (hl : ∀ t ∈ [x, y], Lawful (denote α t)) : PairwiseCompat α [x, y] :=
  have hb : ∀ s ∈ [x, y], Sub (denote α s) (denote α y) :=
    forall_mem_pair h ⟨fun _ _ h => h, fun _ _ h => h⟩
  fun s hs t ht => compat_of_common_bound' (hb s hs) (hb t ht)
    (fun _ _ hp => (hl y (List.mem_cons_of_mem x List.mem_cons_self)).canon hp) (hl t ht)

/-- **…and with the wider option first.** -/
theorem pairwiseCompat_of_sub' {x y : Term} (h : Sub (denote α y) (denote α x))
    (hl : ∀ t ∈ [x, y], Lawful (denote α t)) : PairwiseCompat α [x, y] :=
  have hb : ∀ s ∈ [x, y], Sub (denote α s) (denote α x) :=
    forall_mem_pair ⟨fun _ _ h => h, fun _ _ h => h⟩ h
  fun s hs t ht => compat_of_common_bound' (hb s hs) (hb t ht)
    (fun _ _ hp => (hl x List.mem_cons_self).canon hp) (hl t ht)

/-- **A schema people write, discharged with no certificate.**
    In `union(array(literal "A"), array(literal "B"))` both options write `[]`. Both write it
    as the same attribute, so the options are compatible. -/
theorem pairwiseCompat_array_literals :
    PairwiseCompat α [Term.array (.literal .string "A"), Term.array (.literal .string "B")] :=
  pairwiseCompat_of_compatPair (by decide) (forall_mem_pair
    (denote_array _ ▸ lawful_arrayCodec (lawful_literal _ _))
    (denote_array _ ▸ lawful_arrayCodec (lawful_literal _ _)))

/-- **`refine x Q` is below `x`.** -/
theorem sub_denote_refine (x : Term) (Q : Pred) : Sub (denote α (.refine x Q)) (denote α x) :=
  sub_restrict_self _ _

/-- **`held (refine t R) P k` is below `held t P k`.** -/
theorem sub_held_refine (t P : Term) (R : Pred) (k : Word) :
    Sub (denote α (.held (.refine t R) P k)) (denote α (.held t P k)) := by
  refine ⟨fun v a h => ?_, fun a v h => ?_⟩
  · obtain ⟨hq, he⟩ := restrict_e.mp h
    exact restrict_e.mpr ⟨hq, (restrict_e.mp
      (show (denote α (.refine t R)).e ((α.word k).1 v) = some a from he)).2⟩
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

/-- The table that gives each generator the pair `swX`, `swX`. -/
def swTable : Table := fun _ => (swX, swX)

/-- The held that holds `"x"` and stores `"X"`. -/
def shout : Term := .held (.literal .string "X") (.literal .string "x") [(.caller 0, false)]

/-- The literal `"X"`. -/
def litX : Term := .literal .string "X"

/-- **`shout` reads `"X"` as `"x"`.** -/
theorem shout_p : (denote swTable shout).p (.s "X") = some (.str "x") := rfl
/-- **`litX` reads `"X"` as `"X"`.** -/
theorem litX_p : (denote swTable litX).p (.s "X") = some (.str "X") := rfl
/-- **`shout` writes `"x"` as `"X"`.** -/
theorem shout_e : (denote swTable shout).e (.str "x") = some (.s "X") := rfl
/-- **`litX` declines `"x"`.** -/
theorem litX_e : (denote swTable litX).e (.str "x") = none := rfl

/-- **The `shout` adapter cancels over the literal.** -/
theorem iso_shout : IsoCancels (denote swTable (.literal .string "X")) swX swX :=
  ⟨fun v _ => swX_invol v, fun v _ => swX_invol v⟩

/-- **`shout` is lawful.** -/
theorem lawful_shout : Lawful (denote swTable shout) :=
  (Alg.Lawful.through (lawful_literal _ _) iso_shout).restrict _

/-- **The shout pair is not `Compat`**: the two options read `"X"` to two values. -/
theorem not_compat_shout : ¬ Compat (denote swTable shout) (denote swTable litX) := by
  intro h
  have := Value.str.inj (h.p_agree shout_p litX_p)
  exact absurd this (by decide)

/-! ## An incompatible pair: `boolean | flipBool` -/

/-- Boolean negation, and the identity on every other value. -/
def notV : Value → Value := fun v =>
  match v with
  | .bool b => .bool (!b)
  | _ => v

/-- The table that gives each generator the pair `notV`, `notV`. -/
def flipTable : Table := fun _ => (notV, notV)

/-- The held that stores the negation of a boolean. -/
def flipBool : Term := .held .boolean .boolean [(.caller 0, false)]

/-- **The `flipBool` adapter cancels over `boolean`.** -/
theorem iso_flip : IsoCancels (denote flipTable .boolean) notV notV := by
  refine ⟨fun v _ => ?_, fun v _ => ?_⟩ <;> cases v <;> simp [notV]

/-- **`flipBool` is lawful.** -/
theorem lawful_flip : Lawful (denote flipTable flipBool) :=
  (Alg.Lawful.through (lawful_base .boolean) iso_flip).restrict _

/-- **`boolean` and `flipBool` are not `Compat`**: the two read `true` to two values. -/
theorem not_compat_flip : ¬ Compat (denote flipTable .boolean) (denote flipTable flipBool) := by
  intro h
  have hb : (denote flipTable .boolean).p (.bool true) = some (.bool true) := rfl
  have hf : (denote flipTable flipBool).p (.bool true) = some (.bool false) := rfl
  exact absurd (Value.bool.inj (h.p_agree hb hf)) (by decide)

/-- **Without `Compat`, the order of the options is observable**: the union writes `true`
    through the first option that writes it. -/
theorem flip_order_observable :
    (altCodec [denote flipTable .boolean, denote flipTable flipBool] none).e (.bool true)
      ≠ (altCodec [denote flipTable flipBool, denote flipTable .boolean] none).e (.bool true) := by
  show some (Attr.bool true) ≠ some (Attr.bool false); simp

/-! ## Compatible, and refused by `certPair`

Two overlapping `refine`s of one `held` swap sit below one canonical bound. -/

/-- The adapter: `string` stored, `string` held, `"x"` and `"X"` swapped. -/
def swap : Term := .held .string .string [(.caller 0, false)]

/-- The members `"x"` and `"y"`. -/
def q1 : Pred := .members .string (NEFinset.of "x" {"y"})
/-- The members `"x"` and `"z"`. -/
def q2 : Pred := .members .string (NEFinset.of "x" {"z"})

/-- `swap` refined to `q1`. -/
def sw1 : Term := .refine swap q1
/-- `swap` refined to `q2`. -/
def sw2 : Term := .refine swap q2

/-- **The `swap` adapter cancels over `string`.** -/
theorem iso_swap : IsoCancels (denote swTable .string) swX swX :=
  ⟨fun v _ => swX_invol v, fun v _ => swX_invol v⟩

/-- **`swap` is lawful.** -/
theorem lawful_swap : Lawful (denote swTable swap) :=
  (Alg.Lawful.through (lawful_base .string) iso_swap).restrict _

/-- **`swap` is a canonical bound.** -/
theorem canon_swap : Canon (denote swTable swap) := fun _ _ hp => lawful_swap.canon hp

/-- **The two restrictions overlap at `"x"`**: both read the stored `"X"` to `"x"`. -/
theorem sw_overlap : (denote swTable sw1).p (.s "X") = some (.str "x") ∧
    (denote swTable sw2).p (.s "X") = some (.str "x") := ⟨rfl, rfl⟩

/-- **`sw1` and `sw2` are pairwise `Compat`**, through the common bound `swap`. -/
theorem compat_sw (x y : Term) (hx : x = sw1 ∨ x = sw2) (hy : y = sw1 ∨ y = sw2) :
    Compat (denote swTable x) (denote swTable y) := by
  have hsub : ∀ z, z = sw1 ∨ z = sw2 → Sub (denote swTable z) (denote swTable swap) := by
    rintro z (rfl | rfl) <;> exact sub_denote_refine _ _
  have hlaw : ∀ z, z = sw1 ∨ z = sw2 → Lawful (denote swTable z) := by
    rintro z (rfl | rfl) <;> exact lawful_swap.restrict _
  exact compat_of_common_bound' (hsub x hx) (hsub y hy) canon_swap (hlaw y hy)

/-- **The pair meets the union's obligation** through the common bound, with no certificate. -/
theorem pairwiseCompat_sw : PairwiseCompat swTable [sw1, sw2] := by
  have hm : ∀ z ∈ [sw1, sw2], z = sw1 ∨ z = sw2 := by simp
  exact fun s hs t ht => compat_sw s t (hm s hs) (hm t ht)

/-- **The certificate refuses the pair.** -/
theorem certPair_sw : certPair sw1 sw2 = false := by decide

/-! ## The decision at the witnesses

`compatPair` certifies each pair below, and `certPair` certifies none of them. Each pair holds a
`held`, so no held-free bound covers it: the decision agrees per half and per component. -/

/-- `{a?: swap}` and `{a?: binary}`: the two slots agree, because the two terms are disjoint. -/
example : Alg.compatPair dynOracle (Term.object (Body.mk {"a"} (fun _ => .optional swap) none))
    (Term.object (Body.mk {"a"} (fun _ => .optional Term.binary) none)) = true := by decide
/-- `binary` and `swap | binary`: the partner is an option of the union. -/
example : Alg.compatPair dynOracle Term.binary (Term.union [swap, Term.binary]) = true := by decide
/-- `array(swap)` and `array(boolean)`: the elements are disjoint, and the empty list is one
    attribute. -/
example : Alg.compatPair dynOracle (Term.array swap) (Term.array Term.boolean) = true := by decide
/-- A recursive term and `array(never)`. -/
example : Alg.compatPair dynOracle (Term.mu (.union [swap, .array (.var 0)]))
    (Term.array .never) = true := by decide
/-- …and the zero test certifies none of the four. -/
example : certPair (Term.object (Body.mk {"a"} (fun _ => .optional swap) none))
      (Term.object (Body.mk {"a"} (fun _ => .optional Term.binary) none)) = false ∧
    certPair Term.binary (Term.union [swap, Term.binary]) = false ∧
    certPair (Term.array swap) (Term.array Term.boolean) = false ∧
    certPair (Term.mu (.union [swap, .array (.var 0)])) (Term.array .never) = false := by decide

/-- **The decision refuses the two incompatible witnesses.** -/
example : Alg.compatPair dynOracle shout litX = false ∧
    Alg.compatPair dynOracle Term.boolean flipBool = false := by decide

/-- **Two restrictions of one adapter**: compatible through `swap`, and the decision does not see
    it, because the oracle knows no adapter to be another. -/
example : Alg.compatPair dynOracle sw1 sw2 = false := by decide

end Calculus
