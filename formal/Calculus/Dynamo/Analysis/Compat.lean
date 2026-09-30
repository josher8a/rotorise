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

/-- **The DynamoDB oracles**: the caller-side views decide write orthogonality, and the
    stored-side views decide read orthogonality. -/
def dynOracle : Alg.CompatOracle dynSyn :=
  ⟨fun x y => Alg.Term.disjoint pair0 (view .host x) (view .host y),
   fun x y => Alg.Term.disjoint pair0 (view .dual x) (view .dual y)⟩

/-- **The DynamoDB oracles are sound**: each view admits what its term admits, so disjoint views
    give apart domains. -/
theorem dynOracle_sound : Alg.OracleSound dynOracle where
  e {_ β} x y h v := by
    obtain rfl : β = dynTableA := funext fun g => nomatch g
    rw [← Alg.Adm_eq_isSome, ← Alg.Adm_eq_isSome]
    exact Alg.apart_of_imp (viewLe_of .host _ _ x v) (Alg.apart_of_imp' (viewLe_of .host _ _ y v)
      (Alg.disjoint_sound (S := dynSyn) pair0 _ _ h [] [] (fun _ _ _ hp => nomatch hp) v))
  p {_ β} x y h a := by
    obtain rfl : β = dynTableA := funext fun g => nomatch g
    rw [← Alg.AdmA_eq_isSome (S := dynSyn), ← Alg.AdmA_eq_isSome (S := dynSyn)]
    exact Alg.apart_of_imp (viewLe_of .dual _ _ x a) (Alg.apart_of_imp' (viewLe_of .dual _ _ y a)
      (Alg.disjoint_soundA (S := dynSyn) pair0 _ _ h [] [] (fun _ _ _ hp => nomatch hp) a))

/-- **The decision discharges the union's obligation** of two lawful closed options. -/
theorem pairwiseCompat_of_compatPair {x y : Term} (h : Alg.compatPair dynOracle x y = true)
    (hl : ∀ t ∈ [x, y], Lawful (denote α t)) : PairwiseCompat α [x, y] :=
  Alg.pairwiseCompat_of_compatPair dynOracle_sound h hl

/-- **A schema people write, discharged with no certificate.**
    In `union(array(literal "A"), array(literal "B"))` both options write `[]`. Both write it
    as the same attribute, so the options are compatible. -/
theorem pairwiseCompat_array_literals :
    PairwiseCompat α [Term.array (.literal .string "A"), Term.array (.literal .string "B")] :=
  pairwiseCompat_of_compatPair (by decide) (forall_mem_pair
    (denote_array _ ▸ lawful_arrayCodec (lawful_literal _ _))
    (denote_array _ ▸ lawful_arrayCodec (lawful_literal _ _)))

/-- **`refine x Q` is below `x`.** -/
theorem sub_denote_refine (x : Term) (Q : Pred) : Sub (denote α (.refine x Q ())) (denote α x) := by
  rw [denote_refine]
  exact sub_restrict_self _ _

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
  | s s =>
      simp only [swX]
      split_ifs <;> simp_all
  | _ => rfl

/-- The table that gives each generator the pair `swX`, `swX`. -/
def swTable : Table := fun _ => (swX, swX)

/-- The held that holds `"x"` and stores `"X"`. -/
def shout : Term := .held false (.literal .string "X") (.literal .string "x") (.caller 0, false) []

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
theorem lawful_shout : Lawful (denote swTable shout) := by
  rw [shout, denote_held]
  exact (Alg.Lawful.through (lawful_literal _ _) iso_shout).refine2 _ _

/-- **The shout pair is not `Compat`**: the two options read `"X"` to two values. -/
theorem not_compat_shout : ¬ Compat (denote swTable shout) (denote swTable litX) := by
  intro h
  have := Attr.s.inj (h.p_agree shout_p litX_p)
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
def flipBool : Term := .held false .boolean .boolean (.caller 0, false) []

/-- **The `flipBool` adapter cancels over `boolean`.** -/
theorem iso_flip : IsoCancels (denote flipTable .boolean) notV notV := by
  refine ⟨fun v _ => ?_, fun v _ => ?_⟩ <;> cases v <;> simp [notV]

/-- **`flipBool` is lawful.** -/
theorem lawful_flip : Lawful (denote flipTable flipBool) := by
  rw [flipBool, denote_held]
  exact (Alg.Lawful.through (lawful_base .boolean) iso_flip).refine2 _ _

/-- **`boolean` and `flipBool` are not `Compat`**: the two read `true` to two values. -/
theorem not_compat_flip : ¬ Compat (denote flipTable .boolean) (denote flipTable flipBool) := by
  intro h
  have hb : (denote flipTable .boolean).p (.bool true) = some (.bool true) := rfl
  have hf : (denote flipTable flipBool).p (.bool true) = some (.bool false) := rfl
  exact absurd (Attr.bool.inj (h.p_agree hb hf)) (by decide)

/-- **Without `Compat`, the order of the options is observable**: the union writes `true`
    through the first option that writes it. -/
theorem flip_order_observable :
    (altCodec [denote flipTable .boolean, denote flipTable flipBool] none).e (.bool true)
      ≠ (altCodec [denote flipTable flipBool, denote flipTable .boolean] none).e (.bool true) := by
  show some (Attr.bool true) ≠ some (Attr.bool false); simp

/-! ## Compatible, and refused by `certPair`

Two overlapping `refine`s of one `held` swap sit below one canonical bound. -/

/-- The adapter: `string` stored, `string` held, `"x"` and `"X"` swapped. -/
def swap : Term := .held false .string .string (.caller 0, false) []

/-- The members `"x"` and `"y"`. -/
def q1 : Pred := .members .string (NEFinset.of "x" {"y"})
/-- The members `"x"` and `"z"`. -/
def q2 : Pred := .members .string (NEFinset.of "x" {"z"})

/-- `swap` refined to `q1`. -/
def sw1 : Term := .refine swap q1 ()
/-- `swap` refined to `q2`. -/
def sw2 : Term := .refine swap q2 ()

/-- **The `swap` adapter cancels over `string`.** -/
theorem iso_swap : IsoCancels (denote swTable .string) swX swX :=
  ⟨fun v _ => swX_invol v, fun v _ => swX_invol v⟩

/-- **`swap` is lawful.** -/
theorem lawful_swap : Lawful (denote swTable swap) := by
  rw [swap, denote_held]
  exact (Alg.Lawful.through (lawful_base .string) iso_swap).refine2 _ _

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
    rintro z (rfl | rfl) <;> simp only [sw1, sw2, denote_refine] <;> exact lawful_swap.restrict _
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

/-- **Two restrictions of one adapter**: the decision accepts them, because the two `held`s carry
    one adapter and their inner terms agree. -/
example : Alg.compatPair dynOracle sw1 sw2 = true := by decide

end Calculus
