import Calculus.Dynamo.Analysis.ScopeCompat
import Calculus.Dynamo.Analysis.ScopeOrthogonality
import Calculus.Dynamo.Lang.ScopeEquations

/-!
# Compatibility of closed codecs, at the witnesses

The witnesses of compatibility as closed codecs. Two incompatible pairs, `shout | string('X')` and
`boolean | flipBool`, read one attribute to two values, and without compatibility the order of the
options is observable. Two overlapping `refine`s of one `held` swap sit below one canonical
bound, so they are compatible, and the certificate refuses them.

The adapter of each witness cancels over the codec of the inner term, and `Closed.sound` carries
that cancellation to the lawfulness of the closed codec. `Closed.compatPair` decides each pair at
the term, with no oracle.
-/

namespace Calculus

variable {α : Table}

/-- **The decision discharges the obligation of a union** of two lawful closed options. -/
theorem Closed.pairwiseCompat_of_compatPair {x y : Closed} (h : x.compatPair y = true)
    (hl : ∀ t ∈ [x, y], Lawful (t.meaning α)) : Closed.PairwiseCompat α [x, y] := by
  have hx := hl x (List.mem_cons_self ..)
  have hy := hl y (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have hc := Closed.compat_of_compatPair h α hx hy
  intro s hs t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact compat_self _
  · exact hc.1
  · exact hc.2
  · exact compat_self _

/-- **A primitive is typed** at every environment. -/
theorem Scoped.typed_prim {w k : Nat} (τ : (s : Bool) → Alg.TableAt dynSig s) (κ : Fin 0 → Codec)
    (ρw : Fin w → Codec) (ρk : Fin k → Codec) (g : Ground) :
    ∃ T μ, Alg.Scoped.Typed τ κ ρw ρk (Alg.Scoped.Term.prim g : Scoped.Term 0 w k) T μ :=
  ⟨_, _, Alg.Scoped.Typed.node (B := dynSig) (o := .prim g) (T := Empty.elim) (μ := Empty.elim)
    (fun p => p.elim) rfl⟩

/-- **A `held` of two primitives is typed** at every environment. -/
theorem Scoped.typed_heldPrim {w k : Nat} (τ : (s : Bool) → Alg.TableAt dynSig s)
    (κ : Fin 0 → Codec) (ρw : Fin w → Codec) (ρk : Fin k → Codec) (g g' : Ground)
    (k₀ : DynGen × Bool) (ks : List (DynGen × Bool)) :
    ∃ T μ, Alg.Scoped.Typed τ κ ρw ρk
      (Scoped.Term.held false (.prim g) (.prim g') k₀ ks : Scoped.Term 0 w k) T μ := by
  obtain ⟨T1, μ1, h1⟩ := Scoped.typed_prim τ κ Fin.elim0 Fin.elim0 g
  obtain ⟨T2, μ2, h2⟩ := Scoped.typed_prim τ κ Fin.elim0 Fin.elim0 g'
  exact ⟨_, _, Alg.Scoped.Typed.node (B := dynSig) (o := .held false k₀ ks)
    (T := fun p => match p with | true => T1 | false => T2)
    (μ := fun p => match p with | true => μ1 | false => μ2)
    (fun p => match p with
      | true => h1
      | false => h2) rfl⟩

/-- **An array of a primitive is typed** at every environment. -/
theorem Scoped.typed_arrayPrim {w k : Nat} (τ : (s : Bool) → Alg.TableAt dynSig s)
    (κ : Fin 0 → Codec) (ρw : Fin w → Codec) (ρk : Fin k → Codec) (g : Ground) :
    ∃ T μ, Alg.Scoped.Typed τ κ ρw ρk (Scoped.Term.array (.prim g) : Scoped.Term 0 w k) T μ := by
  obtain ⟨T1, μ1, h1⟩ := Scoped.typed_prim τ κ ρw ρw g
  exact ⟨_, _, Alg.Scoped.Typed.node (B := dynSig) (o := .list 0 1 0) (T := fun _ => T1)
    (μ := fun _ => μ1)
    (fun p => match p with
      | .inl p => p.elim0
      | .inr (.inl _) => h1
      | .inr (.inr p) => p.elim0) rfl⟩

/-- **A closed `held` of two primitives is typed.** -/
theorem Closed.typed_heldPrim (g g' : Ground) (k₀ : DynGen × Bool) (ks : List (DynGen × Bool)) :
    (Closed.one (.held false (.prim g) (.prim g') k₀ ks)).Typed α :=
  ⟨trivial, fun i => match i with | ⟨0, _⟩ => Scoped.typed_heldPrim _ _ _ _ g g' k₀ ks⟩

/-- **A closed `held` of two primitives meets its obligations** where its adapter cancels over the
    codec of the inner primitive. -/
theorem Closed.obligations_heldPrim (g g' : Ground) (k₀ : DynGen × Bool) (ks : List (DynGen × Bool))
    (h : IsoCancels (groundCodec g) (α.word (k₀ :: ks)).1 (α.word (k₀ :: ks)).2) :
    (Closed.one (.held false (.prim g) (.prim g') k₀ ks)).Obligations α :=
  ⟨trivial, fun _ _ i => match i with
    | ⟨0, _⟩ => ⟨fun p => match p with
        | true => ⟨fun p => p.elim, trivial⟩
        | false => ⟨fun p => p.elim, trivial⟩, h, trivial⟩⟩

/-- **A closed array of a primitive is lawful.** -/
theorem Closed.lawful_arrayPrim (g : Ground) : Lawful ((Closed.one (.array (.prim g))).meaning α) :=
  Closed.sound ⟨trivial, fun i => match i with | ⟨0, _⟩ => Scoped.typed_arrayPrim _ _ _ _ g⟩
    ⟨trivial, fun _ _ i => match i with
      | ⟨0, _⟩ => ⟨fun p => match p with
          | .inl p => p.elim0
          | .inr (.inl _) => ⟨fun p => p.elim, trivial⟩
          | .inr (.inr p) => p.elim0, trivial⟩⟩

/-- **A schema people write, discharged with no certificate**: both options write `[]` as one
    attribute, so the decision accepts the pair. -/
theorem Closed.pairwiseCompat_array_literals :
    Closed.PairwiseCompat α [Closed.one (.array (.literal .string "A")),
      Closed.one (.array (.literal .string "B"))] := by
  refine Closed.pairwiseCompat_of_compatPair (by decide) fun t ht => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> exact Closed.lawful_arrayPrim _

/-- **`refine t Q` is below `t`**, over a scope term, at every environment. -/
theorem Scoped.sub_interp_refine {c w k : Nat} (τ : (s : Bool) → Alg.TableAt dynSig s)
    (κ : Fin c → Codec) (t : Scoped.Term c w k) (Q : Pred) (ρw : Fin w → Codec)
    (ρk : Fin k → Codec) :
    Sub (Alg.SFlat.interp (Alg.CStep (Alg.Scoped.TStep τ) c κ) (Scoped.Term.refine t Q ()) ρw ρk)
      (Alg.SFlat.interp (Alg.CStep (Alg.Scoped.TStep τ) c κ) t ρw ρk) := by
  rw [Scoped.interp_refine]
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
      split_ifs with h1 h2 <;> first | (subst h1; rfl) | (subst h2; rfl) | simp only [h1, h2, if_false]
  | _ => rfl

/-- The table that gives each generator the pair `swX`, `swX`. -/
def swTable : Table := fun _ => (swX, swX)

/-- The held that holds `"x"` and stores `"X"`, as a closed codec. -/
def shoutClosed : Closed :=
  Closed.one (.held false (.literal .string "X") (.literal .string "x") (.caller 0, false) [])

/-- The literal `"X"`, as a closed codec. -/
def litXClosed : Closed := Closed.one (.literal .string "X")

/-- **`shout` reads `"X"` as `"x"`.** -/
theorem Closed.shout_p : (shoutClosed.meaning swTable).p (.s "X") = some (.str "x") := rfl
/-- **`litX` reads `"X"` as `"X"`.** -/
theorem Closed.litX_p : (litXClosed.meaning swTable).p (.s "X") = some (.str "X") := rfl
/-- **`shout` writes `"x"` as `"X"`.** -/
theorem Closed.shout_e : (shoutClosed.meaning swTable).e (.str "x") = some (.s "X") := rfl
/-- **`litX` declines `"x"`.** -/
theorem Closed.litX_e : (litXClosed.meaning swTable).e (.str "x") = none := rfl

/-- **The `shout` adapter cancels over the literal**, at the codec of the literal. -/
theorem Closed.iso_shout : IsoCancels (groundCodec (.literal .string "X")) swX swX :=
  ⟨fun v _ => swX_invol v, fun v _ => swX_invol v⟩

/-- **`shout` is lawful.** -/
theorem Closed.lawful_shout : Lawful (shoutClosed.meaning swTable) :=
  Closed.sound (Closed.typed_heldPrim _ _ _ _) (Closed.obligations_heldPrim _ _ _ _ Closed.iso_shout)

/-- **The shout pair is not `Compat`**: the two options read `"X"` to two values. -/
theorem Closed.not_compat_shout : ¬ Compat (shoutClosed.meaning swTable) (litXClosed.meaning swTable) :=
  fun h => absurd (Attr.s.inj (h.p_agree Closed.shout_p Closed.litX_p)) (by decide)

/-! ## An incompatible pair: `boolean | flipBool` -/

/-- Boolean negation, and the identity on every other value. -/
def notV : Value → Value := fun v =>
  match v with
  | .bool b => .bool (!b)
  | _ => v

/-- The table that gives each generator the pair `notV`, `notV`. -/
def flipTable : Table := fun _ => (notV, notV)

/-- The held that stores the negation of a boolean, as a closed codec. -/
def flipBoolClosed : Closed := Closed.one (.held false .boolean .boolean (.caller 0, false) [])

/-- **The `flipBool` adapter cancels over `boolean`**, at the codec of `boolean`. -/
theorem Closed.iso_flip : IsoCancels (groundCodec (.base .boolean)) notV notV := by
  refine ⟨fun v _ => ?_, fun v _ => ?_⟩ <;> cases v <;> simp [notV]

/-- **`flipBool` is lawful.** -/
theorem Closed.lawful_flip : Lawful (flipBoolClosed.meaning flipTable) :=
  Closed.sound (Closed.typed_heldPrim _ _ _ _) (Closed.obligations_heldPrim _ _ _ _ Closed.iso_flip)

/-- **`boolean` and `flipBool` are not `Compat`**: the two read `true` to two values. -/
theorem Closed.not_compat_flip :
    ¬ Compat ((Closed.one .boolean).meaning flipTable) (flipBoolClosed.meaning flipTable) := by
  intro h
  have hb : ((Closed.one .boolean).meaning flipTable).p (.bool true) = some (.bool true) := rfl
  have hf : (flipBoolClosed.meaning flipTable).p (.bool true) = some (.bool false) := rfl
  exact absurd (Attr.bool.inj (h.p_agree hb hf)) (by decide)

/-- **Without `Compat`, the order of the options is observable**: the union writes `true`
    through the first option that writes it. -/
theorem Closed.flip_order_observable :
    (altCodec [(Closed.one .boolean).meaning flipTable, flipBoolClosed.meaning flipTable] none).e
        (.bool true)
      ≠ (altCodec [flipBoolClosed.meaning flipTable, (Closed.one .boolean).meaning flipTable]
        none).e (.bool true) := by
  show some (Attr.bool true) ≠ some (Attr.bool false); simp

/-! ## Compatible, and refused by `viewsDisjoint`

Two overlapping `refine`s of one `held` swap sit below one canonical bound. -/

/-- The adapter: `string` stored, `string` held, `"x"` and `"X"` swapped. -/
def swapBody {w k : Nat} : Scoped.Term 0 w k := .held false .string .string (.caller 0, false) []

/-- The members `"x"` and `"y"`. -/
def q1 : Pred := .members .string (NEFinset.of "x" {"y"})
/-- The members `"x"` and `"z"`. -/
def q2 : Pred := .members .string (NEFinset.of "x" {"z"})

/-- The adapter, as a closed codec. -/
def swapClosed : Closed := Closed.one swapBody
/-- `swap` refined to `q1`, as a closed codec. -/
def sw1Closed : Closed := Closed.one (.refine swapBody q1 ())
/-- `swap` refined to `q2`, as a closed codec. -/
def sw2Closed : Closed := Closed.one (.refine swapBody q2 ())

/-- **The `swap` adapter cancels over `string`**, at the codec of `string`. -/
theorem Closed.iso_swap : IsoCancels (groundCodec (.base .string)) swX swX :=
  ⟨fun v _ => swX_invol v, fun v _ => swX_invol v⟩

/-- **`swap` is lawful.** -/
theorem Closed.lawful_swap : Lawful (swapClosed.meaning swTable) :=
  Closed.sound (Closed.typed_heldPrim _ _ _ _) (Closed.obligations_heldPrim _ _ _ _ Closed.iso_swap)

/-- **`swap` is a canonical bound.** -/
theorem Closed.canon_swap : Canon (swapClosed.meaning swTable) :=
  fun _ _ hp => Closed.lawful_swap.canon hp

/-- **A restriction of a `held` of two primitives is typed** at every environment. -/
theorem Scoped.typed_refineHeldPrim {w k : Nat} (τ : (s : Bool) → Alg.TableAt dynSig s)
    (κ : Fin 0 → Codec) (ρw : Fin w → Codec) (ρk : Fin k → Codec) (g g' : Ground)
    (k₀ : DynGen × Bool) (ks : List (DynGen × Bool)) (q : Pred) :
    ∃ T μ, Alg.Scoped.Typed τ κ ρw ρk
      (Scoped.Term.refine (Scoped.Term.held false (.prim g) (.prim g') k₀ ks) q () :
        Scoped.Term 0 w k) T μ := by
  obtain ⟨T1, μ1, h1⟩ := Scoped.typed_heldPrim τ κ ρw ρk g g' k₀ ks
  exact ⟨_, _, Alg.Scoped.Typed.node (B := dynSig) (o := .refine q ()) (T := fun _ => T1)
    (μ := fun _ => μ1) (fun _ => h1) rfl⟩

/-- **A restriction of `swap` is lawful**: the refinement keeps the laws of the `held`. -/
theorem Closed.lawful_swRefine (q : Pred) :
    Lawful ((Closed.one (.refine swapBody q ())).meaning swTable) :=
  Closed.sound ⟨trivial, fun i => match i with
      | ⟨0, _⟩ => Scoped.typed_refineHeldPrim _ _ _ _ _ _ _ _ q⟩
    ⟨trivial, fun _ _ i => match i with
      | ⟨0, _⟩ => ⟨fun _ => ⟨fun p => match p with
          | true => ⟨fun p => p.elim, trivial⟩
          | false => ⟨fun p => p.elim, trivial⟩, Closed.iso_swap, trivial⟩, trivial⟩⟩

/-- **The two restrictions overlap at `"x"`**: both read the stored `"X"` to `"x"`. -/
theorem Closed.sw_overlap : (sw1Closed.meaning swTable).p (.s "X") = some (.str "x") ∧
    (sw2Closed.meaning swTable).p (.s "X") = some (.str "x") := ⟨rfl, rfl⟩

/-- **A restriction of `swap` is below `swap`.** -/
theorem Closed.sub_swRefine (q : Pred) :
    Sub ((Closed.one (.refine swapBody q ())).meaning swTable) (swapClosed.meaning swTable) :=
  fun o x y h => by
    rw [Closed.one_fix] at h
    rw [swapClosed, Closed.one_fix]
    exact Scoped.sub_interp_refine _ _ swapBody q
      (fun _ => (Closed.one (.refine swapBody q ())).meaning swTable) Fin.elim0 o x y h

/-- **`sw1` and `sw2` are pairwise `Compat`**, through the common bound `swap`. -/
theorem Closed.compat_sw (x y : Closed) (hx : x = sw1Closed ∨ x = sw2Closed)
    (hy : y = sw1Closed ∨ y = sw2Closed) : Compat (x.meaning swTable) (y.meaning swTable) := by
  have hsub : ∀ z, z = sw1Closed ∨ z = sw2Closed → Sub (z.meaning swTable) (swapClosed.meaning swTable) := by
    rintro z (rfl | rfl) <;> exact Closed.sub_swRefine _
  have hlaw : ∀ z, z = sw1Closed ∨ z = sw2Closed → Lawful (z.meaning swTable) := by
    rintro z (rfl | rfl) <;> exact Closed.lawful_swRefine _
  exact compat_of_common_bound' (hsub x hx) (hsub y hy) Closed.canon_swap (hlaw y hy)

/-- **The pair meets the obligation of a union** through the common bound, with no certificate. -/
theorem Closed.pairwiseCompat_sw : Closed.PairwiseCompat swTable [sw1Closed, sw2Closed] := by
  have hm : ∀ z ∈ [sw1Closed, sw2Closed], z = sw1Closed ∨ z = sw2Closed := by simp
  exact fun s hs t ht => Closed.compat_sw s t (hm s hs) (hm t ht)

/-- **The certificate refuses the pair.** -/
theorem Closed.viewsDisjoint_sw : sw1Closed.viewsDisjoint sw2Closed = false := by decide

/-! ## The decision at the witnesses

`Closed.compatPair` certifies each pair below, and `Closed.viewsDisjoint` certifies none of them.
Each pair holds a `held`, so no held-free bound covers it: the decision agrees per half and per
component. -/

/-- `{a?: swap}` and `{a?: binary}`: the two slots agree, because the two terms are disjoint. -/
example : (Closed.one (.object (Scoped.Body.mk {"a"} (fun _ => .optional swapBody) none))).compatPair
    (Closed.one (.object (Scoped.Body.mk {"a"} (fun _ => .optional .binary) none))) = true := by decide
/-- `binary` and `swap | binary`: the partner is an option of the union. -/
example : (Closed.one .binary).compatPair (Closed.one (.union [swapBody, .binary])) = true := by decide
/-- `array(swap)` and `array(boolean)`: the elements are disjoint, and the empty list is one
    attribute. -/
example : (Closed.one (.array swapBody)).compatPair (Closed.one (.array .boolean)) = true := by decide
/-- A recursive closed codec and `array(never)`. -/
example : (Closed.one (.union [swapBody, .array (.ref 0)])).compatPair
    (Closed.one (.array .never)) = true := by decide
/-- …and the certificate certifies none of the four. -/
example : (Closed.one (.object (Scoped.Body.mk {"a"} (fun _ => .optional swapBody) none))).viewsDisjoint
      (Closed.one (.object (Scoped.Body.mk {"a"} (fun _ => .optional .binary) none))) = false ∧
    (Closed.one .binary).viewsDisjoint (Closed.one (.union [swapBody, .binary])) = false ∧
    (Closed.one (.array swapBody)).viewsDisjoint (Closed.one (.array .boolean)) = false ∧
    (Closed.one (.union [swapBody, .array (.ref 0)])).viewsDisjoint (Closed.one (.array .never)) = false := by
  decide

/-- **The decision refuses the two incompatible witnesses.** -/
example : shoutClosed.compatPair litXClosed = false ∧
    (Closed.one .boolean).compatPair flipBoolClosed = false := by decide

/-- **Two restrictions of one adapter**: the decision accepts them, because the two `held`s carry
    one adapter and their inner terms agree. -/
example : sw1Closed.compatPair sw2Closed = true := by decide

end Calculus
