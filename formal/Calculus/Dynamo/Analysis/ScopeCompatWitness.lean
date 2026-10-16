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
theorem Scoped.typed_prim {w k : Nat} (τ : (s : Bool) → Alg.TableAt dynSig s)
    (ρw : Fin w → Codec) (ρk : Fin k → Codec) (g : Ground) :
    ∃ T μ, Alg.Scoped.Typed τ ρw ρk (Alg.Scoped.Term.prim g : Scoped.Term w k) T μ :=
  ⟨_, _, Alg.Scoped.Typed.node (B := dynSig) (o := .prim g) (T := Empty.elim) (μ := Empty.elim)
    (fun p => p.elim) rfl⟩

/-- **A closed primitive is typed.** -/
theorem Scoped.typedC_prim (τ : (s : Bool) → Alg.TableAt dynSig s) (g : Ground) :
    ∃ T μ, Alg.Scoped.TypedC τ (Scoped.Graph.Term.prim g : Scoped.Graph.Term 0) T μ :=
  ⟨_, _, Alg.Scoped.TypedC.node (B := dynSig) (o := .prim g) (T := Empty.elim) (μ := Empty.elim)
    (fun p => p.elim) rfl⟩

/-- **A `held` of two primitives is typed** at every environment. -/
theorem Scoped.typed_heldPrim {w k : Nat} (τ : (s : Bool) → Alg.TableAt dynSig s)
    (ρw : Fin w → Codec) (ρk : Fin k → Codec) (g g' : Ground)
    (k₀ : DynGen × Bool) (ks : List (DynGen × Bool)) :
    ∃ T μ, Alg.Scoped.Typed τ ρw ρk
      (Scoped.Term.held false (.prim g) (.prim g') k₀ ks : Scoped.Term w k) T μ := by
  obtain ⟨T1, μ1, h1⟩ := Scoped.typedC_prim τ g
  obtain ⟨T2, μ2, h2⟩ := Scoped.typedC_prim τ g'
  exact ⟨_, _, Alg.Scoped.Typed.wall (B := dynSig) (o := .held false k₀ ks)
    (T := fun p => match p with | true => T1 | false => T2)
    (μ := fun p => match p with | true => μ1 | false => μ2)
    (fun p => match p with
      | true => h1
      | false => h2) rfl⟩

/-- **An array of an entry is typed** at every environment. -/
theorem Scoped.typed_array {w k : Nat} (τ : (s : Bool) → Alg.TableAt dynSig s)
    (ρw : Fin w → Codec) (ρk : Fin k → Codec) (j : Fin w) :
    ∃ T μ, Alg.Scoped.Typed τ ρw ρk (Scoped.Term.array j : Scoped.Term w k) T μ :=
  ⟨_, _, Alg.Scoped.Typed.down (B := dynSig) (o := .list 0 1 0) rfl⟩

/-- **A closed `held` of two primitives is typed.** -/
theorem Closed.typed_heldPrim (g g' : Ground) (k₀ : DynGen × Bool) (ks : List (DynGen × Bool)) :
    (Closed.one (.held false (.prim g) (.prim g') k₀ ks)).Typed α :=
  fun i => match i with | ⟨0, _⟩ => Scoped.typed_heldPrim _ _ _ g g' k₀ ks

/-- **A closed `held` of two primitives meets its obligations** where its adapter cancels over the
    codec of the inner primitive. -/
theorem Closed.obligations_heldPrim (g g' : Ground) (k₀ : DynGen × Bool) (ks : List (DynGen × Bool))
    (h : IsoCancels (groundCodec g) (α.word (k₀ :: ks)).1 (α.word (k₀ :: ks)).2) :
    (Closed.one (.held false (.prim g) (.prim g') k₀ ks)).Obligations α :=
  fun _ _ i => match i with
    | ⟨0, _⟩ => ⟨fun p => match p with
        | true => ⟨fun p => p.elim, trivial⟩
        | false => ⟨fun p => p.elim, trivial⟩, h, trivial⟩

/-- An array of a primitive, as a closed codec of two entries. -/
def arrayPrimClosed (g : Ground) : Closed := Closed.two (.array 1) (Alg.Scoped.Term.prim g)

/-- **A closed array of a primitive is lawful.** -/
theorem Closed.lawful_arrayPrim (g : Ground) : Lawful ((arrayPrimClosed g).meaning α) :=
  Closed.sound (fun i => match i with
      | ⟨0, _⟩ => Scoped.typed_array _ _ _ ⟨1, Nat.one_lt_two⟩
      | ⟨1, _⟩ => Scoped.typed_prim _ _ _ g)
    fun _ _ i => match i with
      | ⟨0, _⟩ => trivial
      | ⟨1, _⟩ => ⟨fun p => p.elim, trivial⟩

/-- **A schema people write, discharged with no certificate**: both options write `[]` as one
    attribute, so the decision accepts the pair. -/
theorem Closed.pairwiseCompat_array_literals :
    Closed.PairwiseCompat α [arrayPrimClosed (.literal .string "A"),
      arrayPrimClosed (.literal .string "B")] := by
  refine Closed.pairwiseCompat_of_compatPair (by decide) fun t ht => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> exact Closed.lawful_arrayPrim _

/-- **`refine t Q` is below `t`**, over a scope term, at every environment. -/
theorem Scoped.sub_interp_refine {w k : Nat} (τ : (s : Bool) → Alg.TableAt dynSig s)
    (t : Scoped.Term w k) (Q : Pred) (ρw : Fin w → Codec)
    (ρk : Fin k → Codec) :
    Sub (Alg.SFlat.interp (Alg.Scoped.TStep τ) (Scoped.Term.refine t Q ()) ρw ρk)
      (Alg.SFlat.interp (Alg.Scoped.TStep τ) t ρw ρk) := by
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

/-- **`shoutClosed` reads `"X"` as `"x"`.** -/
theorem Closed.shout_p : (shoutClosed.meaning swTable).p (.s "X") = some (.str "x") := rfl
/-- **`litXClosed` reads `"X"` as `"X"`.** -/
theorem Closed.litX_p : (litXClosed.meaning swTable).p (.s "X") = some (.str "X") := rfl
/-- **`shoutClosed` writes `"x"` as `"X"`.** -/
theorem Closed.shout_e : (shoutClosed.meaning swTable).e (.str "x") = some (.s "X") := rfl
/-- **`litXClosed` declines `"x"`.** -/
theorem Closed.litX_e : (litXClosed.meaning swTable).e (.str "x") = none := rfl

/-- **The `shoutClosed` adapter cancels over the literal**, at the codec of the literal. -/
theorem Closed.iso_shout : IsoCancels (groundCodec (.literal .string "X")) swX swX :=
  ⟨fun v _ => swX_invol v, fun v _ => swX_invol v⟩

/-- **`shoutClosed` is lawful.** -/
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

/-- **The `flipBoolClosed` adapter cancels over `boolean`**, at the codec of `boolean`. -/
theorem Closed.iso_flip : IsoCancels (groundCodec (.base .boolean)) notV notV := by
  refine ⟨fun v _ => ?_, fun v _ => ?_⟩ <;> cases v <;> simp [notV]

/-- **`flipBoolClosed` is lawful.** -/
theorem Closed.lawful_flip : Lawful (flipBoolClosed.meaning flipTable) :=
  Closed.sound (Closed.typed_heldPrim _ _ _ _) (Closed.obligations_heldPrim _ _ _ _ Closed.iso_flip)

/-- **`boolean` and `flipBoolClosed` are not `Compat`**: the two read `true` to two values. -/
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
def swapBody {w k : Nat} : Scoped.Term w k := .held false .string .string (.caller 0, false) []

/-- The predicate that holds at `"x"` and at `"y"`. -/
def q1 : Pred := .closure fun v => inL .string "x" v || inL .string "y" v
/-- The predicate that holds at `"x"` and at `"z"`. -/
def q2 : Pred := .closure fun v => inL .string "x" v || inL .string "z" v

/-- The adapter, as a closed codec. -/
def swapClosed : Closed := Closed.one swapBody
/-- `swapClosed` refined to `q1`, as a closed codec. -/
def sw1Closed : Closed := Closed.one (.refine swapBody q1 ())
/-- `swapClosed` refined to `q2`, as a closed codec. -/
def sw2Closed : Closed := Closed.one (.refine swapBody q2 ())

/-- **The `swapClosed` adapter cancels over `string`**, at the codec of `string`. -/
theorem Closed.iso_swap : IsoCancels (groundCodec (.base .string)) swX swX :=
  ⟨fun v _ => swX_invol v, fun v _ => swX_invol v⟩

/-- **`swapClosed` is lawful.** -/
theorem Closed.lawful_swap : Lawful (swapClosed.meaning swTable) :=
  Closed.sound (Closed.typed_heldPrim _ _ _ _) (Closed.obligations_heldPrim _ _ _ _ Closed.iso_swap)

/-- **`swapClosed` is a canonical bound.** -/
theorem Closed.canon_swap : Canon (swapClosed.meaning swTable) :=
  fun _ _ hp => Closed.lawful_swap.canon hp

/-- **A restriction of a `held` of two primitives is typed** at every environment. -/
theorem Scoped.typed_refineHeldPrim {w k : Nat} (τ : (s : Bool) → Alg.TableAt dynSig s)
    (ρw : Fin w → Codec) (ρk : Fin k → Codec) (g g' : Ground)
    (k₀ : DynGen × Bool) (ks : List (DynGen × Bool)) (q : Pred) :
    ∃ T μ, Alg.Scoped.Typed τ ρw ρk
      (Scoped.Term.refine (Scoped.Term.held false (.prim g) (.prim g') k₀ ks) q () :
        Scoped.Term w k) T μ := by
  obtain ⟨T1, μ1, h1⟩ := Scoped.typed_heldPrim τ ρw ρk g g' k₀ ks
  exact ⟨_, _, Alg.Scoped.Typed.node (B := dynSig) (o := .refine q ()) (T := fun _ => T1)
    (μ := fun _ => μ1) (fun _ => h1) rfl⟩

/-- **A restriction of `swapClosed` is lawful**: the refinement keeps the laws of the `held`. -/
theorem Closed.lawful_swRefine (q : Pred) :
    Lawful ((Closed.one (.refine swapBody q ())).meaning swTable) :=
  Closed.sound (fun i => match i with
      | ⟨0, _⟩ => Scoped.typed_refineHeldPrim _ _ _ _ _ _ _ q)
    fun _ _ i => match i with
      | ⟨0, _⟩ => ⟨fun _ => ⟨fun p => match p with
          | true => ⟨fun p => p.elim, trivial⟩
          | false => ⟨fun p => p.elim, trivial⟩, Closed.iso_swap, trivial⟩, trivial⟩

/-- **The two restrictions overlap at `"x"`**: both read the stored `"X"` to `"x"`. -/
theorem Closed.sw_overlap : (sw1Closed.meaning swTable).p (.s "X") = some (.str "x") ∧
    (sw2Closed.meaning swTable).p (.s "X") = some (.str "x") := ⟨rfl, rfl⟩

/-- **A restriction of `swapClosed` is below `swapClosed`.** -/
theorem Closed.sub_swRefine (q : Pred) :
    Sub ((Closed.one (.refine swapBody q ())).meaning swTable) (swapClosed.meaning swTable) :=
  fun o x y h => by
    rw [Closed.one_fix] at h
    rw [swapClosed, Closed.one_fix]
    exact Scoped.sub_interp_refine _ swapBody q
      (fun _ => (Closed.one (.refine swapBody q ())).meaning swTable) Fin.elim0 o x y h

/-- **`sw1Closed` and `sw2Closed` are pairwise `Compat`**, through the common bound `swapClosed`. -/
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
example : (Closed.two (.object (Scoped.Body.mk {"a"} (fun _ => .optional 1) none)) swapBody).compatPair
    (Closed.two (.object (Scoped.Body.mk {"a"} (fun _ => .optional 1) none)) .binary) = true := by
  decide
/-- `binary` and `swap | binary`: the partner is an option of the union. -/
example : (Closed.one .binary).compatPair (Closed.one (.union [swapBody, .binary])) = true := by decide
/-- `array(swap)` and `array(boolean)`: the elements are disjoint, and the empty list is one
    attribute. -/
example : (Closed.two (.array 1) swapBody).compatPair (Closed.two (.array 1) .boolean) = true := by
  decide
/-- A recursive closed codec and `array(never)`. -/
example : (Closed.one (.union [swapBody, .array 0])).compatPair
    (Closed.two (.array 1) .never) = true := by decide
/-- …and the certificate certifies none of the four. -/
example : (Closed.two (.object (Scoped.Body.mk {"a"} (fun _ => .optional 1) none)) swapBody).viewsDisjoint
      (Closed.two (.object (Scoped.Body.mk {"a"} (fun _ => .optional 1) none)) .binary) = false ∧
    (Closed.one .binary).viewsDisjoint (Closed.one (.union [swapBody, .binary])) = false ∧
    (Closed.two (.array 1) swapBody).viewsDisjoint (Closed.two (.array 1) .boolean) = false ∧
    (Closed.one (.union [swapBody, .array 0])).viewsDisjoint (Closed.two (.array 1) .never) = false := by
  decide

/-- **The decision refuses the two incompatible witnesses.** -/
example : shoutClosed.compatPair litXClosed = false ∧
    (Closed.one .boolean).compatPair flipBoolClosed = false := by decide

/-- **Two restrictions of one adapter**: the decision accepts them, because the two `held`s carry
    one adapter and their inner terms agree. -/
example : sw1Closed.compatPair sw2Closed = true := by decide

end Calculus
