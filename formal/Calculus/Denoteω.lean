import Calculus.Denote
import Calculus.Opaque

/-!
# The denotation, without fuel

`denote : Nat → Term → Codec` needed fuel for two reasons, and both are now gone:

* `lazy` carried `Unit → Term`, which defeated the termination checker without adding a
  constructible term. `Term.lean` now carries a plain `Term`.
* `opaque` regressed on the *value*, not the term. `Opaque.lean` gives `opaqCodecω`,
  which supplies each input its own budget.

So every case here recurses on a strict subterm, and the definition is structural. The
list companions exist for the same reason `μSynList` does — `Term`'s recursive positions
sit under `List`, and structural recursion wants them spelled out rather than hidden in
`List.map`.

This is additive: the fueled `denote` and everything proved about it are untouched.
`Equivω.lean` will connect the two, and the fuel-free soundness statement follows.
-/

namespace Calculus

noncomputable section

mutual

/-- §3–§4, denoted. Same dispatch as `denote`, no fuel. -/
def denoteω : Term → Codec
  | .string => stringCodec
  | .number => numberCodec
  | .decimal => decimalCodec
  | .boolean => booleanCodec
  | .binary => binaryCodec
  | .numeric q => numericCodec q
  | .literalS ls => literalSCodec ls
  | .literalN ls => literalNCodec ls
  | .set elem => setCodec (denoteω elem)
  | .array elem => arrayCodec (denoteω elem)
  | .tuple elems tail => tupleCodec (denoteωL elems) (denoteωO tail)
  | .record val => recordCodec (denoteω val)
  | .held inner f g => (denoteω inner).through f g
  | .refine inner q => (denoteω inner).restrict q
  | .legacy inner r => (denoteω inner).extendRead r
  | .nullable inner => (denoteω inner).orNull
  -- `(lazy)` concludes `⊤`: the pair is the thunk's, the member is not.
  | .lazy inner => { denoteω inner with μ := none }
  | .custom ce cp => { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp }
  -- The one case fuel used to be load-bearing for.
  | .opaq lossy => opaqCodecω lossy
  | .object fields rest => objectCodec (denoteωF fields) (denoteωR rest)
  | .union opts => altCodec (denoteωOpts opts) (unanimous (denoteωMems opts))
  | .dunion d opts => dunionCodec d (denoteωTags d opts)

def denoteωL : List Term → List Codec
  | [] => []
  | t :: ts => denoteω t :: denoteωL ts

def denoteωO : Option Term → Option Codec
  | none => none
  | some t => some (denoteω t)

def denoteωField : Field → FieldSem
  | .req t => .req (denoteω t)
  | .optional t => .opt (denoteω t)
  | .fallback t v => .fb (denoteω t) v

def denoteωF : List (Name × Field) → List (Name × FieldSem)
  | [] => []
  | kf :: rest => (kf.1, denoteωField kf.2) :: denoteωF rest

def denoteωR : Rest → RestSem
  | .drop => .drop
  | .refuse => .refuse
  | .codec t => .codec (denoteω t)

def denoteωOpts : List Term → List OptionSem
  | [] => []
  | t :: ts => optionSemOf (denoteω t) (specOf t) :: denoteωOpts ts

def denoteωMems : List Term → List (Option Member)
  | [] => []
  | t :: ts => (denoteω t).μ :: denoteωMems ts

def denoteωTags (d : Name) : List Term → List (List String × Codec)
  | [] => []
  | t :: ts => (tagsOf d t, denoteω t) :: denoteωTags d ts

end

/-! ## The companions are the obvious maps

Stated so later proofs can move between the spelled-out recursions and `List.map`, which
is how `denote` and the combinator lemmas phrase things. -/

theorem denoteωL_eq : ∀ ts : List Term, denoteωL ts = ts.map denoteω
  | [] => rfl
  | t :: ts => by simp only [denoteωL, List.map, denoteωL_eq ts]

theorem denoteωO_eq : ∀ t? : Option Term, denoteωO t? = t?.map denoteω
  | none => rfl
  | some _ => rfl

theorem denoteωF_eq : ∀ fs : List (Name × Field),
    denoteωF fs = fs.map fun kf => (kf.1, denoteωField kf.2)
  | [] => rfl
  | kf :: fs => by simp only [denoteωF, List.map, denoteωF_eq fs]

theorem denoteωOpts_eq : ∀ ts : List Term,
    denoteωOpts ts = ts.map fun t => optionSemOf (denoteω t) (specOf t)
  | [] => rfl
  | t :: ts => by simp only [denoteωOpts, List.map, denoteωOpts_eq ts]

theorem denoteωMems_eq : ∀ ts : List Term,
    denoteωMems ts = ts.map fun t => (denoteω t).μ
  | [] => rfl
  | t :: ts => by simp only [denoteωMems, List.map, denoteωMems_eq ts]

theorem denoteωTags_eq (d : Name) : ∀ ts : List Term,
    denoteωTags d ts = ts.map fun t => (tagsOf d t, denoteω t)
  | [] => rfl
  | t :: ts => by simp only [denoteωTags, List.map, denoteωTags_eq d ts]

mutual

/-- `denoteω`'s member index is the syntactic one — `μSyn`, exactly as `denote_μ` says of
    the fueled denotation, but with no fuel hypothesis to carry. -/
theorem denoteω_μ : ∀ t : Term, (denoteω t).μ = μSyn t
  | .string | .number | .decimal | .boolean | .binary
  | .numeric _ | .literalS _ | .literalN _ => rfl
  | .set elem => by
      simp only [denoteω, μSyn, setCodec, denoteω_μ elem]
  | .array _ | .tuple _ _ | .record _ => rfl
  | .held inner _ _ => denoteω_μ inner
  | .refine inner _ => denoteω_μ inner
  | .legacy inner _ => denoteω_μ inner
  | .nullable _ => rfl
  | .lazy _ => rfl
  | .custom _ _ => rfl
  | .opaq _ => rfl
  | .object _ _ => rfl
  | .union opts => by
      simp only [denoteω, altCodec, μSyn, denoteωMems_eq]
      congr 1
      exact denoteω_μList opts
  | .dunion _ _ => rfl

/-- The `union` case of `denoteω_μ`, spelled out: the member list is `μSynList`. -/
theorem denoteω_μList : ∀ opts : List Term,
    opts.map (fun t => (denoteω t).μ) = μSynList opts
  | [] => rfl
  | t :: ts => by
      simp only [List.map, μSynList, denoteω_μ t, denoteω_μList ts]

end

/-! ## Term depth, and agreement with the fueled denotation

`denote`'s `opaq` case is now `opaqCodecω` too, so fuel enters `denote` *only* through the
term recursion — and therefore stabilizes. `termDepth` is the budget, and `denoteω_eq`
says the two denotations are equal (as codecs, not merely pointwise) once fuel reaches it.

That equality is what lets every fueled theorem be restated without fuel: no reproof, just
transport. -/

mutual

def termDepth : Term → Nat
  | .string | .number | .decimal | .boolean | .binary
  | .numeric _ | .literalS _ | .literalN _ | .custom _ _ | .opaq _ => 1
  | .set t | .array t | .record t | .nullable t | .lazy t => termDepth t + 1
  | .held t _ _ => termDepth t + 1
  | .refine t _ => termDepth t + 1
  | .legacy t _ => termDepth t + 1
  | .tuple ts tail => max (termDepthL ts) (termDepthO tail) + 1
  | .object fields rest => max (termDepthF fields) (termDepthR rest) + 1
  | .union opts => termDepthL opts + 1
  | .dunion _ opts => termDepthL opts + 1

def termDepthL : List Term → Nat
  | [] => 1
  | t :: ts => max (termDepth t) (termDepthL ts)

def termDepthO : Option Term → Nat
  | none => 1
  | some t => termDepth t

def termDepthField : Field → Nat
  | .req t => termDepth t
  | .optional t => termDepth t
  | .fallback t _ => termDepth t

def termDepthF : List (Name × Field) → Nat
  | [] => 1
  | kf :: fs => max (termDepthField kf.2) (termDepthF fs)

def termDepthR : Rest → Nat
  | .drop => 1
  | .refuse => 1
  | .codec t => termDepth t

end

/-- Pointwise-equal functions map equally. Core-only, so proved here. -/
theorem mapCongrω {α β : Type} {f g : α → β} :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.map f = l.map g
  | [], _ => rfl
  | a :: as, h => by
      simp only [List.map, h a (by simp), mapCongrω as (fun x hx => h x (by simp [hx]))]

mutual

/-- The two denotations agree once the fuel covers the term. -/
theorem denoteω_eq : ∀ (t : Term) (n : Nat), termDepth t <= n -> denoteω t = denote n t
  | .string, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' => rfl
  | .number, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' => rfl
  | .decimal, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' => rfl
  | .boolean, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' => rfl
  | .binary, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' => rfl
  | .numeric _, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' => rfl
  | .literalS _, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' => rfl
  | .literalN _, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' => rfl
  | .custom _ _, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' => rfl
  | .opaq _, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' => rfl
  | .set t, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' =>
      have hn : termDepth t <= n' := by simp only [termDepth] at h; omega
      simp only [denoteω, denote, denoteω_eq t n' hn]
  | .array t, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' =>
      have hn : termDepth t <= n' := by simp only [termDepth] at h; omega
      simp only [denoteω, denote, denoteω_eq t n' hn]
  | .record t, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' =>
      have hn : termDepth t <= n' := by simp only [termDepth] at h; omega
      simp only [denoteω, denote, denoteω_eq t n' hn]
  | .nullable t, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' =>
      have hn : termDepth t <= n' := by simp only [termDepth] at h; omega
      simp only [denoteω, denote, denoteω_eq t n' hn]
  | .lazy t, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' =>
      have hn : termDepth t <= n' := by simp only [termDepth] at h; omega
      simp only [denoteω, denote, denoteω_eq t n' hn]
  | .held t f g, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' =>
      have hn : termDepth t <= n' := by simp only [termDepth] at h; omega
      simp only [denoteω, denote, denoteω_eq t n' hn]
  | .refine t q, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' =>
      have hn : termDepth t <= n' := by simp only [termDepth] at h; omega
      simp only [denoteω, denote, denoteω_eq t n' hn]
  | .legacy t r, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' =>
      have hn : termDepth t <= n' := by simp only [termDepth] at h; omega
      simp only [denoteω, denote, denoteω_eq t n' hn]
  | .tuple ts tail, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' =>
      have hL : termDepthL ts <= n' := by simp only [termDepth] at h; omega
      have hO : termDepthO tail <= n' := by simp only [termDepth] at h; omega
      simp only [denoteω, denote, denoteωL_eq]
      rw [mapCongrω ts (denoteω_eqPt ts n' hL), denoteω_eqO tail n' hO]
  | .object fields rest, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' =>
      have hF : termDepthF fields <= n' := by simp only [termDepth] at h; omega
      have hR : termDepthR rest <= n' := by simp only [termDepth] at h; omega
      simp only [denoteω, denote, denoteωF_eq]
      rw [denoteω_eqR rest n' hR,
          mapCongrω (f := fun kf => (kf.1, denoteωField kf.2))
            (g := fun kf => (kf.1, fieldSemOf (denote n') kf.2))
            fields (denoteω_eqFPt fields n' hF)]
  | .union opts, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' =>
      have hL : termDepthL opts <= n' := by simp only [termDepth] at h; omega
      have hpt := denoteω_eqPt opts n' hL
      simp only [denoteω, denote, denoteωOpts_eq, denoteωMems_eq]
      rw [mapCongrω (f := fun t => optionSemOf (denoteω t) (specOf t))
            (g := fun t => optionSemOf (denote n' t) (specOf t))
            opts (fun t ht => by simp only [hpt t ht]),
          mapCongrω (f := fun t => (denoteω t).μ) (g := fun t => (denote n' t).μ)
            opts (fun t ht => by simp only [hpt t ht])]
  | .dunion d opts, n, h => by
      cases n with | zero => exact absurd h (by simp [termDepth]) | succ n' =>
      have hL : termDepthL opts <= n' := by simp only [termDepth] at h; omega
      have hpt := denoteω_eqPt opts n' hL
      simp only [denoteω, denote, denoteωTags_eq]
      rw [mapCongrω (f := fun t => (tagsOf d t, denoteω t))
            (g := fun t => (tagsOf d t, denote n' t))
            opts (fun t ht => by simp only [hpt t ht])]

theorem denoteω_eqPt : ∀ (ts : List Term) (n : Nat), termDepthL ts <= n ->
    ∀ t ∈ ts, denoteω t = denote n t
  | [], _, _, t, ht => absurd ht (by simp)
  | t :: ts, n, h, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact denoteω_eq x n (by simp only [termDepthL] at h; omega)
      · exact denoteω_eqPt ts n (by simp only [termDepthL] at h; omega) x hx'

theorem denoteω_eqO : ∀ (t? : Option Term) (n : Nat), termDepthO t? <= n ->
    denoteωO t? = t?.map (denote n)
  | none, _, _ => rfl
  | some t, n, h => by
      simp only [denoteωO, Option.map, denoteω_eq t n h]

theorem denoteω_eqField : ∀ (f : Field) (n : Nat), termDepthField f <= n ->
    denoteωField f = fieldSemOf (denote n) f
  | .req t, n, h => by simp only [denoteωField, fieldSemOf, denoteω_eq t n h]
  | .optional t, n, h => by simp only [denoteωField, fieldSemOf, denoteω_eq t n h]
  | .fallback t v, n, h => by simp only [denoteωField, fieldSemOf, denoteω_eq t n h]

theorem denoteω_eqFPt : ∀ (fs : List (Name × Field)) (n : Nat), termDepthF fs <= n ->
    ∀ kf ∈ fs, (kf.1, denoteωField kf.2) = (kf.1, fieldSemOf (denote n) kf.2)
  | [], _, _, kf, hkf => absurd hkf (by simp)
  | kf :: fs, n, h, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [denoteω_eqField x.2 n (by simp only [termDepthF] at h; omega)]
      · exact denoteω_eqFPt fs n (by simp only [termDepthF] at h; omega) x hx'

theorem denoteω_eqR : ∀ (r : Rest) (n : Nat), termDepthR r <= n ->
    denoteωR r = restSemOf (denote n) r
  | .drop, _, _ => rfl
  | .refuse, _, _ => rfl
  | .codec t, n, h => by simp only [denoteωR, restSemOf, denoteω_eq t n h]

end

end

end Calculus
