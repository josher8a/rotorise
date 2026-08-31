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
`denoteω_eq` below connects the two — `denoteω t = denote n t` once `n` covers the term's
depth — and `Soundnessω.lean` carries the fuel-free statement across it.
-/

namespace Calculus

noncomputable section

mutual

/-- §3–§4, denoted. Same dispatch as `denote`, no fuel. -/
def denoteω : Term → Codec
  | .literal v => literalCodec v
  | .string => stringCodec
  | .number => numberCodec
  | .decimal => decimalCodec
  | .boolean => booleanCodec
  | .null => nullCodec
  | .binary => binaryCodec
  | .literalS ls => literalSCodec ls
  | .literalN ls => literalNCodec ls
  | .set elem => setCodec (denoteω elem)
  | .array elem => arrayCodec (denoteω elem)
  | .tuple elems tail => tupleCodec (denoteωL elems) (denoteωO tail)
  | .record val => recordCodec (denoteω val)
  | .held inner f g => (denoteω inner).through f g
  | .refine inner q => (denoteω inner).restrict q
  | .legacy inner r => (denoteω inner).extendRead r
  | .nullable inner => (denoteω inner).withNull
  -- `(lazy)` concludes `⊤`: the pair is the thunk's, the member is not.
  | .lazy inner => { denoteω inner with μ := none }
  | .custom ce cp => { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp }
  -- The one case fuel used to be load-bearing for.
  | .opaq lossy => opaqCodecω lossy
  | .object fields f rest =>
      objectCodec ⟨fields, fun k => denoteωField (f k)⟩ (denoteωR rest)
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

def denoteωTags (d : Name) : List Term → List (Finset String × Codec)
  | [] => []
  | t :: ts => (tagsOf d t, denoteω t) :: denoteωTags d ts

end

/-! ## The companions are the obvious maps

Stated so later proofs can move between the spelled-out recursions and `List.map`, which
is how `denote` and the combinator lemmas phrase things. -/

/-- The field table, denoted. Outside the mutual block on purpose: the recursion has to
    see `denoteωField (f k)` at the constructor, so `denoteω` inlines it and this is the
    name the proofs use. -/
def denoteωF (fields : Finset Name) (f : {k // k ∈ fields} → Field) : MapOf FieldSem :=
  ⟨fields, fun k => denoteωField (f k)⟩

theorem denoteωL_eq : ∀ ts : List Term, denoteωL ts = ts.map denoteω
  | [] => rfl
  | t :: ts => by simp only [denoteωL, List.map, denoteωL_eq ts]

theorem denoteωO_eq : ∀ t? : Option Term, denoteωO t? = t?.map denoteω
  | none => rfl
  | some _ => rfl

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
  | .string | .number | .decimal | .boolean | .binary | .null
  | .literalS _ | .literalN _ => rfl
  | .literal v => literalCodec_μ v
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
  | .object _ _ _ => rfl
  | .union opts => by
      simp only [denoteω, altCodec, select, μSyn, denoteωMems_eq]
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
  | .string | .number | .decimal | .boolean | .binary | .null
  | .literal _ | .literalS _ | .literalN _ | .custom _ _ | .opaq _ => 1
  | .set t | .array t | .record t | .nullable t | .lazy t => termDepth t + 1
  | .held t _ _ => termDepth t + 1
  | .refine t _ => termDepth t + 1
  | .legacy t _ => termDepth t + 1
  | .tuple ts tail => max (termDepthL ts) (termDepthO tail) + 1
  -- The field table is a key set with a function on it, so its budget is a `Finset.sup`
  -- over that set — the same shape `Value.depth` takes at a `map`, and there is no
  -- `termDepthF` list companion left to write.
  | .object fields f rest =>
      max (fields.attach.sup fun k => termDepthField (f k)) (termDepthR rest) + 1
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

/-- `denoteω` is `denote` at any sufficient budget. Every term has positive depth, so a
    sufficient budget is a successor — that is the whole of the `0` case, once, rather
    than at each of the twenty-two rules. The ground terms are then `rfl`, and the rest
    is the recursion pushed under whichever combinator the rule denotes. -/
theorem denoteω_eq : ∀ (t : Term) (n : Nat), termDepth t <= n -> denoteω t = denote n t
  | t, 0, h => absurd h (by cases t <;> simp only [termDepth] <;> omega)
  | .literal _, _+1, _ => rfl
  | .string, _+1, _ => rfl
  | .number, _+1, _ => rfl
  | .decimal, _+1, _ => rfl
  | .boolean, _+1, _ => rfl
  | .null, _+1, _ => rfl
  | .binary, _+1, _ => rfl
  | .literalS _, _+1, _ => rfl
  | .literalN _, _+1, _ => rfl
  | .custom _ _, _+1, _ => rfl
  | .opaq _, _+1, _ => rfl
  | .set t, n'+1, h => by
      simp only [denoteω, denote,
        denoteω_eq t n' (by simp only [termDepth] at h; omega)]
  | .array t, n'+1, h => by
      simp only [denoteω, denote,
        denoteω_eq t n' (by simp only [termDepth] at h; omega)]
  | .record t, n'+1, h => by
      simp only [denoteω, denote,
        denoteω_eq t n' (by simp only [termDepth] at h; omega)]
  | .nullable t, n'+1, h => by
      simp only [denoteω, denote,
        denoteω_eq t n' (by simp only [termDepth] at h; omega)]
  | .lazy t, n'+1, h => by
      simp only [denoteω, denote,
        denoteω_eq t n' (by simp only [termDepth] at h; omega)]
  | .held t f g, n'+1, h => by
      simp only [denoteω, denote,
        denoteω_eq t n' (by simp only [termDepth] at h; omega)]
  | .refine t q, n'+1, h => by
      simp only [denoteω, denote,
        denoteω_eq t n' (by simp only [termDepth] at h; omega)]
  | .legacy t r, n'+1, h => by
      simp only [denoteω, denote,
        denoteω_eq t n' (by simp only [termDepth] at h; omega)]
  | .tuple ts tail, n'+1, h => by
      have hL : termDepthL ts <= n' := by simp only [termDepth] at h; omega
      have hO : termDepthO tail <= n' := by simp only [termDepth] at h; omega
      simp only [denoteω, denote, denoteωL_eq]
      rw [mapCongrω ts (denoteω_eqPt ts n' hL), denoteω_eqO tail n' hO]
  -- No `mapCongrω` on this branch: the two field tables share a key set, so agreeing
  -- pointwise *is* being the same table, and `funext` says so.
  | .object fields f rest, n'+1, h => by
      have hF : ∀ k, termDepthField (f k) <= n' := fun k => by
        -- ascribed, so `omega` sees `termDepthField (f k)` and not an unreduced redex
        have hle : termDepthField (f k)
            <= fields.attach.sup (fun k => termDepthField (f k)) :=
          Finset.le_sup (f := fun k => termDepthField (f k)) (Finset.mem_attach _ k)
        simp only [termDepth] at h; omega
      have hR : termDepthR rest <= n' := by simp only [termDepth] at h; omega
      simp only [denoteω, denote, denoteωF]
      rw [denoteω_eqR rest n' hR,
          funext fun k => denoteω_eqField (f k) n' (hF k)]
  | .union opts, n'+1, h => by
      have hpt := denoteω_eqPt opts n' (by simp only [termDepth] at h; omega)
      simp only [denoteω, denote, denoteωOpts_eq, denoteωMems_eq]
      rw [mapCongrω (f := fun t => optionSemOf (denoteω t) (specOf t))
            (g := fun t => optionSemOf (denote n' t) (specOf t))
            opts (fun t ht => by simp only [hpt t ht]),
          mapCongrω (f := fun t => (denoteω t).μ) (g := fun t => (denote n' t).μ)
            opts (fun t ht => by simp only [hpt t ht])]
  | .dunion d opts, n'+1, h => by
      have hpt := denoteω_eqPt opts n' (by simp only [termDepth] at h; omega)
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

theorem denoteω_eqR : ∀ (r : Rest) (n : Nat), termDepthR r <= n ->
    denoteωR r = restSemOf (denote n) r
  | .drop, _, _ => rfl
  | .refuse, _, _ => rfl
  | .codec t, n, h => by simp only [denoteωR, restSemOf, denoteω_eq t n h]

end

end

end Calculus
