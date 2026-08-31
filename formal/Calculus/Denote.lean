import Calculus.Term
import Calculus.Combinators
import Calculus.Opaque

/-!
# Denotation

`denote fuel t` dispatches each term to its certified combinator (Combinators.lean).
Fuel is primary: every recursive call decrements it, so termination is structural on
`Nat` and `lazy` costs nothing special — at fuel 0 every term's pair is empty and its
laws hold vacuously. The **index is not**: `denote 0 t` keeps `μ := μSyn t`, which is the
whole content of `denote_μ` and the reason the `⇝` column stays truthful at every depth.
The doc's `lazy` case ("partiality is doing the termination argument's work") is this,
literally. Laws are stated for all fuel (Soundness.lean).
-/

namespace Calculus

noncomputable section

/-- The name spec of an object option: `(name, required?)` — `none` for non-objects. -/
def specOf : Term → Option (MapOf Bool)
  | .object fields f _ =>
    some ⟨fields, fun k => match f k with | .optional _ => false | _ => true⟩
  | _ => none

/-- The tags an object option answers to on discriminator `d` (§5 `(dunion)`).
    `req` only: a `fallback` discriminator would fill an absent tag with an arbitrary
    default, breaking the value-side stamp — and the implementation refuses one too
    (`discriminatedUnion` demands a bare `literal`). -/
def tagsOfField : Option Field → Finset String
  | some (.req (.literalS ls)) => ls.1
  | _ => ∅

def tagsOf (d : Name) : Term → Finset String
  | .object fields f _ => tagsOfField (MapOf.at ⟨fields, f⟩ d)
  | _ => ∅

/-- `(literal)`'s member is its base's — the dispatch in `literalCodec` and the one in
    `GroundValue.member` agree case for case.

    `literalMember : Value → Option Member` used to sit here, and its `| _ => none` was the
    `g ground` premise wearing a function's clothes. `GroundValue.member` is total, so the
    `Option` here is only `Codec.μ`'s own — a codec that writes no attribute — and never
    "this payload had no base". -/
theorem literalCodec_μ (v : GroundValue) : (literalCodec v).μ = some v.member := by
  cases v <;> rfl

mutual

/-- The member a term stores, syntactically — the `⇝` index computed from the term.
    Fuel-free: `lazy` concludes `⊤` (the doc's `(lazy)` rule), so the thunk is never
    forced. -/
def μSyn : Term → Option Member
  | .string => some .S
  | .literal v => some v.member
  | .literalS _ => some .S
  | .number => some .N
  | .decimal => some .N
  | .literalN _ => some .N
  | .boolean => some .BOOL
  | .null => some .NULL
  | .binary => some .B
  | .set t => (μSyn t).bind setMember
  | .array _ => some .L
  | .tuple _ _ => some .L
  | .record _ => some .M
  | .held t _ _ => μSyn t
  | .refine t _ => μSyn t
  | .legacy t _ => μSyn t
  | .nullable _ => none
  | .lazy _ => none
  | .custom _ _ => none
  | .opaq _ => none
  | .object _ _ _ => some .M
  | .union opts => unanimous (μSynList opts)
  | .dunion _ _ => some .M

def μSynList : List Term → List (Option Member)
  | [] => []
  | t :: ts => μSyn t :: μSynList ts

end

/-- A field's semantics through a given denotation — named so proofs can speak of it. -/
def fieldSemOf (den : Term → Codec) : Field → FieldSem
  | .req t => .req (den t)
  | .optional t => .opt (den t)
  | .fallback t v => .fb (den t) v

/-- A rest policy's semantics through a given denotation. -/
def restSemOf (den : Term → Codec) : Rest → RestSem
  | .drop => .drop
  | .refuse => .refuse
  | .codec t => .codec (den t)

def denote : Nat → Term → Codec
  | 0, t =>
    -- Dead at fuel 0, but the member index is syntactic, not fueled: `μSyn` keeps the
    -- `⇝` column truthful at every depth.
    { T := fun _ => False, μ := μSyn t, e := fun _ => none, p := fun _ => none }
  | fuel+1, t =>
    match t with
    | .string => stringCodec
    | .number => numberCodec
    | .decimal => decimalCodec
    | .boolean => booleanCodec
    | .null => nullCodec
    | .binary => binaryCodec
    | .literal v => literalCodec v
    | .literalS ls => literalSCodec ls
    | .literalN ls => literalNCodec ls
    | .set elem => setCodec (denote fuel elem)
    | .array elem => arrayCodec (denote fuel elem)
    | .tuple elems tail =>
        tupleCodec (elems.map (denote fuel)) (tail.map (denote fuel))
    | .record val => recordCodec (denote fuel val)
    | .held inner f g => (denote fuel inner).through f g
    | .refine inner q => (denote fuel inner).restrict q
    | .legacy inner r => (denote fuel inner).extendRead r
    | .nullable inner => (denote fuel inner).withNull
    | .lazy inner =>
        -- `(lazy)` concludes `⊤`: the pair is the thunk's, the member is not.
        { denote fuel inner with μ := none }
    | .custom ce cp =>
        { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp }
    -- Fuel-free: `opaqCodecω` budgets each input by its own depth (Opaque.lean).
    | .opaq lossy => opaqCodecω lossy
    | .object fields f rest =>
        objectCodec ⟨fields, fun k => fieldSemOf (denote fuel) (f k)⟩
          (restSemOf (denote fuel) rest)
    | .union opts =>
        altCodec (opts.map fun t' => optionSemOf (denote fuel t') (specOf t'))
          (unanimous (opts.map fun t' => (denote fuel t').μ))
    | .dunion d opts =>
        dunionCodec d (opts.map fun t' => (tagsOf d t', denote fuel t'))

end

end Calculus
