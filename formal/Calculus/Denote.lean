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
  | some (.req (.literal .string ls)) => ls.1
  | _ => ∅

def tagsOf (d : Name) : Term → Finset String
  | .object fields f _ => tagsOfField (MapOf.at ⟨fields, f⟩ d)
  | _ => ∅

/-! ### Where `literalMember` went

`(literal)`'s member is its base's — `literalCodec` and `GroundKind.member` agree case for case,
which is `Combinators.literalCodec_μ`, stated where the codec is.

`literalMember : Value → Option Member` used to sit here, and its `| _ => none` was the
`g ground` premise wearing a function's clothes. The member is a function of the index now, so
the `Option` in `Codec.μ` is only `Codec.μ`'s own — a codec that writes no attribute — and never
"this payload had no base". -/

mutual

/-- The member a term stores, syntactically — the `⇝` index computed from the term.
    Fuel-free: `lazy` concludes `⊤` (the doc's `(lazy)` rule), so the thunk is never
    forced. -/
def μSyn : Term → Option Member
  | .string => some .S
  | .literal k _ => some k.member
  | .number => some .N
  | .decimal => some .N
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

/-- A field's semantics through a given denotation — kept for the bridge lemmas below, which
    let every downstream proof keep speaking of `fieldSemOf denote`. -/
def fieldSemOf (den : Term → Codec) : Field → FieldSem
  | .req t => .req (den t)
  | .optional t => .opt (den t)
  | .fallback t v => .fb (den t) v

/-- A rest policy's semantics through a given denotation, for the same reason. -/
def restSemOf (den : Term → Codec) : Rest → RestSem
  | .drop => .drop
  | .refuse => .refuse
  | .codec t => .codec (den t)

/-! ## The denotation

**Structural, and there is no fuel.** `denote` used to take a `Nat` budget, with a dead
`fuel = 0` codec at the bottom and a whole ω-layer (`Denoteω`, `Soundnessω`, `Continuity`) to
recover the fuel-free reading. None of that was forced by the term language:

* the recursion under `List.map` — `elems.map (denote fuel)` — needs a **list companion**, which
  is exactly what `μSyn`/`μSynList` above already do;
* `fieldSemOf (denote fuel) (f k)` passed the recursion **unapplied**, as a function value, which
  structural recursion cannot do. But `fieldSemOf` applied its argument to *precisely the
  subterm* in every row, so it inverts: it becomes a mutual companion and the higher-order
  argument disappears.

The `Finset`-plus-function field table is *not* an obstruction — structural recursion goes
straight through `f k`, as `Value.depth` in `Opaque.lean` has always done. `sizeOf` cannot see
into a function, but `sizeOf` is only the measure once something forces well-founded recursion,
and nothing here does.

`codec-formalization.md` §2: *"Fuel is a termination device, not a cost measure."* It is not even
that any more. -/

mutual

def denote : Term → Codec
  | .string => stringCodec
  | .number => numberCodec
  | .decimal => decimalCodec
  | .boolean => booleanCodec
  | .null => nullCodec
  | .binary => binaryCodec
  | .literal k ls => literalCodec k ls
  | .set elem => setCodec (denote elem)
  | .array elem => arrayCodec (denote elem)
  | .tuple elems tail => tupleCodec (denoteList elems) (denoteOpt tail)
  | .record val => recordCodec (denote val)
  | .held inner f g => (denote inner).through f g
  | .refine inner q => (denote inner).restrict q
  | .legacy inner r => (denote inner).extendRead r
  | .nullable inner => (denote inner).withNull
  -- `(lazy)` concludes `⊤`: the pair is the thunk's, the member is not.
  | .lazy inner => { denote inner with μ := none }
  | .custom ce cp => { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp }
  -- `opaqCodecω` budgets each input by its own depth (`Opaque.lean`); that is a recursion on the
  -- *input*, not on the term, and is untouched by this.
  | .opaq lossy => opaqCodecω lossy
  | .object fields f rest =>
      objectCodec ⟨fields, fun k => fieldSem (f k)⟩ (restSem rest)
  | .union opts => altCodec (optionSems opts) (unanimous (denoteμs opts))
  | .dunion d opts => dunionCodec d (denoteTagged d opts)

/-- A field's semantics. A companion of `denote` rather than a function of one — which is what
    removed the fuel. -/
def fieldSem : Field → FieldSem
  | .req t => .req (denote t)
  | .optional t => .opt (denote t)
  | .fallback t v => .fb (denote t) v

/-- A rest policy's semantics, for the same reason. -/
def restSem : Rest → RestSem
  | .drop => .drop
  | .refuse => .refuse
  | .codec t => .codec (denote t)

def denoteList : List Term → List Codec
  | [] => []
  | t :: ts => denote t :: denoteList ts

def denoteOpt : Option Term → Option Codec
  | none => none
  | some t => some (denote t)

def optionSems : List Term → List OptionSem
  | [] => []
  | t :: ts => optionSemOf (denote t) (specOf t) :: optionSems ts

def denoteμs : List Term → List (Option Member)
  | [] => []
  | t :: ts => (denote t).μ :: denoteμs ts

def denoteTagged (d : Name) : List Term → List (Finset String × Codec)
  | [] => []
  | t :: ts => (tagsOf d t, denote t) :: denoteTagged d ts

end

/-! ## The member index

Was "fuel-free" as a *claim about a fueled denotation*; now it is a fact about a structural one,
and the proof is a plain induction on the term. `termination_by fuel _ => (fuel, 0)` and its
companion's `(fuel, opts.length + 1)` are gone with the parameter. -/

mutual

theorem denote_μ : ∀ t : Term, (denote t).μ = μSyn t
  | .literal k ls => literalCodec_μ k ls
  | .string | .number | .decimal | .boolean | .binary | .null => rfl
  | .set t' => by
      show (denote t').μ.bind setMember = (μSyn t').bind setMember
      rw [denote_μ t']
  | .array _ | .tuple _ _ | .record _ => rfl
  | .held t' _ _ => denote_μ t'
  | .refine t' _ => denote_μ t'
  | .legacy t' _ => denote_μ t'
  | .nullable _ | .lazy _ | .custom _ _ | .opaq _ => rfl
  | .object _ _ _ => rfl
  | .union opts => by
      show unanimous (denoteμs opts) = unanimous (μSynList opts)
      rw [denoteμs_eq opts]
  | .dunion _ _ => rfl

/-- The union options' members, per option. `μSynList_eq` under its old name was the same fact
    with a fuel index and a `termination_by`; both are gone. -/
theorem denoteμs_eq : ∀ opts : List Term, denoteμs opts = μSynList opts
  | [] => rfl
  | t :: ts => by
      simp only [denoteμs, μSynList]
      rw [denote_μ t, denoteμs_eq ts]

end

/-! ### The companions are the old mapped forms

`denote` had to name its list companions to become structural, and every proof downstream was
written against `opts.map (denote fuel)`. These four are that bridge, `@[simp]` so nothing else
has to know the companions exist. -/

@[simp] theorem denoteList_eq : ∀ ts : List Term, denoteList ts = ts.map denote
  | [] => rfl
  | t :: ts => by simp only [denoteList, List.map]; rw [denoteList_eq ts]

@[simp] theorem denoteOpt_eq : ∀ tail : Option Term, denoteOpt tail = tail.map denote
  | none => rfl
  | some _ => rfl

@[simp] theorem optionSems_eq : ∀ opts : List Term,
    optionSems opts = opts.map fun t => optionSemOf (denote t) (specOf t)
  | [] => rfl
  | t :: ts => by simp only [optionSems, List.map]; rw [optionSems_eq ts]

@[simp] theorem denoteμs_eq_map : ∀ opts : List Term,
    denoteμs opts = opts.map fun t => (denote t).μ
  | [] => rfl
  | t :: ts => by simp only [denoteμs, List.map]; rw [denoteμs_eq_map ts]

@[simp] theorem denoteTagged_eq : ∀ (d : Name) (opts : List Term),
    denoteTagged d opts = opts.map fun t => (tagsOf d t, denote t)
  | _, [] => rfl
  | d, t :: ts => by simp only [denoteTagged, List.map]; rw [denoteTagged_eq d ts]

/-! Per-constructor equations in the shape the fueled `denote` had, so downstream proofs written
against `opts.map (denote fuel)` need no change beyond dropping the argument. -/

@[simp] theorem denote_tuple (ts : List Term) (tail : Option Term) :
    denote (.tuple ts tail) = tupleCodec (ts.map denote) (tail.map denote) := by
  simp only [denote, denoteList_eq, denoteOpt_eq]

@[simp] theorem denote_union (opts : List Term) :
    denote (.union opts)
      = altCodec (opts.map fun t => optionSemOf (denote t) (specOf t))
          (unanimous (opts.map fun t => (denote t).μ)) := by
  simp only [denote, optionSems_eq, denoteμs_eq_map]

@[simp] theorem denote_dunion (d : Name) (opts : List Term) :
    denote (.dunion d opts) = dunionCodec d (opts.map fun t => (tagsOf d t, denote t)) := by
  simp only [denote, denoteTagged_eq]

theorem fieldSem_eq : fieldSem = fieldSemOf denote := by
  funext fd; cases fd <;> rfl

theorem restSem_eq : restSem = restSemOf denote := by
  funext r; cases r <;> rfl

@[simp] theorem denote_object (fields : Finset Name) (f : {k // k ∈ fields} → Field) (rest : Rest) :
    denote (.object fields f rest)
      = objectCodec ⟨fields, fun k => fieldSemOf denote (f k)⟩ (restSemOf denote rest) := by
  simp only [denote, fieldSem_eq, restSem_eq]

end

end Calculus
