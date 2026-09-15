import Calculus.Term
import Calculus.Frontier
import Calculus.Opaque

/-!
# Denotation

`denote t` dispatches each term to its certified combinator, and the
recursion is **structural** — `Term.lazy` carries a plain `Term`, so there is nothing to
stage.

This paragraph described `denote fuel t` and said "fuel is primary: every recursive call
decrements it". That was the shape until the ω-layer was deleted and `denote` lost its fuel,
which is the change that also retired ~~denoteω~~ as a name for `denote`. What survived the
deletion is the fact the fuel was never needed for: `μ := μSyn t` is a *function of the
term*, which is the content of `denote_μ` and the reason the `⇝` column stays truthful.

Why it need not stage is `Continuity.lean`'s subject: a union resolved by *unique* admission
is anti-monotone, so a genuinely recursive union has no fixpoint semantics under that rule —
there is no recursion to approximate, so no approximation to be non-monotone. Laws are in
Soundness.lean.
-/

namespace Calculus

noncomputable section

/-- The payload's field table as a `MapOf` — the shape `MapOf.at` reads. `MapOf Field` is
    what `Body` would *be* if a `mutual` block could nest an inductive through a structure
    whose field is a function into the type being defined; it cannot, so this is the coercion.
    -/
def Body.map (b : Body) : MapOf Field := ⟨b.fields, b.at⟩

/-- The alternatives a field pins its name to, where the field's term is a literal.

    Every field form and not `req` only, because the test this feeds is present-only: a name
    an object does not carry is settled by `keysOk` and never reaches `literalsOk`, so an
    `optional` literal constrains exactly the values that do carry the name. -/
def altsOfField : Field → Option Alts
  | .req (.literal k ls) => some ⟨k, ls⟩
  | .optional (.literal k ls) => some ⟨k, ls⟩
  | .fallback (.literal k ls) _ => some ⟨k, ls⟩
  | _ => none

/-- A body's name spec: what admission reads off each declared name. The payload's own
    function, so `specOf` is a dispatch and nothing more. -/
def Body.spec : Body → MapOf NameSpec
  | .mk fields f _ =>
      ⟨fields, fun k =>
        ⟨(match f k with | .optional _ => false | _ => true), altsOfField (f k)⟩⟩

/-- The name spec of an object option — `none` for non-objects. -/
def specOf : Term → Option (MapOf NameSpec)
  | .object b => some b.spec
  | _ => none

/-! ### Where ~~literalMember~~ went

`(literal)`'s member is its base's — `literalCodec` and `GroundKind.member` agree case for case,
which is `Prisms.literalCodec_μ`, stated where the codec is.

The `Option` in `Codec.μ` is `Codec.μ`'s own — a codec that writes no attribute — and never
"this payload had no base", the member being a function of the index. -/

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
  -- the member is the base's, where it was `setMember` of the element's and could be `none`
  | .set b => some b.member
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
  | .object _ => some .M
  | .union opts => unanimous (μSynList opts)
  -- the bottom writes no value, so there is no member it stores
  | .never => none

def μSynList : List Term → List (Option Member)
  | [] => []
  | t :: ts => μSyn t :: μSynList ts

end

/-! ## The denotation

**Structural, and there is no fuel.** `denote` used to take a `Nat` budget, with a dead
`fuel = 0` codec at the bottom and a whole ω-layer (~~Denoteω~~, ~~Soundnessω~~, `Continuity`) to
recover the fuel-free reading. None of that was forced by the term language:

* the recursion under `List.map` — `elems.map (denote fuel)` — needs a **list companion**, which
  is exactly what `μSyn`/`μSynList` above already do;
* `fieldSemOf (denote fuel) (f k)` passed the recursion **unapplied**, as a function value, which
  structural recursion cannot do. But ~~fieldSemOf~~ applied its argument to *precisely the
  subterm* in every row, so it inverts: it becomes a mutual companion and the higher-order
  argument disappears.

The `Finset`-plus-function field table is *not* an obstruction — structural recursion goes
straight through `f k`, as `Value.depth` in `Opaque.lean` has always done. `sizeOf` cannot see
into a function, but `sizeOf` is only the measure once something forces well-founded recursion,
and nothing here does.

Fuel was a termination device and never a cost measure; it is not even that any more. -/

/-- **What a `Pred` means.** The type is in `Term.lean`, and the meaning is here, because `inL`
    is in `Prisms.lean` and `liftQ` in `Products.lean`, and `Term.lean` imports neither.

    `noncomputable`, because `inL` is: the numeric base's carrier gate reaches `numericHost`.
    That costs nothing new. `denote` is noncomputable for the same reason, and `Orth` never
    calls this — a classifier reads a `Pred`'s constructors, which are data. -/
noncomputable def Pred.eval : Pred → Value → Bool
  | .members k ls => inL k ls
  | .each p       => liftQ p.eval
  | .closure q    => q

mutual

def denote : Term → Codec
  | .string => stringCodec
  | .number => numberCodec
  | .decimal => decimalCodec
  | .boolean => booleanCodec
  | .null => nullCodec
  | .binary => binaryCodec
  | .literal k ls => literalCodec k ls
  | .set b => setCodec b.elem
  | .array elem => arrayCodec (denote elem)
  | .tuple elems tail => tupleCodec (denoteList elems) (denoteOpt tail)
  | .record val => recordCodec (denote val)
  | .held inner f g => (denote inner).through f g
  | .refine inner p => (denote inner).restrict p.eval
  | .legacy inner r => (denote inner).extendRead r
  | .nullable inner => (denote inner).withNull
  -- `(lazy)` concludes `⊤`: the pair is the thunk's, the member is not.
  | .lazy inner => { denote inner with μ := none }
  | .custom ce cp => { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp }
  -- `opaqCodecω` budgets each input by its own depth (`Opaque.lean`); that is a recursion on the
  -- *input*, not on the term, and is untouched by this.
  | .opaq lossy => opaqCodecω lossy
  | .object b => bodySem b
  | .union opts => altCodec (optionSems opts) (unanimous (denoteμs opts))
  -- §2's degenerate codec is the bottom exactly: empty domains, and the laws hold vacuously
  | .never => Codec.empty

/-- The payload's semantics: the field table and the rest policy, each through its own
    companion. This is the third companion of `denote`, alongside `fieldSem` and `restSem`, and
    it exists for the same reason they do — the recursion has to be passed *applied*. Before
    `Body`, `denote`'s row inlined it, which is why nothing else could name "the codec an
    object payload denotes" without repeating the pair. -/
def bodySem : Body → Codec
  | .mk fields f rest => objectCodec ⟨fields, fun k => fieldSem (f k)⟩ (restSem rest)

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

end

/-! ## The member index

Was "fuel-free" as a *claim about a fueled denotation*; now it is a fact about a structural one,
and the proof is a plain induction on the term. `termination_by fuel _ => (fuel, 0)` and its
companion's `(fuel, opts.length + 1)` are gone with the parameter. -/

/-- Whatever the payload, an object writes a map. The companion `denote_μ`'s `.object` row
    needs: with the payload inlined the row was `rfl`, and with a `Body` variable in hand there
    is nothing to reduce until the payload is matched — so the match happens once, here. -/
theorem bodySem_μ : ∀ b : Body, (bodySem b).μ = some .M
  | .mk _ _ _ => rfl

mutual

theorem denote_μ : ∀ t : Term, (denote t).μ = μSyn t
  | .literal k ls => literalCodec_μ k ls
  | .string | .number | .decimal | .boolean | .binary | .null => rfl
  | .set b => SetBase.setCodec_μ b
  | .array _ | .tuple _ _ | .record _ => rfl
  | .held t' _ _ => denote_μ t'
  | .refine t' _ => denote_μ t'
  | .legacy t' _ => denote_μ t'
  | .nullable _ | .lazy _ | .custom _ _ | .opaq _ | .never => rfl
  | .object b => bodySem_μ b
  | .union opts => by
      show unanimous (denoteμs opts) = unanimous (μSynList opts)
      rw [denoteμs_eq opts]

/-- The union options' members, per option. ~~μSynList_eq~~ under its old name was the same fact
    with a fuel index and a `termination_by`; both are gone. -/
theorem denoteμs_eq : ∀ opts : List Term, denoteμs opts = μSynList opts
  | [] => rfl
  | t :: ts => by
      simp only [denoteμs, μSynList]
      rw [denote_μ t, denoteμs_eq ts]

end

/-! ### §6 at term level — the translation table, written down

Moved here from `Equations.lean` when ~~Denoteω~~ was deleted. It lived downstream because
~~denoteω~~ did; these are equations about `denote` and belong beside it.

§6's **Hold** rows are stated about *combinators*; its **Do not hold** rows
(`Refutations.lean`) are stated about *terms*. Reading a Hold row against the specification
needed an eight-entry translation, five entries of which share no substring with the term
they translate, written down nowhere.

Here it is, as `rfl` theorems — `denote` dispatches straight onto the combinator, so these
prove nothing but the correspondence. Term-level twins of each row follow at the end. -/

/-- The object field table, denoted. Was ~~denoteωF~~. -/
def fieldTable (fields : Finset Name) (f : {k // k ∈ fields} → Field) : MapOf FieldSem :=
  ⟨fields, fun k => fieldSem (f k)⟩

section Bridge

theorem denote_set (b : SetBase) : denote (.set b) = setCodec b.elem := rfl
theorem denote_array (t : Term) : denote (.array t) = arrayCodec (denote t) := rfl
theorem denote_record (t : Term) : denote (.record t) = recordCodec (denote t) := rfl

theorem denote_tuple (ts : List Term) (tail : Option Term) :
    denote (.tuple ts tail) = tupleCodec (denoteList ts) (denoteOpt tail) := rfl

/-- `held` denotes `through` — the entry that reads least like its term. -/
theorem denote_held (t : Term) (f g : Value → Value) :
    denote (.held t f g) = (denote t).through f g := rfl

/-- `refine` denotes `restrict`, of the predicate's meaning.

    This is the whole of what `Pred` cost the codec layer: one `.eval`. `restrict` still takes
    a `Value → Bool`, so every theorem about it in the combinator modules is untouched. -/
theorem denote_refine (t : Term) (p : Pred) :
    denote (.refine t p) = (denote t).restrict p.eval := rfl

/-- `legacy` denotes `extendRead`. -/
theorem denote_legacy (t : Term) (r : Attr → Option Value) :
    denote (.legacy t r) = (denote t).extendRead r := rfl

/-- `nullable` denotes `withNull` — `orNull` behind §3's guard. -/
theorem denote_nullable (t : Term) : denote (.nullable t) = (denote t).withNull := rfl

/-- `union` denotes `altCodec`, over the options' semantics and their unanimous member. -/
theorem denote_union_sems (opts : List Term) :
    denote (.union opts) =
      altCodec (optionSems opts) (unanimous (denoteμs opts)) := rfl

/-- `opaque` denotes `opaqCodecω` — the fuel-free one, which is why §5's discharger table has
    a row about `opaqCodec` at a fuel and a reason rather than a term-level twin. -/
theorem denote_opaq (lossy : Bool) : denote (.opaq lossy) = opaqCodecω lossy := rfl

/-- `object` denotes `objectCodec`. -/
theorem denote_object_table (fields : Finset Name) (f : {k // k ∈ fields} → Field)
    (rest : Rest) :
    denote (.object (.mk fields f rest)) = objectCodec (fieldTable fields f) (restSem rest) :=
  rfl

/-- …and the `Body`-level form, which is the one a statement about an arbitrary object needs. -/
theorem denote_object (b : Body) : denote (.object b) = bodySem b := rfl


end Bridge

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

end

end Calculus
