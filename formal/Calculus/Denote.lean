import Calculus.Term
import Calculus.Frontier
import Calculus.Opaque

/-!
# Denotation

`denote t` dispatches each term to its certified combinator, and the
recursion is **structural** — `Term.lazy` carries a plain `Term`, so there is nothing to
stage.

`μ := μSyn t` is a *function of the term* (`denote_μ`), so the `⇝` column stays truthful.

No term is recursive, so `denote` does not stage. A recursive term needs a binder or a staged
`denote`. `altCodec` resolves by the first admitter, and first-match resolution is monotone
where the admitters agree (`Continuity.lean`). Laws are in Soundness.lean.
-/

namespace Calculus

noncomputable section

/-- The payload's field table as a `MapOf` — the shape `MapOf.at` reads. `MapOf Field` is
    what `Body` would *be* if a `mutual` block could nest an inductive through a structure
    whose field is a function into the type being defined; it cannot, so this is the coercion.
    -/
def Body.map (b : Body) : MapOf ObjectSlot := ⟨b.fields, b.at⟩

/-- The alternatives a field pins its name to, where the field's term is a literal.

    Every field form and not `req` only, because the test this feeds is present-only: a name
    an object does not carry is settled by `keysOk` and never reaches `literalsOk`, so an
    `optional` literal constrains exactly the values that do carry the name. -/
def altsOfField : ObjectSlot → Option Alts
  | .req (.literal k x) => some ⟨k, x⟩
  | .optional (.literal k x) => some ⟨k, x⟩
  | _ => none

/-- The alternatives a *term* pins, for the open block, which carries a term and no mark.
    `altsOfField`'s row for a slot, with the slot taken off. -/
def altsOfTerm : Term → Option Alts
  | .literal k x => some ⟨k, x⟩
  | _ => none

/-- A body's spec: what admission reads off each declared name, **and off the open block**.
    The payload's own function, so `specOf` is a dispatch and nothing more.

    The open block contributes `altsOfTerm` of its term, one layer in: `some (some alts)` where
    the block is a literal, `some none` where it is any other term, and `none` where the body
    has no block at all. Reading the block here is what lets `keysOk` and `litOkV` answer for
    an undeclared name without consulting `Adm`, which is `noncomputable` and is the whole
    reason admission decides by structure. -/
def Body.spec : Body → BodySpec
  | .mk fields f wild =>
      { names := ⟨fields, fun k =>
          ⟨(f k).presence, altsOfField (f k)⟩⟩
        wild := wild.map (fun w => altsOfTerm w) }

/-- The spec's name table, read off the constructor. -/
@[simp] theorem Body.spec_names_mk (fields : Finset Name)
    (f : {k // k ∈ fields} → ObjectSlot) (wild : Option Term) :
    (Body.mk fields f wild).spec.names =
      ⟨fields, fun k => ⟨(f k).presence, altsOfField (f k)⟩⟩ := rfl

/-- …and the open block, which a closed body does not have. -/
@[simp] theorem Body.spec_wild_none (fields : Finset Name)
    (f : {k // k ∈ fields} → ObjectSlot) : (Body.mk fields f none).spec.wild = none := rfl

/-- The spec has an open block exactly where the body does. `altsOfTerm` reads what the
    block pins, never whether there is one, so the two questions stay separate. -/
@[simp] theorem Body.spec_wild_isNone (b : Body) : b.spec.wild.isNone = b.wild.isNone := by
  cases b with | mk _ _ w => cases w <;> rfl

/-- The spec of an object option — `none` for non-objects. -/
def specOf : Term → Option BodySpec
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
  | .boolean => some .BOOL
  | .null => some .NULL
  | .binary => some .B
  -- the member is the base's, where it was `setMember` of the element's and could be `none`
  | .set b => some b.member
  | .list _ _ _ => some .L
  | .held t _ _ _ => μSyn t
  | .refine t _ => μSyn t
  | .lazy _ => none
  | .opaq => none
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

/-- **A set of alternatives, as the predicate `Pred.members` carries.** Some alternative is the
    value, which is `inL` at each.

    This is what `inL` was before a literal carried one value. It survives because a refinement
    predicate is data over a `Finset` and a literal is not: `Pred.members` is the only remaining
    set of alternatives in the language. -/
noncomputable def inLs (k : GroundKind) (ls : NEFinset k.Carrier) (v : Value) : Bool :=
  decide (∃ x ∈ ls.1, inL k x v = true)

/-- Whether a value is of one ground base. -/
def inBase : GroundKind → Value → Bool
  | .string,  .str _  => true
  | .number,  .num _  => true
  | .boolean, .bool _ => true
  | .binary,  .bin _  => true
  | .null,    .null   => true
  | _, _ => false

/-- **What a `Pred` means.** The type is in `Term.lean`, and the meaning is here, because `inL`
    is in `Prisms.lean` and `liftQ` in `Products.lean`, and `Term.lean` imports neither.

    `noncomputable`, because `inL` is. `denote` is noncomputable for the same reason, and
    the meet never calls this: the meet reads a `Pred`'s constructors, which are data.

    **`members` keeps its `Finset`, and a literal no longer has one.** A refinement predicate is
    data over a set of alternatives; a literal is one value. `inLs` is the set form, built from
    `inL` at each alternative rather than as a membership row of its own. -/
noncomputable def Pred.eval : Pred → Value → Bool
  | .members k ls => inLs k ls
  | .each p       => liftQ p.eval
  | .closure q    => q
  | .except k ls  => fun v => inBase k v && !inLs k ls v

mutual

def denote : Term → Codec
  | .string => stringCodec
  | .number => numberCodec
  | .boolean => booleanCodec
  | .null => nullCodec
  | .binary => binaryCodec
  | .literal k ls => literalCodec k ls
  | .set b => setCodec b.elem
  | .list pre spread suf => listCodec (denoteList pre) (denoteOpt spread) (denoteList suf)
  -- the caller-side restriction is a `restrict`, the combinator of the `refine` row
  | .held inner outer f g => ((denote inner).through f g).restrict fun v => ((denote outer).e v).isSome
  | .refine inner p => (denote inner).restrict p.eval
  -- `(lazy)` concludes `⊤`: the pair is the thunk's, the member is not.
  | .lazy inner => { denote inner with μ := none }
  -- `opaqCodecω` budgets each input by its own depth (`Opaque.lean`); that is a recursion on the
  -- *input*, not on the term, and is untouched by this.
  | .opaq => opaqCodecω
  | .object b => bodySem b
  | .union opts => altCodec (optionSems opts) (unanimous (denoteμs opts))
  -- §2's degenerate codec is the bottom exactly: empty domains, and the laws hold vacuously
  | .never => Codec.empty

/-- The payload's semantics: the slot table and the open block, each through its own
    companion. This is the third companion of `denote`, alongside `fieldSem` and `wildSem`, and
    it exists for the same reason they do — the recursion has to be passed *applied*. Before
    `Body`, `denote`'s row inlined it, which is why nothing else could name "the codec an
    object payload denotes" without repeating the pair. -/
def bodySem : Body → Codec
  | .mk fields f wild => objectCodec ⟨fields, fun k => fieldSem (f k)⟩ (wildSem wild)

/-- A field's semantics. A companion of `denote` rather than a function of one — which is what
    removed the fuel. -/
def fieldSem : ObjectSlot → FieldSem
  | .req t => .req (denote t)
  | .optional t => .opt (denote t)

/-- The open block's semantics, for the same reason.

    **A body with no open block refuses.** There is no third answer: the policy that read an
    undeclared name and wrote nothing back is gone, so a name the body does not claim is a name
    the body refuses, in both directions. -/
def wildSem : Option Term → RestSem
  | none => .refuse
  | some t => .codec (denote t)

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
  | .string | .number | .boolean | .binary | .null => rfl
  | .set b => SetBase.setCodec_μ b
  | .list _ _ _ => rfl
  | .held t' _ _ _ => denote_μ t'
  | .refine t' _ => denote_μ t'
  | .lazy _ | .opaq | .never => rfl
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
def fieldTable (fields : Finset Name) (f : {k // k ∈ fields} → ObjectSlot) : MapOf FieldSem :=
  ⟨fields, fun k => fieldSem (f k)⟩

section Bridge

theorem denote_set (b : SetBase) : denote (.set b) = setCodec b.elem := rfl
/-- `array` denotes the spread-only `list`, which is what `arrayCodec` is. -/
theorem denote_array (t : Term) : denote (.array t) = arrayCodec (denote t) :=
  (arrayCodec_eq_listCodec (denote t)).symm
/-- `record` denotes `recordCodec`: the empty body with an open block, which is what
    `objectCodec_empty_codec` proves the record codec to be. -/
theorem denote_record (t : Term) : denote (.record t) = recordCodec (denote t) :=
  objectCodec_empty_codec (denote t)

/-- `tuple` denotes the suffix-free `list`, which is what `tupleCodec` is. -/
theorem denote_tuple (ts : List Term) (tail : Option Term) :
    denote (.tuple ts tail) = tupleCodec (denoteList ts) (denoteOpt tail) :=
  (tupleCodec_eq_listCodec (denoteList ts) (denoteOpt tail)).symm

/-- …and the container itself denotes the `list` codec over its three parts. -/
theorem denote_list (pre : List Term) (spread : Option Term) (suf : List Term) :
    denote (.list pre spread suf)
      = listCodec (denoteList pre) (denoteOpt spread) (denoteList suf) := rfl

/-- `held` denotes `through`, restricted by the admission of the caller-side term. -/
theorem denote_held (t P : Term) (f g : Value → Value) :
    denote (.held t P f g) = ((denote t).through f g).restrict fun v => ((denote P).e v).isSome :=
  rfl

/-- `refine` denotes `restrict`, of the predicate's meaning.

    This is the whole of what `Pred` cost the codec layer: one `.eval`. `restrict` still takes
    a `Value → Bool`, so every theorem about it in the combinator modules is untouched. -/
theorem denote_refine (t : Term) (p : Pred) :
    denote (.refine t p) = (denote t).restrict p.eval := rfl


/-- `union` denotes `altCodec`, over the options' semantics and their unanimous member. -/
theorem denote_union_sems (opts : List Term) :
    denote (.union opts) =
      altCodec (optionSems opts) (unanimous (denoteμs opts)) := rfl

/-- `opaque` denotes `opaqCodecω` — the fuel-free one, which is why §5's discharger table has
    a row about `opaqCodec` at a fuel and a reason rather than a term-level twin. -/
theorem denote_opaq : denote .opaq = opaqCodecω := rfl

/-- `object` denotes `objectCodec`. -/
theorem denote_object_table (fields : Finset Name) (f : {k // k ∈ fields} → ObjectSlot)
    (wild : Option Term) :
    denote (.object (.mk fields f wild)) = objectCodec (fieldTable fields f) (wildSem wild) :=
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
