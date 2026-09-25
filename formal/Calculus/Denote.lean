import Calculus.Term
import Calculus.Frontier
import Calculus.Opaque

/-!
# Denotation

`denote t ρ` dispatches each term to its certified combinator, and the recursion is
**structural** on the term. The environment `ρ` holds the codec of each bound variable, nearest
binder first, and a closed term is denoted at `ρ = []`, which the default supplies.

`mu b` is the one row that stages: it is `muCodec` of the body `fun c => denote b (c :: ρ)`, and
`muCodec` budgets each input by its own depth, which is a recursion on the input and not on the
term. `opaque` is `muCodec opaqStep`, the same construct at a fixed body.

`μ := μSyn t` is a *function of the term* (`denote_μ`), so the `⇝` column stays truthful.
Laws are in Soundness.lean.
-/

namespace Calculus

noncomputable section

/-- The payload's field table as a `MapOf`, the shape `MapOf.at` reads. `Body.mk` takes the key
    set and the slot function as two arguments, so this is the coercion. -/
def Body.map (b : Body) : MapOf ObjectSlot := ⟨b.fields, b.at⟩

/-- The alternatives a field pins its name to, where the field's term is a literal.

    Every field form and not `req` only. The slice reads the presence beside the alternatives
    (`litSubAt`), so an `optional` literal is told apart by its presence and not by its
    alternatives. -/
def altsOfField : ObjectSlot → Option Alts
  | .req (.literal k x) => some ⟨k, x⟩
  | .optional (.literal k x) => some ⟨k, x⟩
  | _ => none

/-- A body's spec: the presence and the pinned literal of each declared name, which a slice
    reads. A slice asks each name that a clause names, so an undeclared name and the open block
    answer nothing here. The payload's own function, so `specOf` is a dispatch and nothing
    more. Admission reads no spec: every option admits by attempt, which runs `Adm`. -/
def Body.spec : Body → MapOf NameSpec
  | .mk fields f _ => ⟨fields, fun k => ⟨(f k).presence, altsOfField (f k)⟩⟩

/-- The spec of an object option — `none` for non-objects. -/
def specOf : Term → Option (MapOf NameSpec)
  | .object b => some b.spec
  | _ => none

/-! ### Where ~~literalMember~~ went

`(literal)`'s member is its base's — `literalCodec` and `GroundKind.member` agree case for case,
which is `Prisms.literalCodec_μ`, stated where the codec is.

The `Option` in `Codec.μ` is `Codec.μ`'s own — a codec that writes no attribute — and never
"this payload had no base", the member being a function of the index. -/

mutual

/-- The member a term stores, syntactically — the `⇝` index computed from the term. -/
def μSyn : Term → Option Member
  | .string => some .S
  | .literal k _ => some k.member
  | .number => some .N
  | .boolean => some .BOOL
  | .null => some .NULL
  | .binary => some .B
  -- the member is `setMember` of the element's: `none` where the element names no member of
  -- `S`, `N` or `B`, which is the case the DynamoDB obligation `SetElem` refuses
  | .set t => (μSyn t).bind setMember
  | .list _ _ _ => some .L
  | .held t _ _ _ => μSyn t
  | .refine t _ => μSyn t
  | .opaq => none
  -- a closed term reads an unbound variable as the bottom, and a recursive term concludes `⊤`
  | .var _ => none
  | .mu _ => none
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
straight through `f k`, as `Value.depth` in `Recursion.lean` does. `sizeOf` cannot see
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
    is in `Prisms.lean`, which `Term.lean` does not import.

    `noncomputable`, because `inL` is. `denote` is noncomputable for the same reason, and
    the meet never calls this: the meet reads a `Pred`'s constructors, which are data.

    **`members` keeps its `Finset`, and a literal no longer has one.** A refinement predicate is
    data over a set of alternatives; a literal is one value. `inLs` is the set form, built from
    `inL` at each alternative rather than as a membership row of its own. -/
noncomputable def Pred.eval : Pred → Value → Bool
  | .members k ls => inLs k ls
  | .closure q    => q
  | .except k ls  => fun v => inBase k v && !inLs k ls v

/-- The codec an environment gives the variable `i`: the bottom where no binder is. -/
def envAt (ρ : List Codec) (i : Nat) : Codec := ρ.getD i .empty

mutual

def denote : Term → (ρ : List Codec := []) → Codec
  | .string, _ => stringCodec
  | .number, _ => numberCodec
  | .boolean, _ => booleanCodec
  | .null, _ => nullCodec
  | .binary, _ => binaryCodec
  | .literal k ls, _ => literalCodec k ls
  | .set t, ρ => setCodec (denote t ρ)
  | .list pre spread suf, ρ =>
      listCodec (denoteList pre ρ) (denoteOpt spread ρ) (denoteList suf ρ)
  -- the caller-side restriction is a `restrict`, the combinator of the `refine` row
  | .held inner outer f g, ρ =>
      ((denote inner ρ).through f g).restrict fun v => ((denote outer ρ).e v).isSome
  | .refine inner p, ρ => (denote inner ρ).restrict p.eval
  -- `opaque` is the recursive codec of one fixed body (`Opaque.lean`)
  | .opaq, _ => muCodec opaqStep
  | .object b, ρ => bodySem b ρ
  | .union opts, ρ => altCodec (denoteList opts ρ) (unanimous (denoteμs opts ρ))
  -- §2's degenerate codec is the bottom exactly: empty domains, and the laws hold vacuously
  | .never, _ => Codec.empty
  | .var i, ρ => envAt ρ i
  -- each input reads the stage of the body that its own depth names
  | .mu b, ρ => muCodec fun c => denote b (c :: ρ)

/-- The payload's semantics: the slot table and the open block, each through its own
    companion. This is the third companion of `denote`, alongside `fieldSem` and `wildSem`, and
    it exists for the same reason they do — the recursion has to be passed *applied*. Before
    `Body`, `denote`'s row inlined it, which is why nothing else could name "the codec an
    object payload denotes" without repeating the pair. -/
def bodySem : Body → (ρ : List Codec := []) → Codec
  | .mk fields f wild, ρ => objectCodec ⟨fields, fun k => fieldSem (f k) ρ⟩ (wildSem wild ρ)

/-- A field's semantics. A companion of `denote` rather than a function of one — which is what
    removed the fuel. -/
def fieldSem : ObjectSlot → (ρ : List Codec := []) → FieldSem
  | .req t, ρ => .req (denote t ρ)
  | .optional t, ρ => .opt (denote t ρ)

/-- The open block's semantics, for the same reason.

    **A body with no open block refuses.** There is no third answer: the policy that read an
    undeclared name and wrote nothing back is gone, so a name the body does not claim is a name
    the body refuses, in both directions. -/
def wildSem : Option Term → (ρ : List Codec := []) → RestSem
  | none, _ => .refuse
  | some t, ρ => .codec (denote t ρ)

def denoteList : List Term → (ρ : List Codec := []) → List Codec
  | [], _ => []
  | t :: ts, ρ => denote t ρ :: denoteList ts ρ

def denoteOpt : Option Term → (ρ : List Codec := []) → Option Codec
  | none, _ => none
  | some t, ρ => some (denote t ρ)

def denoteμs : List Term → (ρ : List Codec := []) → List (Option Member)
  | [], _ => []
  | t :: ts, ρ => (denote t ρ).μ :: denoteμs ts ρ

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
  | .set t => by show (denote t).μ.bind setMember = _; rw [denote_μ t]; rfl
  | .list _ _ _ => rfl
  | .held t' _ _ _ => denote_μ t'
  | .refine t' _ => denote_μ t'
  | .opaq | .never | .var _ | .mu _ => rfl
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
def fieldTable (fields : Finset Name) (f : {k // k ∈ fields} → ObjectSlot)
    (ρ : List Codec := []) : MapOf FieldSem :=
  ⟨fields, fun k => fieldSem (f k) ρ⟩

section Bridge

/-- `set` denotes the finite-powerset lift of its element's codec. -/
theorem denote_set (t : Term) (ρ : List Codec) : denote (.set t) ρ = setCodec (denote t ρ) := rfl
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
theorem denote_list (pre : List Term) (spread : Option Term) (suf : List Term)
    {ρ : List Codec} : denote (.list pre spread suf) ρ
      = listCodec (denoteList pre ρ) (denoteOpt spread ρ) (denoteList suf ρ) := rfl

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
theorem denote_union_sems (opts : List Term) {ρ : List Codec} :
    denote (.union opts) ρ =
      altCodec (denoteList opts ρ) (unanimous (denoteμs opts ρ)) := rfl

/-- `opaque` denotes the recursive codec of its body `opaqStep`. -/
theorem denote_opaq : denote .opaq = muCodec opaqStep := rfl

/-- `mu` denotes the recursive codec of its body, with the stage for the bound variable. -/
theorem denote_mu (b : Term) (ρ : List Codec) :
    denote (.mu b) ρ = muCodec fun c => denote b (c :: ρ) := rfl

/-- `object` denotes `objectCodec`. -/
theorem denote_object_table (fields : Finset Name) (f : {k // k ∈ fields} → ObjectSlot)
    (wild : Option Term) {ρ : List Codec} :
    denote (.object (.mk fields f wild)) ρ
      = objectCodec (fieldTable fields f ρ) (wildSem wild ρ) :=
  rfl

/-- …and the `Body`-level form, which is the one a statement about an arbitrary object needs. -/
theorem denote_object (b : Body) : denote (.object b) = bodySem b := rfl


end Bridge

/-! ### The companions are the old mapped forms

`denote` had to name its list companions to become structural, and every proof downstream was
written against `opts.map (denote fuel)`. These four are that bridge, `@[simp]` so nothing else
has to know the companions exist. -/

@[simp] theorem denoteList_eq {ρ : List Codec} :
    ∀ ts : List Term, denoteList ts ρ = ts.map (denote · ρ)
  | [] => rfl
  | t :: ts => by simp only [denoteList, List.map]; rw [denoteList_eq ts]

@[simp] theorem denoteOpt_eq {ρ : List Codec} :
    ∀ tail : Option Term, denoteOpt tail ρ = tail.map (denote · ρ)
  | none => rfl
  | some _ => rfl

@[simp] theorem denoteμs_eq_map {ρ : List Codec} : ∀ opts : List Term,
    denoteμs opts ρ = opts.map fun t => (denote t ρ).μ
  | [] => rfl
  | t :: ts => by simp only [denoteμs, List.map]; rw [denoteμs_eq_map ts]

end

end Calculus
