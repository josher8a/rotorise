import Calculus.Dynamo.Lang.Term
import Calculus.Lang.Typing
import Calculus.Dynamo.Alg.Frontier
import Calculus.Dynamo.Alg.Opaque

variable {α : Calculus.Table}

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

/-- The member a term stores, syntactically: the generic `⇝` index at DynamoDB. -/
abbrev μSyn (t : Term) : Option Member := Alg.μSyn t

/-- The members of a list of terms, in order. -/
abbrev μSynList (ts : List Term) : List (Option Member) := Alg.μSynList ts

section Rows
variable (k : GroundKind) (t : Term) (ts : List Term)

@[μSyn_rows] theorem μSyn_base : μSyn (.base k) = some k.member := rfl
@[μSyn_rows] theorem μSyn_literal (x : k.Carrier) : μSyn (.literal k x) = some k.member := rfl
/-- The member is `setMember` of the element's: `none` where the element names no member of
    `S`, `N` or `B`, which is the case the DynamoDB obligation `SetElem` refuses. -/
@[μSyn_rows] theorem μSyn_set : μSyn (.set t) = (μSyn t).bind setMember := rfl
@[μSyn_rows] theorem μSyn_list (pre suf : List Term) (sp : Option Term) :
    μSyn (.list pre sp suf) = some .L := rfl
@[μSyn_rows] theorem μSyn_held (P : Term) (k : Word) :
    μSyn (.held t P k) = μSyn t := rfl
@[μSyn_rows] theorem μSyn_refine (p : Pred) : μSyn (.refine t p) = μSyn t := rfl
@[μSyn_rows] theorem μSyn_opaq : μSyn .opaq = none := rfl
/-- A closed term reads an unbound variable as the bottom, and a recursive term concludes `⊤`. -/
@[μSyn_rows] theorem μSyn_var (i : Nat) : μSyn (.var i) = none := rfl
@[μSyn_rows] theorem μSyn_mu : μSyn (.mu t) = none := rfl
@[μSyn_rows] theorem μSyn_object (b : Body) : μSyn (.object b) = some .M := rfl
@[μSyn_rows] theorem μSyn_union : μSyn (.union ts) = unanimous (μSynList ts) := rfl
/-- The bottom writes no value, so there is no member it stores. -/
@[μSyn_rows] theorem μSyn_never : μSyn .never = none := rfl
@[μSyn_rows] theorem μSynList_nil : μSynList [] = [] := rfl
@[μSyn_rows] theorem μSynList_cons : μSynList (t :: ts) = μSyn t :: μSynList ts := rfl

end Rows

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

export Alg (envAt)

variable (α) in
/-- Each term, at its certified combinator: the generic denotation at DynamoDB. -/
abbrev denote (t : Term) (ρ : List Codec := []) : Codec := Alg.denote α t ρ

variable (α) in
/-- The payload's semantics: the slot table and the open block, each through its own
    companion. The recursion has to be passed *applied*, so `denote`'s `.object` row delegates
    to this companion, alongside `fieldSem` and `wildSem`. -/
abbrev bodySem (b : Body) (ρ : List Codec := []) : Codec := Alg.bodySem α b ρ

variable (α) in
/-- A field's semantics. A companion of `denote` rather than a function of one, which is what
    removed the fuel. -/
abbrev fieldSem (s : ObjectSlot) (ρ : List Codec := []) : FieldSem := Alg.fieldSem α s ρ

variable (α) in
/-- The open block's semantics. **A body with no open block refuses**: a name the body does not
    claim is a name the body refuses, in both directions. -/
abbrev wildSem (w : Option Term) (ρ : List Codec := []) : RestSem := Alg.wildSem α w ρ

variable (α) in
/-- The options' codecs, in order. -/
abbrev denoteList (ts : List Term) (ρ : List Codec := []) : List Codec := Alg.denoteList α ts ρ

variable (α) in
/-- The spread's codec, where there is one. -/
abbrev denoteOpt (o : Option Term) (ρ : List Codec := []) : Option Codec := Alg.denoteOpt α o ρ

variable (α) in
/-- The options' members, in order. -/
abbrev denoteμs (ts : List Term) (ρ : List Codec := []) : List (Option Member) :=
  Alg.denoteμs α ts ρ

/-! ### The rows at the DynamoDB constructors

Each row is `rfl`: the generic row at `dynSem` is the DynamoDB combinator. `§6`'s **Hold** rows
are stated about combinators and its **Do not hold** rows (`Refutations.lean`) about terms, and
these rows are the translation between the two. -/

section Rows
variable (t : Term) (ts : List Term) (ρ : List Codec)

@[denote_rows] theorem denote_base (k : GroundKind) : denote α (.base k) ρ = baseCodec k := rfl
@[denote_rows] theorem denote_literal (k : GroundKind) (x : k.Carrier) :
    denote α (.literal k x) ρ = literalCodec k x := rfl
/-- `set` denotes the finite-powerset lift of its element's codec. -/
@[denote_rows] theorem denote_set : denote α (.set t) ρ = setCodec (denote α t ρ) := rfl
/-- The container denotes the `list` codec over its three parts. -/
@[denote_rows] theorem denote_list (pre : List Term) (spread : Option Term) (suf : List Term) :
    denote α (.list pre spread suf) ρ
      = listCodec (denoteList α pre ρ) (denoteOpt α spread ρ) (denoteList α suf ρ) := rfl
/-- `held` denotes `through`, restricted by the admission of the caller-side term. -/
@[denote_rows] theorem denote_held (P : Term) (k : Word) :
    denote α (.held t P k) ρ
      = ((denote α t ρ).through (α.word k).1 (α.word k).2).restrict
          fun v => ((denote α P ρ).e v).isSome := rfl
/-- `refine` denotes `restrict`, of the predicate's meaning. This is the whole of what `Pred`
    cost the codec layer: one `.eval`. -/
@[denote_rows] theorem denote_refine (p : Pred) :
    denote α (.refine t p) ρ = (denote α t ρ).restrict p.eval := rfl
/-- `opaque` denotes the recursive codec of its body `opaqStep` (`Opaque.lean`). -/
@[denote_rows] theorem denote_opaq : denote α .opaq ρ = muCodec opaqStep := rfl
/-- `object` denotes its payload's semantics. -/
@[denote_rows] theorem denote_object (b : Body) : denote α (.object b) ρ = bodySem α b ρ := rfl
/-- `union` denotes `altCodec`, over the options' semantics and their unanimous member. -/
@[denote_rows] theorem denote_union_sems :
    denote α (.union ts) ρ = altCodec (denoteList α ts ρ) (unanimous (denoteμs α ts ρ)) := rfl
/-- §2's degenerate codec is the bottom exactly: empty domains, and the laws hold vacuously. -/
@[denote_rows] theorem denote_never : denote α .never ρ = Codec.empty := rfl
@[denote_rows] theorem denote_var (i : Nat) : denote α (.var i) ρ = envAt ρ i := rfl
/-- `mu` denotes the recursive codec of its body: each input reads the stage of the body that
    its own depth names. -/
@[denote_rows] theorem denote_mu : denote α (.mu t) ρ = muCodec fun c => denote α t (c :: ρ) := rfl
@[denote_rows] theorem bodySem_mk (fields : Finset Name) (f : {k // k ∈ fields} → ObjectSlot)
    (wild : Option Term) : bodySem α (.mk fields f wild) ρ
      = objectCodec ⟨fields, fun k => fieldSem α (f k) ρ⟩ (wildSem α wild ρ) := rfl
@[denote_rows] theorem fieldSem_req : fieldSem α (.req t) ρ = .req (denote α t ρ) := rfl
@[denote_rows] theorem fieldSem_optional : fieldSem α (.optional t) ρ = .opt (denote α t ρ) := rfl
@[denote_rows] theorem wildSem_none : wildSem α none ρ = .refuse := rfl
@[denote_rows] theorem wildSem_some : wildSem α (some t) ρ = .codec (denote α t ρ) := rfl
@[denote_rows] theorem denoteList_nil : denoteList α [] ρ = [] := rfl
@[denote_rows] theorem denoteList_cons : denoteList α (t :: ts) ρ = denote α t ρ :: denoteList α ts ρ :=
  rfl
@[denote_rows] theorem denoteOpt_none : denoteOpt α none ρ = none := rfl
@[denote_rows] theorem denoteOpt_some : denoteOpt α (some t) ρ = some (denote α t ρ) := rfl
@[denote_rows] theorem denoteμs_nil : denoteμs α [] ρ = [] := rfl
@[denote_rows] theorem denoteμs_cons : denoteμs α (t :: ts) ρ = (denote α t ρ).μ :: denoteμs α ts ρ :=
  rfl

end Rows

/-! ## The member index

Was "fuel-free" as a *claim about a fueled denotation*; now it is a fact about a structural one,
and the proof is a plain induction on the term. `termination_by fuel _ => (fuel, 0)` and its
companion's `(fuel, opts.length + 1)` are gone with the parameter. -/

/-- Whatever the payload, an object writes a map. The companion `denote_μ`'s `.object` row
    needs: with the payload inlined the row was `rfl`, and with a `Body` variable in hand there
    is nothing to reduce until the payload is matched — so the match happens once, here. -/
theorem bodySem_μ : ∀ b : Body, (bodySem α b).μ = some .M
  | .mk _ _ _ => rfl

mutual

theorem denote_μ : ∀ t : Term, (denote α t).μ = μSyn t
  | .literal k ls => literalCodec_μ k ls
  | .base k => by cases k <;> rfl
  | .set t => by show (denote α t).μ.bind setMember = _; rw [denote_μ t]; rfl
  | .list _ _ _ => rfl
  | .held t' _ _ => denote_μ t'
  | .refine t' _ => denote_μ t'
  | .opaq | .never | .var _ | .mu _ => rfl
  | .object b => bodySem_μ b
  | .union opts => by
      show unanimous (denoteμs α opts) = unanimous (μSynList opts)
      rw [denoteμs_eq opts]

/-- The union options' members, per option. ~~μSynList_eq~~ under its old name was the same fact
    with a fuel index and a `termination_by`; both are gone. -/
theorem denoteμs_eq : ∀ opts : List Term, denoteμs α opts = μSynList opts
  | [] => rfl
  | t :: ts => by
      simp only [denote_rows, μSyn_rows]
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

variable (α) in
/-- The object field table, denoted. Was ~~denoteωF~~. -/
def fieldTable (fields : Finset Name) (f : {k // k ∈ fields} → ObjectSlot)
    (ρ : List Codec := []) : MapOf FieldSem :=
  ⟨fields, fun k => fieldSem α (f k) ρ⟩

section Bridge

/-- `array` denotes the spread-only `list`, which is what `arrayCodec` is. -/
theorem denote_array (t : Term) : denote α (.array t) = arrayCodec (denote α t) :=
  (arrayCodec_eq_listCodec (denote α t)).symm

/-- `record` denotes `recordCodec`: the empty body with an open block, which is what
    `objectCodec_empty_codec` proves the record codec to be. -/
theorem denote_record (t : Term) : denote α (.record t) = recordCodec (denote α t) :=
  objectCodec_empty_codec (denote α t)

/-- `tuple` denotes the suffix-free `list`, which is what `tupleCodec` is. -/
theorem denote_tuple (ts : List Term) (tail : Option Term) :
    denote α (.tuple ts tail) = tupleCodec (denoteList α ts) (denoteOpt α tail) :=
  (tupleCodec_eq_listCodec (denoteList α ts) (denoteOpt α tail)).symm

/-- `object` denotes `objectCodec`. -/
theorem denote_object_table (fields : Finset Name) (f : {k // k ∈ fields} → ObjectSlot)
    (wild : Option Term) {ρ : List Codec} :
    denote α (.object (.mk fields f wild)) ρ
      = objectCodec (fieldTable α fields f ρ) (wildSem α wild ρ) :=
  rfl

end Bridge

/-! ### The companions are the old mapped forms

`denote` had to name its list companions to become structural, and every proof downstream was
written against `opts.map (denote fuel)`. These four are that bridge, `@[simp]` so nothing else
has to know the companions exist. -/

@[simp] theorem denoteList_eq {ρ : List Codec} :
    ∀ ts : List Term, denoteList α ts ρ = ts.map (denote α · ρ)
  | [] => rfl
  | t :: ts => by simp only [denote_rows, List.map]; rw [denoteList_eq ts]

@[simp] theorem denoteOpt_eq {ρ : List Codec} :
    ∀ tail : Option Term, denoteOpt α tail ρ = tail.map (denote α · ρ)
  | none => rfl
  | some _ => rfl

@[simp] theorem denoteμs_eq_map {ρ : List Codec} : ∀ opts : List Term,
    denoteμs α opts ρ = opts.map fun t => (denote α t ρ).μ
  | [] => rfl
  | t :: ts => by simp only [denote_rows, List.map]; rw [denoteμs_eq_map ts]

end

end Calculus
