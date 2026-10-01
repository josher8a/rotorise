import Calculus.Lang.Term
import Calculus.Dynamo.Alg.Opaque
import Mathlib.Data.Finset.Lattice.Fold

/-!
# §3–§4 — The term language

Deep embedding. Notes:

* Predicates carried by terms (`refine`) are `Bool`-valued so the denotation
  needs no classical choice; the doc's subsets are their coercions. `Pred` below is that
  predicate **as data** where the data exists, and a function only where it does not.
* `opaque` is a Lean keyword, hence `opaq`.
* Slots (§4) are a separate inductive — the stratification is the point: no `Term`
  position accepts an `ObjectSlot`.
* An object's **payload** (§4) is a separate inductive for the same reason, one level up.
  `Body` is the key set, the slot function on it, and the open block, as one thing — so
  every table over terms has a *one-argument* `.object` row that delegates to a `Body`
  companion, the way `denote`'s row delegates to `fieldSem` and `wildSem`. Threading three
  arguments by hand through twenty tables was the only reason those three had to agree by
  convention rather than by type.
-/

/-! ## The DynamoDB rows of the generic functions

`denote`, `μSyn`, `Adm`, `AdmA` and their companions are the generic functions at `dynSyn`. A
generic equation states a row through the signature (`Mean.list`, `PrimAdm.admV`), and
`simp only [g]` delta-unfolds an abbreviation and reads no other equation. So each row at the
DynamoDB constructors is a `rfl` lemma in one of these sets, and a proof names the set. The
sets are registered here because a set is usable only in a module that imports its
registration. -/

/-- The rows of `denote`, `bodySem`, `fieldSem`, `wildSem`, `denoteList`, `denoteOpt` and
    `denoteμs` at the DynamoDB constructors. -/
register_simp_attr denote_rows
/-- The rows of `μSyn` and `μSynList` at the DynamoDB constructors. -/
register_simp_attr μSyn_rows
/-- The rows of `Adm` and its companions at the DynamoDB constructors. -/
register_simp_attr Adm_rows
/-- The rows of `AdmA`, its companions and `refineReads` at the DynamoDB constructors. -/
register_simp_attr AdmA_rows

namespace Calculus

open Alg (Term.depth Body.depth Term.depthO Term.depth_le_depthL Term.depthO_le
  Term.depth_lt_object_req Term.depth_lt_object_opt Term.depth_lt_object_rest)


/-- §3 `(refine)`'s predicate, as far as it can be read.

    A bare `Value → Bool` decides nothing a table can see, and two things wanted to see it.
    A certificate cannot compare `set(literal k ls)` with another one while the predicate is a
    function, because the meet reads a predicate only as data. And
    `src/codec/term.ts` had already made the same move for the same reason: its predicate type is
    `members | closure`, and its docstring says the declaration guard has to read the
    predicate as data. The model has `members` and `closure` and one more, `except`, which the
    host does not spell yet.

    * `members` is membership of a literal's alternatives, `inL k ls`. The base indexes the
      carrier, exactly as `Term.literal` does.
    * `closure` is a caller's function. It is the case that stays opaque, and it is why this
      is a wider type and not a narrower one: `refine` still carries an arbitrary predicate,
      and every theorem that quantifies over one still runs.
    * `except` is the complement of `members` at one base: a value of the base that is none of
      the alternatives. With it, the data cases are closed under the meet and under the
      complement at a base. A name is a string, so the same case excludes a finite set of names.

    `Pred` mentions no `Term`, so it is the universe's predicate type (`Alg.Syn.Pred`), and
    `Pred.eval` below is its meaning (`Alg.Syn.eval`). -/
inductive Pred where
  | members (k : GroundKind) (ls : NEFinset k.Carrier)
  | closure (q : Value → Bool)
  | except  (k : GroundKind) (ls : NEFinset k.Carrier)


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

/-- **What a `Pred` means.** The universe's `Alg.Syn.eval`, beside the type.

    `noncomputable`, because `inL` is. `denote` is noncomputable for the same reason, and
    the meet never calls this: the meet reads a `Pred`'s constructors, which are data.

    **`members` keeps its `Finset`, and a literal no longer has one.** A refinement predicate is
    data over a set of alternatives; a literal is one value. `inLs` is the set form, built from
    `inL` at each alternative rather than as a membership row of its own. -/
noncomputable def Pred.eval : Pred → Value → Bool
  | .members k ls => inLs k ls
  | .closure q    => q
  | .except k ls  => fun v => inBase k v && !inLs k ls v

/-- **The DynamoDB set obligation**: the element writes one member of `S`, `N` or `B`.

    A rule of the store universe, not of the set algebra: `lawful_setCodec` needs only a lawful
    element. A set writes a wire set in the first family, `SS`, `NS` or `BS`, into which every
    element writes, and writes nothing where no family holds every element. So `set` over an
    element that names no member can still write a value (`set opaque` writes an `SS` of strings),
    and `set` over an element of a non-scalar member writes nothing. The obligation asks the static
    fact a schema states: the element names one member of `S`, `N` or `B`. The other two DynamoDB set rules, the three element types and the absent
    empty set, are the carrier's (`Value.strSet`, `numSet`, `binSet`). -/
def SetElem (c : Codec) : Prop := (c.μ.bind setMember).isSome = true

/-! ## The DynamoDB signature

The term language is `Alg.Term` at `dynSyn`, and `dynSem` is its meaning. Each field of the signature is a declaration that
this development already proves: the ground codecs, the list and map prisms, the set lift and
`opaque`. -/

/-- The primitives of DynamoDB: a ground base, or one alternative at a base. -/
inductive Ground where
  /-- §3's ground bases: the base is an index, as `literal`'s is. -/
  | base (k : GroundKind)
  /-- §3 `(literal)`: a ground **base**, and one inhabitant of that base's carrier.

      This was three constructors — arity-one over a value, and ~~literalS~~/~~literalN~~ at the
      two commonest bases — because no single payload type could say "this alternative, at this
      base". `(k : GroundKind)` with `v : k.Carrier` says it: the base is an index, so
      `g ground` is unsayable-otherwise and the member is a function rather than an index with a
      premise, and `ℓ ⊆ T` is the carrier. `.null`'s carrier is `Unit`, so `literal .null` can
      say nothing but what it means.

      **One value, and several values are a `union`.** A set of alternatives is a certified
      union of singletons: the members are pairwise separated because the values differ.
      `Calculus/Dynamo/Witness/LiteralArity1.lean` derives that rule. -/
  | literal (k : GroundKind) (v : k.Carrier)

/-- The codec of each primitive. -/
@[simp] noncomputable def groundCodec : Ground → Codec
  | .base k => baseCodec k
  | .literal k v => literalCodec k v

/-- Each primitive is lawful. -/
theorem lawful_groundCodec : ∀ g, Lawful (groundCodec g)
  | .base k => lawful_baseCodec k
  | .literal k v => lawful_literalCodec k v

/-! ### The held sets that the signature names -/

/-- `℘⁺fin(T)` — the nonempty finite subsets of `T` (§3 `(set)`). -/
def HSet (T : Value → Prop) : Value → Prop := fun v =>
  (∃ S : NEFinset String, v = .strSet S ∧ ∀ s ∈ S.1, T (.str s)) ∨
  (∃ S : NEFinset WFNumeral, v = .numSet S ∧ ∀ d ∈ S.1, T (.num d)) ∨
  (∃ S : NEFinset Bytes,  v = .binSet S ∧ ∀ b ∈ S.1, T (.bin b))

/-- The list former: the `L` prism. -/
abbrev dList : Alg.ListA Value Member Attr.member Attr.depth where
  p := lA
  μ := .L
  hμ _ := rfl
  d_lt _ _ hx := Nat.succ_le_succ (Attr.depth_le_depthL hx)

/-- The map former: the `M` prism. -/
abbrev dMap : Alg.MapA Value Member Attr.member Attr.depth where
  m := mA
  μ := .M
  hμ _ := rfl
  d_lt m k := Attr.depth_map_entry (f := m.2) k

/-- **Two element codecs that agree at an orientation move a set to one image.** -/
theorem setAt_agree {α : Type} {o : Alg.Orient} {c d : Codec} {inj : α → Attr} {S : NEFinset α}
    {a b : Attr} (h : Alg.Agree o c d) (ha : setAt o c inj S = some a)
    (hb : setAt o d inj S = some b) : a = b :=
  Option.some.inj <| (ha.symm.trans (setAt_congr fun x hx => by
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (setAt_elem ha x hx)
    obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp (setAt_elem hb x hx)
    rw [hu, hu', h _ _ _ hu hu'])).trans hb

/-- The set former: the lift, with the store's set rule as the element's obligation. -/
noncomputable abbrev dSet : Alg.SetF Value Member Attr.member Attr.depth where
  lift := setCodec
  lawful h := lawful_setCodec h
  agree h := agreeLe_setCodec h
  agreeS {side c d} h := by
    cases side
    · intro a t w ht hw
      cases a <;> first | exact setAt_agree h ht hw | exact nomatch ht
    · intro v a b ha hb
      cases v <;> first | exact setAt_agree h ha hb | exact nomatch ha
  elem := SetElem
  held := HSet
  member := setMember
  lift_μ _ := rfl
  carrier h := carrier_setCodec h
  held_of {c T} ih v hv := by
    cases v <;> first
      | exact Or.inl ⟨_, rfl, fun x hx => ih _ (hv x hx)⟩
      | exact Or.inr (Or.inl ⟨_, rfl, fun x hx => ih _ (hv x hx)⟩)
      | exact Or.inr (Or.inr ⟨_, rfl, fun x hx => ih _ (hv x hx)⟩)
      | exact nomatch hv

/-- **The generators of the DynamoDB adapters.** `decimalText` is the text adapter that the
    library ships as `decimal`. `caller n` is the `n`th adapter that a caller supplies, and a
    vector quantifies its two functions through the table. -/
inductive DynGen where
  | decimalText
  | caller (n : Nat)
  deriving DecidableEq

/-- The predicates of DynamoDB at each absolute side: the caller side reads a data predicate, and
    the store names no predicate but the truth. -/
abbrev dynP : Bool → Type
  | false => Pred
  | true => Unit

/-- The generators of DynamoDB at each absolute side: the store names no generator, so a `held`
    at the side `true` has no representation. -/
abbrev dynG : Bool → Type
  | false => DynGen
  | true => Empty

/-- **The DynamoDB signature**: the ground primitives, the data predicates, and the generators of
    the adapters. -/
abbrev dynSig : Alg.Sig where
  Ground := Ground
  P := dynP
  G := dynG
  decG
    | false => inferInstanceAs (DecidableEq DynGen)
    | true => inferInstanceAs (DecidableEq Empty)

/-- **The DynamoDB syntax**: the signature at the host orientation. -/
abbrev dynSyn : Alg.Syn := ⟨dynSig, .host⟩

/-- **The DynamoDB meaning** of that signature. -/
@[reducible] noncomputable instance dynSem : Alg.Mean dynSig where
  V := Value
  Mem := Member
  mem := Attr.member
  decM := inferInstance
  ground := groundCodec
  lawful_ground := lawful_groundCodec
  carrier_ground
    | .base k => carrier_baseCodec k
    | .literal k v => carrier_literalCodec k v
  eval
    | false => Pred.eval
    | true => fun _ _ => true
  truth
    | false => .closure fun _ => true
    | true => ()
  eval_truth
    | false, _ => rfl
    | true, _ => rfl
  d := Attr.depth
  d_pos := Attr.depth_pos
  list := some dList
  map := some dMap
  set := some dSet

/-- **The one stored table of DynamoDB**: the store names no generator. -/
def dynTableA : Alg.Table dynSyn.op := fun g => nomatch g

/-! ## The term language at DynamoDB

Each constructor keeps its spelling, as a `match_pattern` abbreviation: a pattern `.list pre sp
suf` or `.string` matches as it did. -/

/-- The term language of DynamoDB. -/
abbrev Term := Alg.Term dynSyn
/-- A table of the DynamoDB adapters: the two functions of each generator. -/
abbrev Table := Alg.Table dynSyn
/-- An adapter word of DynamoDB. -/
abbrev Word := Alg.Word dynSyn
/-- An object payload of DynamoDB. -/
abbrev Body := Alg.Body dynSyn
/-- An object slot of DynamoDB. -/
abbrev ObjectSlot := Alg.ObjectSlot dynSyn

@[match_pattern] abbrev Term.base (k : GroundKind) : Term := Alg.Term.prim (.base k)
@[match_pattern] abbrev Term.literal (k : GroundKind) (v : k.Carrier) : Term :=
  Alg.Term.prim (.literal k v)
@[match_pattern] abbrev Term.set (elem : Term) : Term := Alg.Term.set elem
@[match_pattern] abbrev Term.list (pre : List Term) (spread : Option Term) (suf : List Term) :
    Term := Alg.Term.list pre spread suf
@[match_pattern] abbrev Term.held (s : Bool) (inner outer : Term) (k₀ : dynSig.G s × Bool)
    (k : List (dynSig.G s × Bool)) : Term :=
  Alg.Term.held s inner outer k₀ k
@[match_pattern] abbrev Term.refine (inner : Term) (p : Pred) (pA : dynSyn.PredA) :
    Term := Alg.Term.refine inner p pA
@[match_pattern] abbrev Term.opaq : Term := Alg.Term.opaq
@[match_pattern] abbrev Term.object (b : Body) : Term := Alg.Term.object b
@[match_pattern] abbrev Term.union (options : List Term) : Term := Alg.Term.union options
@[match_pattern] abbrev Term.never : Term := Alg.Term.never
@[match_pattern] abbrev Term.var (i : Nat) : Term := Alg.Term.var i
@[match_pattern] abbrev Term.mu (body : Term) : Term := Alg.Term.mu body
@[match_pattern] abbrev Body.mk (fields : Finset Name) (f : {k // k ∈ fields} → ObjectSlot)
    (wild : Option Term) : Body := Alg.Body.mk fields f wild
@[match_pattern] abbrev ObjectSlot.req (t : Term) : ObjectSlot := Alg.ObjectSlot.req t
@[match_pattern] abbrev ObjectSlot.optional (t : Term) : ObjectSlot := Alg.ObjectSlot.optional t

/-- **Case analysis on a DynamoDB term**, with the primitive split into its two rows, and each
    field at its DynamoDB type. `cases` uses this eliminator for every `Term`, so a case reads
    `base k` and `literal k v`, and a field reads the DynamoDB tables by field notation. A `held`
    has one case, at the side `false`: the side `true` names no generator. -/
@[elab_as_elim, cases_eliminator]
def Term.casesD {motive : Term → Sort _} (base : ∀ k, motive (.base k))
    (literal : ∀ k v, motive (.literal k v)) (set : ∀ elem, motive (.set elem))
    (list : ∀ pre spread suf, motive (.list pre spread suf))
    (held : ∀ inner outer k₀ k, motive (.held false inner outer k₀ k))
    (refine : ∀ inner p pA, motive (.refine inner p pA)) (opaq : motive .opaq)
    (object : ∀ b, motive (.object b)) (union : ∀ options, motive (.union options))
    (never : motive .never) (var : ∀ i, motive (.var i)) (mu : ∀ body, motive (.mu body)) :
    (t : Term) → motive t
  | .base k => base k
  | .literal k v => literal k v
  | .set e => set e
  | .list pre sp suf => list pre sp suf
  | .held false i o k₀ k => held i o k₀ k
  | .held true _ _ k₀ _ => nomatch k₀.1
  | .refine i p pA => refine i p pA
  | .opaq => opaq
  | .object b => object b
  | .union os => union os
  | .never => never
  | .var i => var i
  | .mu b => mu b

/-- Case analysis on a DynamoDB payload, at the DynamoDB types. -/
@[elab_as_elim, cases_eliminator]
def Body.casesD {motive : Body → Sort _}
    (mk : ∀ fields (f : {k // k ∈ fields} → ObjectSlot) wild, motive (Body.mk fields f wild)) :
    (b : Body) → motive b
  | .mk fields f wild => mk fields f wild

/-- Case analysis on a DynamoDB slot, at the DynamoDB types. -/
@[elab_as_elim, cases_eliminator]
def ObjectSlot.casesD {motive : ObjectSlot → Sort _} (req : ∀ t, motive (ObjectSlot.req t))
    (optional : ∀ t, motive (ObjectSlot.optional t)) : (s : ObjectSlot) → motive s
  | .req t => req t
  | .optional t => optional t

/-- The five bases by name. A pattern `.string` still matches, as `.base .string`. -/
@[match_pattern] abbrev Term.string : Term := .base .string
@[match_pattern] abbrev Term.number : Term := .base .number
@[match_pattern] abbrev Term.boolean : Term := .base .boolean
@[match_pattern] abbrev Term.binary : Term := .base .binary
/-- §3 `(null)`: the `NULL` point, so a schema can say "this attribute is exactly NULL". -/
@[match_pattern] abbrev Term.null : Term := .base .null

/-- A required slot is required on both sides of the current schema. -/
theorem req_presence :
    (.req .string : ObjectSlot).presence = (true, false) := by decide

/-- A bottom required slot admits neither presence nor absence. -/
theorem req_never_presence :
    (.req .never : ObjectSlot).presence = (false, false) := by decide

/-! ## `array` and `tuple`, as builders over `list`

`Term.list` replaced three constructors, and these two keep the words that name the shapes
a caller writes. They are definitions, so a *statement* about `.array c` reads as it always
did, while a *match* goes through `.list`. -/

/-- §3 `(array)`: every position under one codec, and no fixed position. -/
def Term.array (elem : Term) : Term := .list [] (some elem) []

/-- §3 `(tuple)` and `(tuple-tail)` in one builder: the declared positions, then the tail
    codec where there is one. `tail = none` is the plain tuple, whose arity is exactly the
    number of declared positions. -/
def Term.tuple (elems : List Term) (tail : Option Term) : Term := .list elems tail []

/-- §4 `(record)`: the object that declares no name and takes every key at one codec. It stopped
    being a constructor when the open block became a block like any other, and its codec
    `recordCodec` is the object codec of this body by definition. -/
def Term.record (val : Term) : Term :=
  .object (.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some val))

/-- An **open object**: one that carries the open block, so a name it does not declare is held
    rather than refused.

    §5's closed-option dischargers exclude exactly these, and they used to say so with three
    quantifiers and a disequality — `∀ fields ff tr, t ≠ .object fields ff (.codec tr)` — at
    seven statements. The payload is one thing now, so the exclusion is one decidable
    question about it. `isOpenObject_eq_false` below is the form the disequality had. -/
def Term.isOpenObject : Term → Bool
  | .object b => b.wild.isSome
  | _ => false

/-- The old spelling of the premise, so a reader can see the two say the same thing. -/
theorem Term.isOpenObject_eq_false {t : Term} :
    t.isOpenObject = false ↔ ∀ b, t = .object b → b.wild = none := by
  constructor
  · intro h b hb
    subst hb
    cases hw : b.wild with
    | none => rfl
    | some w => simp only [Term.isOpenObject, hw, Option.isSome] at h; exact absurd h (by simp)
  · intro h
    cases t with
    | object b => simp only [Term.isOpenObject, h b rfl, Option.isSome]
    | _ => rfl



end Calculus
