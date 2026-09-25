import Calculus.AlgTerm
import Calculus.Opaque
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
    `Pred.eval` below is its meaning (`Alg.Sem.eval`). -/
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

/-- **What a `Pred` means.** The universe's `Alg.Sem.eval`, beside the type.

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
      `Calculus/LiteralArity1.lean` derives that rule. -/
  | literal (k : GroundKind) (v : k.Carrier)

/-- The codec of each primitive. -/
@[simp] noncomputable def groundCodec : Ground → Codec
  | .base k => baseCodec k
  | .literal k v => literalCodec k v

/-- Each primitive is lawful. -/
theorem lawful_groundCodec : ∀ g, Lawful (groundCodec g)
  | .base k => lawful_baseCodec k
  | .literal k v => lawful_literalCodec k v

/-- The list former: the `arr` and `L` prisms. -/
abbrev dList : Alg.ListF Value Attr Member Attr.member Value.depth Attr.depth where
  pV := arrV
  pA := lA
  μ := .L
  hμ _ := rfl
  dV_lt _ _ hx := Nat.succ_le_succ (Value.depth_le_depthL hx)
  dA_lt _ _ hx := Nat.succ_le_succ (Attr.depth_le_depthL hx)

/-- The map former: the `map` and `M` prisms. -/
abbrev dMap : Alg.MapF Value Attr Member Attr.member Value.depth Attr.depth where
  mV := mapV
  mA := mA
  μ := .M
  hμ _ := rfl
  dV_lt m k := Value.depth_map_entry (f := m.2) k
  dA_lt m k := Attr.depth_map_entry (f := m.2) k

/-- The set former: the lift, with the store's set rule as the element's obligation. -/
noncomputable abbrev dSet : Alg.SetF Value Attr Member Attr.member Value.depth Attr.depth where
  lift := setCodec
  lawful h := lawful_setCodec h
  agree h := agreeLe_setCodec h
  elem := SetElem

/-- **The DynamoDB syntax**: values, the ground primitives, and the data predicates. -/
abbrev dynSyn : Alg.Syn where
  V := Value
  Ground := Ground
  Pred := Pred

/-- **The DynamoDB meaning** of that syntax. -/
@[reducible] noncomputable instance dynSem : Alg.Sem dynSyn where
  A := Attr
  M := Member
  member := Attr.member
  decM := inferInstance
  ground := groundCodec
  lawful_ground := lawful_groundCodec
  eval := Pred.eval
  dV := Value.depth
  dA := Attr.depth
  dV_pos := Value.depth_pos
  dA_pos := Attr.depth_pos
  list := some dList
  map := some dMap
  set := some dSet
  top := Ω
  lawful_top := lawful_opaq

/-! ## The term language at DynamoDB

Each constructor keeps its spelling, as a `match_pattern` abbreviation: a pattern `.list pre sp
suf` or `.string` matches as it did. -/

/-- The term language of DynamoDB. -/
abbrev Term := Alg.Term dynSyn
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
@[match_pattern] abbrev Term.held (inner outer : Term) (f g : Value → Value) : Term :=
  Alg.Term.held inner outer f g
@[match_pattern] abbrev Term.refine (inner : Term) (p : Pred) : Term := Alg.Term.refine inner p
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
    `base k` and `literal k v`, and a field reads the DynamoDB tables by field notation. -/
@[elab_as_elim, cases_eliminator]
def Term.casesD {motive : Term → Sort _} (base : ∀ k, motive (.base k))
    (literal : ∀ k v, motive (.literal k v)) (set : ∀ elem, motive (.set elem))
    (list : ∀ pre spread suf, motive (.list pre spread suf))
    (held : ∀ inner outer f g, motive (.held inner outer f g))
    (refine : ∀ inner p, motive (.refine inner p)) (opaq : motive .opaq)
    (object : ∀ b, motive (.object b)) (union : ∀ options, motive (.union options))
    (never : motive .never) (var : ∀ i, motive (.var i)) (mu : ∀ body, motive (.mu body)) :
    (t : Term) → motive t
  | .base k => base k
  | .literal k v => literal k v
  | .set e => set e
  | .list pre sp suf => list pre sp suf
  | .held i o f g => held i o f g
  | .refine i p => refine i p
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
    being a constructor when the open block became a block like any other, and
    `objectCodec_empty_codec` is the equation that keeps the two readings one. -/
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



/-- The termination argument every `Term.depth` recursion in this development uses, written
    once. **Three** theorems share it, all in `Soundness.lean` — `soundness`,
    `typed_TSub`, `carrier_denote` — and their goal sets differ, so some alternatives are dead
    at each use. That is what the `unreachableTactic` linter reports at those sites, and it is
    why the option is disabled there rather than the block being specialised three ways.

    This said *five*, naming `Adm_sound` and `AdmA_sound` as the other two. They do not
    recurse: `Adm_exact`/`AdmA_exact` are structural mutual recursions over the term family
    with no `termination_by`, and `Adm_sound`/`AdmA_sound` are one-line corollaries of them.
    The claim was true before the exactness rewrite replaced a measured recursion with a
    structural one, and nothing was keeping it honest — `name_drift.py` checks that cited
    names *exist*, and all five do. -/
macro (name := termDepthWf) "term_depth_wf" : tactic => `(tactic|
  (all_goals simp_wf
   all_goals subst_vars
   all_goals
     first
       -- one subterm: the measure is `depth t' + 1`
       | (simp only [Term.depth]; omega)
       -- an element of a list, where the layer is a bare fold (union)…
       | (have hle := Term.depth_le_depthL ‹_ ∈ _›
          simp only [Term.depth]
          exact Nat.lt_succ_of_le hle)
       -- …or a `max` (list): the prefix, the spread and the suffix each sit under one
       -- branch of the nested `max`, and `omega` reads `Nat.max` directly, so one
       -- alternative per companion covers all three rather than one per branch.
       | (have hle := Term.depth_le_depthL ‹_ ∈ _›
          simp only [Term.depth]
          omega)
       | (have hle := Term.depthO_le ‹_ ∈ _›
          simp only [Term.depth]
          omega)
       -- the spread, where the recursion substituted `sp := some t'` and left no
       -- membership to read: `depthO (some t')` IS `t'.depth`, so the row needs no premise
       | (simp only [Term.depth, Term.depthO]; omega)
       -- a declared field's term: the inequality `sizeOf` cannot give
       | exact Term.depth_lt_object_req _ (by assumption)
       | exact Term.depth_lt_object_opt _ (by assumption)
       -- the rest policy's codec
       | exact Term.depth_lt_object_rest (by assumption)
       | exact Term.depth_lt_object_rest rfl
       | (simp only [Term.depth, Body.depth, Rest.depth]
          first
            | exact Nat.lt_succ_of_le (le_trans (Nat.le_succ _) (le_max_right _ _))
            | exact Nat.lt_succ_of_le (le_max_right _ _)
            | omega)))

end Calculus
