import Calculus.Codec
import Mathlib.Data.Finset.Lattice.Fold

/-!
# §3–§4 — The term language

Deep embedding. Notes:

* Predicates carried by terms (`refine`) are `Bool`-valued so the denotation
  needs no classical choice; the doc's subsets are their coercions. `Pred` below is that
  predicate **as data** where the data exists, and a function only where it does not.
* `custom` carries its pair as data; its *laws* are premises of the typing rule (§3),
  exactly as in the doc.
* `opaque` is a Lean keyword, hence `opaq`.
* Fields (§4) are a separate inductive — the stratification is the point: no `Term`
  position accepts a `Field`.
* An object's **payload** (§4) is a separate inductive for the same reason, one level up.
  `Body` is the key set, the field function on it, and the rest policy, as one thing — so
  every table over terms has a *one-argument* `.object` row that delegates to a `Body`
  companion, the way `denote`'s row delegates to `fieldSem` and `restSem`. Threading three
  arguments by hand through twenty tables was the only reason those three had to agree by
  convention rather than by type.
-/

namespace Calculus

/-- §3 `(refine)`'s predicate, as far as it can be read.

    A bare `Value → Bool` decides nothing a table can see, and two things wanted to see it.
    `Orth` cannot certify `set(literal k ls)` against another one while the predicate is a
    function, so the pair keeps a host exemption that the model proves nothing about. And
    `src/codec/term.ts` had already made the same move for the same reason: its predicate type is
    `members | each | closure`, and its docstring says the declaration guard has to read the
    predicate as data. These are the same three cases, so the two sides are now one shape.

    * `members` is membership of a literal's alternatives, `inL k ls`. The base indexes the
      carrier, exactly as `Term.literal` does.
    * `each` lifts an element predicate to a wire set, `liftQ`. It is what makes
      `set(literal k ls)` expressible: `set` takes a base, so a restricted element is a
      restriction of the *set*, and `setCodec_restrict` proves the two are one pair.
    * `closure` is a caller's function. It is the case that stays opaque, and it is why this
      is a wider type and not a narrower one: `refine` still carries an arbitrary predicate,
      and every theorem that quantifies over one still runs.

    `Pred` mentions no `Term`, so it is not in the mutual block below. Its `eval` is not here
    either: `inL` is in `Prisms.lean` and `liftQ` in `Products.lean`, neither of which
    `Term.lean` imports, so
    `Pred.eval` sits beside `denote`. The type is the term language's; the meaning is the
    denotation's. -/
inductive Pred where
  | members (k : GroundKind) (ls : NEFinset k.Carrier)
  | each    (p : Pred)
  | closure (q : Value → Bool)

mutual

inductive Term where
  | string | number | decimal | boolean | binary
  /-- §3 `(null)`: the `NULL` point. `Value.null` and `⟨NULL, ∗⟩` are in §1 and
      `nullCodec` is one of `opaque`'s options, but until now no *term* denoted it —
      so a schema could not say "this attribute is exactly NULL". -/
  | null
  /-- §3 `(literal)`: a ground **base**, and one inhabitant of that base's carrier.

      This was three constructors — arity-one over a value, and ~~literalS~~/~~literalN~~ at the
      two commonest bases — because no single payload type could say "this alternative, at this
      base". `(k : GroundKind)` with `v : k.Carrier` says it: the base is an index, so
      `g ground` is unsayable-otherwise and the member is a function rather than an index with a
      premise, and `ℓ ⊆ T` is the carrier. `.null`'s carrier is `Unit`, so `literal .null` can
      say nothing but what it means.

      **One value, and several values are a `union`.** A set of alternatives is a certified
      union of singletons: the members are pairwise separated because the values differ, which
      is `OrthL` at one base. `Calculus/LiteralArity1.lean` derives that rule. -/
  | literal (k : GroundKind) (v : k.Carrier)
  /-- §3 `(set)`, indexed by its element **base** rather than by an arbitrary element term.

      The rule's premise was `⊢ c : T ⇝ μ` together with `setMember μ = some μS`, and
      `setMember` is partial — so the constructor accepted element terms the rule then
      refused (`set(union(string, boolean))` was the standing witness). `SetBase` is the
      four bases that survive that premise, so the member is a function of the index and
      the refusal is a type error.

      **What this gives up, deliberately.** `set(refine(b, q))` and `set(literal k ls)` are
      *not* lost: a restriction of the elements is a restriction of the set, and
      `setCodec_restrict` and `setCodec_restrict_p` (`Products.lean`) prove the two are
      one pair on the nose, the first on `e` and the second on `p`, with `liftQ` carrying
      the predicate through. This cited the write-side theorem for both halves, and the
      read side was a sentence in its docstring until it was proved. What is lost is
      `set(held b f g)` and `set(legacy b r)` — an element-level adapter and an
      element-level read widening. Neither appears in `src/`, and neither has a set-level
      spelling: a set-level `held` would need `setImage` rather than the classical
      `Finset.image` to stay injective, and a set-level `legacy` widens the whole attribute
      rather than each member. -/
  | set      (base : SetBase)
  /-- §3 `(list)`: the one positional container, as a prefix, at most one spread, and a
      suffix. `array`, `(tuple)` and `(tuple-tail)` were three shapes of one thing, and
      none of the three could say `[A, B, ...C[], D]` — a fixed position AFTER a spread.

      A value of length `n` is admitted when `n ≥ pre.length + suf.length`: `pre` aligns
      from the left, `suf` from the right, and every position between them goes through
      the spread. With `spread = none` the arity is exactly `pre.length + suf.length`.

      **Two spreads have no term**, because the spread is an `Option` and not a `List`. The
      host carries a type-level refusal for a rest element that is not last, and that
      refusal has nothing left to refuse: the ambiguity it excluded is now unrepresentable.
      `array` and `tuple` survive below as *builders*, so a statement that spells either
      keeps its spelling. -/
  | list     (pre : List Term) (spread : Option Term) (suf : List Term)
  | record   (val : Term)
  | held     (inner : Term) (f : Value → Value) (g : Value → Value)
  | refine   (inner : Term) (p : Pred)
  | legacy   (inner : Term) (r : Attr → Option Value)
  /-- §3 `(lazy)`. The thunk is *not* `Unit → Term`: a closure adds no constructible
      term (every `Term` is finite either way) and only defeats the termination
      checker. Recursive codecs are not modelled, and cannot be — see
      `Continuity.lean`: `union`'s admission is anti-monotone, so a genuinely
      recursive union has no fixpoint semantics in any system. -/
  | lazy     (inner : Term)
  | custom   (ce : Value → Option Attr) (cp : Attr → Option Value)
  /-- §3 `(opaque)`: `lossy = false` is the `refuse` policy. -/
  | opaq     (lossy : Bool)
  /-- §4's field table is a *set* of names each declaring one field, so that is what the
      term carries. A `List (Name × Field)` admitted two orderings of one object and a
      repeated name, and the typing rule carried a `Nodup` premise to make the first
      harmless and rule out the second; both are now properties of the type. `Field`
      sits in the function's codomain, which is strictly positive — the same factoring
      `Attr.m` and `Value.map` use one level down. -/
  | object   (b : Body)
  | union    (options : List Term)
  /-- §5's bottom: the term that admits no value. Its held set is `False`, which is a subset of
      every held set, so (D) fails against every other option and this is an option of no
      `union`. A constructor and not an empty `union`: the empty option list is a term a caller
      can build by accident, and a rule that reads it as the bottom reads that accident as intent. -/
  | never

/-- §4's object payload: the declared names, the field at each, and the policy for
    everything else. A `mutual` block admits no `structure`, so this is `inductive … | mk`
    and the projections below are written by hand — three lines, against a `Body`-shaped
    row in every table over terms. -/
inductive Body where
  | mk (fields : Finset Name) (f : {k // k ∈ fields} → Field) (rest : Rest)

inductive Field where
  | req      (t : Term)
  | optional (t : Term)
  | fallback (t : Term) (v : Value)

inductive Rest where
  | drop | refuse
  | codec (t : Term)

end

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


/-! ## `Body`'s projections

`inductive … | mk` generates none, and a `mutual` block admits no `structure`, so these are
written out. They are named for `MapOf`'s — `fields`/`at` — because a body *is* a `MapOf Field`
paired with a policy, and `MapOf Field` is not expressible here: nesting an inductive through a
structure whose field is a function into the type being defined is not something the nested
inductive compiler accepts.

The projections exist so that a *statement* about an object can quantify over one thing. Rows
that need all three components still pattern-match on `.mk`, which is cheaper than three
projections and keeps the equation compiler's iota reductions available. -/

def Body.fields : Body → Finset Name
  | .mk fields _ _ => fields

def Body.at : (b : Body) → {k // k ∈ b.fields} → Field
  | .mk _ f _ => f

def Body.rest : Body → Rest
  | .mk _ _ rest => rest

@[simp] theorem Body.fields_mk (fields : Finset Name) (f : {k // k ∈ fields} → Field)
    (rest : Rest) : (Body.mk fields f rest).fields = fields := rfl

@[simp] theorem Body.rest_mk (fields : Finset Name) (f : {k // k ∈ fields} → Field)
    (rest : Rest) : (Body.mk fields f rest).rest = rest := rfl

@[simp] theorem Body.at_mk (fields : Finset Name) (f : {k // k ∈ fields} → Field)
    (rest : Rest) : (Body.mk fields f rest).at = f := rfl

/-- `codec` is the policy that *holds* an undeclared name; `drop` and `refuse` both refuse
    it on the way out. -/
def Rest.isOpen : Rest → Bool
  | .codec _ => true
  | .drop | .refuse => false

/-- An **open object**: one whose rest policy is a codec, so an undeclared name is held
    rather than refused.

    §5's closed-option dischargers exclude exactly these, and they used to say so with three
    quantifiers and a disequality — `∀ fields ff tr, t ≠ .object fields ff (.codec tr)` — at
    seven statements. The payload is one thing now, so the exclusion is one decidable
    question about it. `isOpenObject_eq_false` below is the form the disequality had. -/
def Term.isOpenObject : Term → Bool
  | .object b => b.rest.isOpen
  | _ => false

/-- The old spelling of the premise, so a reader can see the two say the same thing. -/
theorem Term.isOpenObject_eq_false {t : Term} :
    t.isOpenObject = false ↔ ∀ b tr, t = .object b → b.rest ≠ .codec tr := by
  constructor
  · intro h b tr hb hr
    subst hb
    simp only [Term.isOpenObject, hr, Rest.isOpen] at h
    exact absurd h (by simp)
  · intro h
    cases t with
    | object b =>
      cases hr : b.rest with
      | drop => simp [Term.isOpenObject, hr, Rest.isOpen]
      | refuse => simp [Term.isOpenObject, hr, Rest.isOpen]
      | codec tr => exact absurd hr (h b tr rfl)
    | _ => rfl


/-! ## A structural measure on terms

`denote` recurses structurally and needs no measure. The **proofs** do: `soundness_both` recurses
on the derivation, and `Typed` is a `Prop`-valued mutual family with no `.brecOn`, so it has to
recurse on the term instead — and `sizeOf` cannot serve, because `Term.object`'s field table is a
*function* and `sizeOf` is blind to functions (`sizeOf f = 0`).

This is the measure that sees through it, and it is not a new idea: it is exactly the shape
`Value.depth` in `Opaque.lean` has always used — `attach.sup` over the key set where a list would
fold. What matters is that it is **derived from the term** rather than supplied by a caller, so it
appears in no statement, no `Obligations`, and no rule. That is the whole difference between this
and the `fuel` parameter it replaces. -/

mutual

def Term.depth : Term → Nat
  | .string | .number | .decimal | .boolean | .binary | .null
  -- `set` is a **leaf** since its base became an index: there is no element term to
  -- measure, so it sits with the other ground shapes rather than costing a layer.
  | .literal _ _ | .custom _ _ | .opaq _ | .set _ | .never => 1
  | .record t | .lazy t => Term.depth t + 1
  | .held t _ _ | .refine t _ | .legacy t _ => Term.depth t + 1
  | .list pre sp suf =>
      max (Term.depthL pre) (max (Term.depthO sp) (Term.depthL suf)) + 1
  -- one companion, like every other non-leaf row
  | .object b => Body.depth b + 1
  | .union opts => Term.depthL opts + 1
/-- The payload's own budget: the field table is a key *set* with a function on it, so its
    layer is the largest field budget over the key set — a `Finset.sup`, where a list would be
    a fold — against the rest policy's. This is the companion `Field.depth` and `Rest.depth`
    were always missing: the object row used to inline it, which is why the three inequality
    lemmas below had to quantify over three components. -/
def Body.depth : Body → Nat
  | .mk fields f rest =>
      max (fields.attach.sup fun k => Field.depth (f k)) (Rest.depth rest) + 1

def Field.depth : Field → Nat
  | .req t | .optional t => Term.depth t + 1
  | .fallback t _ => Term.depth t + 1

def Rest.depth : Rest → Nat
  | .drop | .refuse => 1
  | .codec t => Term.depth t + 1

def Term.depthL : List Term → Nat
  | [] => 1
  | t :: ts => max (Term.depth t) (Term.depthL ts)

def Term.depthO : Option Term → Nat
  | none => 1
  | some t => Term.depth t

end

theorem Term.depth_pos (t : Term) : 0 < Term.depth t := by
  cases t <;> simp [Term.depth]

/-- A list element is no deeper than its list. -/
theorem Term.depth_le_depthL : ∀ {ts : List Term} {t}, t ∈ ts → Term.depth t ≤ Term.depthL ts
  | _ :: _, _, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · simp [Term.depthL]
      · exact le_trans (Term.depth_le_depthL h') (by simp [Term.depthL])

theorem Term.depthO_le : ∀ {tail : Option Term} {t}, t ∈ tail → Term.depth t ≤ Term.depthO tail
  | some _, _, h => by cases h; simp [Term.depthO]

/-- A declared field is strictly shallower than the body — the inequality `sizeOf` cannot give,
    and the reason this measure exists. Stated at `Body`, where it belongs: it is a fact about a
    key set and a function on it, and mentions no `Term` at all. -/
theorem Body.depth_lt_field : ∀ (b : Body) (k : {k // k ∈ b.fields}),
    Field.depth (b.at k) < Body.depth b
  | .mk fields f _, k => by
      have : (fun k => Field.depth (f k)) k ≤ fields.attach.sup fun k => Field.depth (f k) :=
        Finset.le_sup (f := fun k => Field.depth (f k)) (Finset.mem_attach _ k)
      simp only at this
      simp only [Body.depth, Body.at]
      omega

/-- …and the rest policy's codec, the other half of the payload. -/
theorem Body.depth_lt_rest : ∀ (b : Body) {t : Term}, b.rest = .codec t →
    Term.depth t < Body.depth b
  | .mk _ _ _, _, h => by
      simp only [Body.rest] at h
      subst h
      simp only [Body.depth, Rest.depth]
      omega

/-- The body is strictly shallower than the object term — one layer, by `rfl` on the measure. -/
theorem Term.depth_lt_object_body (b : Body) : Body.depth b < Term.depth (.object b) := by
  simp only [Term.depth]; omega

/-- A declared field's *layer* against the object's, kept under its old name: every downstream
    citation is of this, and the payload's own version is `Body.depth_lt_field`. -/
theorem Term.depth_lt_object (b : Body) (k : {k // k ∈ b.fields}) :
    Field.depth (b.at k) < Term.depth (.object b) :=
  lt_trans (Body.depth_lt_field b k) (Term.depth_lt_object_body b)

/-- …and the three field shapes, which is what a proof recursing into a declared field needs.
    A row that matched `.object (.mk fields f rest)` discharges these with `f k = .req t` in
    hand: `(Body.mk fields f rest).at k` is `f k` by `rfl`, so `assumption` closes it. -/
theorem Term.depth_lt_object_req {b : Body} (k : {k // k ∈ b.fields}) {t : Term}
    (h : b.at k = .req t) : Term.depth t < Term.depth (.object b) := by
  have h1 := Term.depth_lt_object b k
  rw [h] at h1; simp only [Field.depth] at h1; omega

theorem Term.depth_lt_object_opt {b : Body} (k : {k // k ∈ b.fields}) {t : Term}
    (h : b.at k = .optional t) : Term.depth t < Term.depth (.object b) := by
  have h1 := Term.depth_lt_object b k
  rw [h] at h1; simp only [Field.depth] at h1; omega

theorem Term.depth_lt_object_fb {b : Body} (k : {k // k ∈ b.fields}) {t : Term} {v : Value}
    (h : b.at k = .fallback t v) : Term.depth t < Term.depth (.object b) := by
  have h1 := Term.depth_lt_object b k
  rw [h] at h1; simp only [Field.depth] at h1; omega

/-- The rest policy's codec against the object's layer, for the same reason. -/
theorem Term.depth_lt_object_rest {b : Body} {t : Term} (h : b.rest = .codec t) :
    Term.depth t < Term.depth (.object b) :=
  lt_trans (Body.depth_lt_rest b h) (Term.depth_lt_object_body b)

/-- The termination argument every `Term.depth` recursion in this development uses, written
    once. **Three** theorems share it, all in `Soundness.lean` — `soundness_both`,
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
       | exact Term.depth_lt_object_fb _ (by assumption)
       -- the rest policy's codec
       | exact Term.depth_lt_object_rest (by assumption)
       | exact Term.depth_lt_object_rest rfl
       | (simp only [Term.depth, Body.depth, Rest.depth]
          first
            | exact Nat.lt_succ_of_le (le_trans (Nat.le_succ _) (le_max_right _ _))
            | exact Nat.lt_succ_of_le (le_max_right _ _)
            | omega)))

end Calculus
