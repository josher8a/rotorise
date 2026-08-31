import Calculus.Codec
import Mathlib.Data.Finset.Lattice.Fold

/-!
# §3–§4 — The term language

Deep embedding. Notes:

* Predicates carried by terms (`refine`) are `Bool`-valued so the denotation
  needs no classical choice; the doc's subsets are their coercions.
* `custom` carries its pair as data; its *laws* are premises of the typing rule (§3),
  exactly as in the doc.
* `opaque` is a Lean keyword, hence `opaq`.
* Fields (§4) are a separate inductive — the stratification is the point: no `Term`
  position accepts a `Field`.
-/

namespace Calculus

mutual

inductive Term where
  | string | number | decimal | boolean | binary
  /-- §3 `(null)`: the `NULL` point. `Value.null` and `⟨NULL, ∗⟩` are in §1 and
      `nullCodec` is one of `opaque`'s options, but until now no *term* denoted it —
      so a schema could not say "this attribute is exactly NULL". -/
  | null
  /-- §3 `(literal)`, in the shape §3 states it: a ground **base**, and a nonempty finite set
      of that base's alternatives.

      This was three constructors — arity-one over a value, and `literalS`/`literalN` at the
      two commonest bases — because no single payload type could say "these alternatives, all
      at one base". `(k : GroundKind)` with `ls : NEFinset k.Carrier` says it: the base is an
      index, so `g ground` is unsayable-otherwise and the member is a function rather than an
      index with a premise; the alternatives are a `NEFinset` of that base's carrier, so
      `n ≥ 1`, pairwise distinctness *and* homogeneity are the type's. Arity one is the
      singleton case, and `.null`'s carrier is `Unit`, so `literal .null` can say nothing but
      what it means.

      Not a union of arity-one literals, which is derivable but not free: see
      `Calculus/LiteralArity1.lean` and `docs/codec-audit.md` §11.5. -/
  | literal (k : GroundKind) (ls : NEFinset k.Carrier)
  | set      (elem : Term)
  | array    (elem : Term)
  /-- `(tuple)` and `(tuple-tail)` in one constructor; `tail = none` is the plain tuple. -/
  | tuple    (elems : List Term) (tail : Option Term)
  | record   (val : Term)
  | held     (inner : Term) (f : Value → Value) (g : Value → Value)
  | refine   (inner : Term) (q : Value → Bool)
  | legacy   (inner : Term) (r : Attr → Option Value)
  | nullable (inner : Term)
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
  | object   (fields : Finset Name) (f : {k // k ∈ fields} → Field) (rest : Rest)
  | union    (options : List Term)
  | dunion   (d : Name) (options : List Term)

inductive Field where
  | req      (t : Term)
  | optional (t : Term)
  | fallback (t : Term) (v : Value)

inductive Rest where
  | drop | refuse
  | codec (t : Term)

end

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
  | .literal _ _ | .custom _ _ | .opaq _ => 1
  | .set t | .array t | .record t | .nullable t | .lazy t => Term.depth t + 1
  | .held t _ _ | .refine t _ | .legacy t _ => Term.depth t + 1
  | .tuple ts tail => max (Term.depthL ts) (Term.depthO tail) + 1
  -- the field table is a key *set* with a function on it, so its layer is the largest field
  -- budget over the key set — a `Finset.sup`, where a list would be a fold
  | .object fields f rest =>
      max (fields.attach.sup fun k => Field.depth (f k)) (Rest.depth rest) + 1
  | .union opts => Term.depthL opts + 1
  | .dunion _ opts => Term.depthL opts + 1

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

/-- A declared field's term is strictly shallower than the object — the inequality `sizeOf`
    cannot give, and the reason this measure exists. -/
theorem Term.depth_lt_object {fields : Finset Name} (f : {k // k ∈ fields} → Field)
    (rest : Rest) (k : {k // k ∈ fields}) :
    Field.depth (f k) < Term.depth (.object fields f rest) := by
  have : (fun k => Field.depth (f k)) k ≤ fields.attach.sup fun k => Field.depth (f k) :=
    Finset.le_sup (f := fun k => Field.depth (f k)) (Finset.mem_attach _ k)
  simp only at this
  simp only [Term.depth]
  omega

/-- …and the three field shapes, which is what a proof recursing into a declared field needs. -/
theorem Term.depth_lt_object_req {fields : Finset Name} {f : {k // k ∈ fields} → Field}
    {rest : Rest} (k : {k // k ∈ fields}) {t : Term} (h : f k = .req t) :
    Term.depth t < Term.depth (.object fields f rest) := by
  have h1 := Term.depth_lt_object f rest k
  rw [h] at h1; simp only [Field.depth] at h1; omega

theorem Term.depth_lt_object_opt {fields : Finset Name} {f : {k // k ∈ fields} → Field}
    {rest : Rest} (k : {k // k ∈ fields}) {t : Term} (h : f k = .optional t) :
    Term.depth t < Term.depth (.object fields f rest) := by
  have h1 := Term.depth_lt_object f rest k
  rw [h] at h1; simp only [Field.depth] at h1; omega

theorem Term.depth_lt_object_fb {fields : Finset Name} {f : {k // k ∈ fields} → Field}
    {rest : Rest} (k : {k // k ∈ fields}) {t : Term} {v : Value} (h : f k = .fallback t v) :
    Term.depth t < Term.depth (.object fields f rest) := by
  have h1 := Term.depth_lt_object f rest k
  rw [h] at h1; simp only [Field.depth] at h1; omega

theorem Term.depth_lt_rest {fields : Finset Name} (f : {k // k ∈ fields} → Field) (rest : Rest) :
    Rest.depth rest < Term.depth (.object fields f rest) := by
  simp only [Term.depth]; omega

/-- The termination argument every `Term.depth` recursion in this development uses, written
    once. Five theorems share it — `soundness_both`, `typed_TSub`, `carrier_denote`,
    `Adm_sound`, `AdmA_sound` — and their goal sets differ, so some alternatives
    are dead at each use. That is what the `unreachableTactic` linter reports at those sites,
    and it is why the option is disabled there rather than the block being specialised five
    ways. -/
macro "term_depth_wf" : tactic => `(tactic|
  (all_goals simp_wf
   all_goals subst_vars
   all_goals
     first
       -- one subterm: the measure is `depth t' + 1`
       | (simp only [Term.depth]; omega)
       -- an element of a list, where the layer is a bare fold (union, dunion)…
       | (have hle := Term.depth_le_depthL ‹_ ∈ _›
          simp only [Term.depth]
          exact Nat.lt_succ_of_le hle)
       -- …or a `max` (tuple)
       | (have hle := Term.depth_le_depthL ‹_ ∈ _›
          simp only [Term.depth]
          exact Nat.lt_succ_of_le (le_trans hle (le_max_left _ _)))
       | (have hle := Term.depthO_le ‹_ ∈ _›
          simp only [Term.depth]
          exact Nat.lt_succ_of_le (le_trans hle (le_max_right _ _)))
       -- a declared field's term: the inequality `sizeOf` cannot give
       | exact Term.depth_lt_object_req _ (by assumption)
       | exact Term.depth_lt_object_opt _ (by assumption)
       | exact Term.depth_lt_object_fb _ (by assumption)
       -- the rest policy's codec
       | (simp only [Term.depth, Rest.depth]
          first
            | exact Nat.lt_succ_of_le (le_trans (Nat.le_succ _) (le_max_right _ _))
            | exact Nat.lt_succ_of_le (le_max_right _ _)
            | omega)))

end Calculus
