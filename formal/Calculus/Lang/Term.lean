import Calculus.Alg.Containers
import Calculus.Alg.Recursion
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The term language over a universe signature

A universe is a syntax and a meaning. `Syn` holds the values that a `held` maps, the primitives
and the predicates: the term language `Term S` reads nothing else, so a term is data that code can
compute with. `Sem S` holds the stored carrier, the member, the codec of each primitive, one
former record per container, and the canonical top. `denote` builds each former from the generic
combinators, so a universe writes no denotation.

`Sem` is a class over the syntax, so `denote t` finds its meaning from the term's own universe,
and the term family carries no instance argument.

A former is an `Option`: a universe without the former denotes the term as the bottom. A
carrier can hold no `Finset` of itself, because the kernel refuses the nested occurrence, so
the set former is a codec transformer with its law, and not a prism.
-/

namespace Calculus.Alg

/-- The list former of a universe: a prism from each carrier onto `List`, the member that the
    stored side stamps, and the fact that an element is one layer below its list. -/
structure ListF (V A M : Type) (member : A → M) (dV : V → Nat) (dA : A → Nat) where
  pV : Ctor (List V) V
  pA : Ctor (List A) A
  μ : M
  hμ : ∀ y, member (pA.into y) = μ
  dV_lt : ∀ vs, ∀ x ∈ vs, dV x + 1 ≤ dV (pV.into vs)
  dA_lt : ∀ as, ∀ x ∈ as, dA x + 1 ≤ dA (pA.into as)

/-- The keyed-map former of a universe: the same four facts onto `MapOf`. -/
structure MapF (V A M : Type) (member : A → M) (dV : V → Nat) (dA : A → Nat) where
  mV : Ctor (MapOf V) V
  mA : Ctor (MapOf A) A
  μ : M
  hμ : ∀ y, member (mA.into y) = μ
  dV_lt : ∀ (m : MapOf V) k, dV (m.get k) + 1 ≤ dV (mV.into m)
  dA_lt : ∀ (m : MapOf A) k, dA (m.get k) + 1 ≤ dA (mA.into m)

/-- The set former of a universe: the lift, its law, and its agreement one layer down. -/
structure SetF (V A M : Type) (member : A → M) (dV : V → Nat) (dA : A → Nat) where
  lift : Codec V A M → Codec V A M
  lawful : ∀ {c}, Lawful member c → Lawful member (lift c)
  agree : ∀ {d c₁ c₂}, AgreeLe dV dA d c₁ c₂ → AgreeLe dV dA (d + 1) (lift c₁) (lift c₂)
  /-- The universe's own obligation on an element. Soundness does not read this field. -/
  elem : Codec V A M → Prop
  /-- The held set of a set, from the held set of its element. -/
  held : (V → Prop) → V → Prop
  /-- The member of a set, from the member of its element. -/
  member : M → Option M
  /-- The lift of a codec on its carrier is on its carrier. -/
  carrier : ∀ {c : Codec V A M}, Carrier c → Carrier (lift c)
  /-- The lift's held set is inside `held` of any bound on the element's held set. -/
  held_of : ∀ {c : Codec V A M} {T : V → Prop}, (∀ v, c.T v → T v) → ∀ v, (lift c).T v → held T v

/-- **The syntax of a universe**: the values a `held` maps, the primitives, and the predicates.
    The term language reads no more than this, so a term over a universe is data that code can
    compute with, whatever the universe's codecs are. -/
structure Syn where
  V : Type
  Ground : Type
  Pred : Type

/-- **The meaning of a universe**: the stored carrier, the member, and the codec of each part of
    the syntax. A class over the syntax, so `denote t` finds the meaning from the term's own
    universe, and the term family carries no instance argument. -/
class Sem (S : Syn) where
  A : Type
  M : Type
  member : A → M
  decM : DecidableEq M
  ground : S.Ground → Codec S.V A M
  lawful_ground : ∀ g, Lawful member (ground g)
  carrier_ground : ∀ g, Carrier (ground g)
  eval : S.Pred → S.V → Bool
  dV : S.V → Nat
  dA : A → Nat
  dV_pos : ∀ v, 0 < dV v
  dA_pos : ∀ a, 0 < dA a
  list : Option (ListF S.V A M member dV dA)
  map : Option (MapF S.V A M member dV dA)
  set : Option (SetF S.V A M member dV dA)
  /-- The member that the judgement gives a primitive. -/
  groundμ : S.Ground → Option M
  top : Codec S.V A M
  lawful_top : Lawful member top
  carrier_top : Carrier top
  /-- The held set that the judgement gives the top, and the top's held set lies inside it. -/
  topHeld : S.V → Prop
  top_held : ∀ v, top.T v → topHeld v

instance (S : Syn) [Sem S] : DecidableEq (Sem.M S) := Sem.decM

/-- The codecs of a universe. -/
abbrev Syn.C (S : Syn) [Sem S] : Type := Codec S.V (Sem.A S) (Sem.M S)

mutual

inductive Term (S : Syn) where
  /-- §3's ground rules, as one row: a primitive of the universe. A universe names its primitives
      (`Syn.Ground`) and the codec of each (`Sem.ground`). -/
  | prim (g : S.Ground)
  /-- §3 `(set)`: the finite-powerset lift of an element term. A lawful element gives a lawful
      set (`lawful_setCodec`), and that law reads nothing about the element's base.

      **The DynamoDB set rules are not structure here.** That a stored set holds elements of one
      member of `S`, `N` or `B` is the store universe's rule, and `Obligations` states it as
      `SetElem`, the way `(union)`'s compatibility is stated. The three element types and the
      absent empty set are the carrier's (`Value.strSet`, `numSet`, `binSet`). So a restricted
      element, a literal element and an adapter element are each spelled at the element:
      `set(refine(string, q))`, `set(literal k v)` and `set(held number string f g)`. -/
  | set      (elem : Term S)
  /-- §3 `(list)`: the one positional container, as a prefix, at most one spread, and a
      suffix. `array`, `(tuple)` and `(tuple-tail)` were three shapes of one thing, and
      none of the three could say `[A, B, ...C[], D]` — a fixed position AFTER a spread.

      A value of length `n` is admitted when `n ≥ pre.length + suf.length`: `pre` aligns
      from the left, `suf` from the right, and every position between them goes through
      the spread. With `spread = none` the arity is exactly `pre.length + suf.length`.

      **Two spreads have no term**, because the spread is an `Option` and not a `List`.
      The host's list constructor takes the spread as one parameter and inherits that,
      while its tuple takes a tail as a marker inside a variadic parameter list. So the
      host's type-level refusal for a misplaced tail still has a job, on the tuple alone:
      the refusal is narrower than it was and it is not gone. Measured, not read.
      `array` and `tuple` survive below as *builders*, so a statement that spells either
      keeps its spelling. -/
  | list     (pre : List (Term S)) (spread : Option (Term S)) (suf : List (Term S))
  /-- §3 `(held)`: a morphism between two restrictions. `inner` restricts the stored side,
      `outer` restricts the caller side, and `f` and `g` only transform between the two. The
      caller side has no unrestricted spelling: a caller that states no restriction writes
      `.opaq` as `outer`. -/
  | held     (inner : Term S) (outer : Term S) (f : S.V → S.V) (g : S.V → S.V)
  | refine   (inner : Term S) (p : S.Pred)
  /-- §3 `(opaque)`: the universal sum. The number option is `numberCodec`, so `opaque`
      writes every `Value` (`opaq_total`). -/
  | opaq
  /-- §4's field table is a *set* of names each declaring one field, so that is what the
      term carries. A `List (Name × ObjectSlot)` admitted two orderings of one object and a
      repeated name, and the typing rule carried a `Nodup` premise to make the first
      harmless and rule out the second; both are now properties of the type. `ObjectSlot`
      sits in the function's codomain, which is strictly positive — the same factoring
      `Attr.m` and `Value.map` use one level down. -/
  | object   (b : Body S)
  | union    (options : List (Term S))
  /-- §5's bottom: the term that admits no value. Its held set is `False`, which is a subset of
      every held set. A constructor and not an empty `union`: the empty option list is a term a
      caller can build by accident, and a rule that reads it as the bottom reads that accident as
      intent. -/
  | never
  /-- A bound variable, as a de Bruijn index: `var 0` names the nearest enclosing `mu`. A closed
      term reads a variable that no `mu` binds as the bottom. -/
  | var (i : Nat)
  /-- A guarded recursive term: `mu b` is the fixed point of `b`, where `var 0` in `b` stands for
      `mu b` itself. The name is not `rec`, which the recursor holds. `denote` reads each input at
      the stage of `b` that the input's own depth names (`muCodec`).

      **The guard is a checked condition, and not a type.** `Term.guarded` refuses a variable that
      reads the input of its binder itself, as in `mu (var 0)` and `mu (union [var 0, string])`,
      and a variable under a `held`, whose `f` can make the input deeper. `Typed.mu` carries the
      guard, and the test file pins each refusal. A type would need a second term family for the
      body of a binder, and every table over terms would then have one more family. -/
  | mu (body : Term S)

/-- §4's object payload: the declared names, the slot at each, and the one open block.
    The type is `inductive … | mk`, so the projections below are written by hand: three lines,
    against a `Body`-shaped row in every table over terms.

    **A body is a partition of the key space.** The declared names are one block each, `wild`
    is the single open block, and every remaining name is refused. There is no policy that
    silently drops a name: an undeclared name a body does not claim is a name the body refuses,
    on the way in and on the way out. The declared names are subtracted *structurally*, so no
    well-formedness premise travels with a body.

    **An open block needs no ban list.** A name an open body must refuse is a *declared* name at
    `optional never`: the key may be absent, and nothing admits it when it is present. So
    `object({c}, exclude d)` is `{c, d : optional never}` with an open block, and the exclusion
    needs no second place to live.

    **The open block is a term and no pattern.** It holds every undeclared name. `Name` is
    `String` and so infinite, which is why two open blocks always intersect, and why one block
    is all a body can ever carry. A key pattern other than "every undeclared name", a template
    or a regular expression, is a change to this constructor. -/
inductive Body (S : Syn) where
  | mk (fields : Finset String) (f : {k // k ∈ fields} → ObjectSlot S) (wild : Option (Term S))

/-- §4's current-schema slot. A required name is required on both current-schema sides. -/
inductive ObjectSlot (S : Syn) where
  | req      (t : Term S)
  | optional (t : Term S)

end

variable {S : Syn}

/-- Whether a term is the bottom, as a `Bool` the object presence rows branch on. -/
def Term.isNever : Term S → Bool
  | .never => true
  | _ => false

/-- Whether a slot's name must be present on the write side. -/
def ObjectSlot.isReq : ObjectSlot S → Bool
  | .optional _ => false
  | _ => true

/-- A slot's presence lattice element. The bits admit presence and absence, respectively. -/
def ObjectSlot.presence (f : ObjectSlot S) : Bool × Bool :=
  match f with
  | .req t => if t.isNever then (false, false) else (f.isReq, !f.isReq)
  | .optional t => if t.isNever then (false, true) else (true, true)


/-! ## `Body`'s projections

`inductive … | mk` generates none, so these are written out. They are named for `MapOf`'s
`fields`/`at`, because a body *is* a `MapOf ObjectSlot` paired with an open block. The `mutual`
block also elaborates with `Body` as a `structure`, and with a `MapOf ObjectSlot` argument in
place of the key set and the slot function. `Body` takes neither form, so the projections are
written by hand.

The projections exist so that a *statement* about an object can quantify over one thing. Rows
that need all three components still pattern-match on `.mk`, which is cheaper than three
projections and keeps the equation compiler's iota reductions available. -/

def Body.fields : Body S → Finset String
  | .mk fields _ _ => fields

def Body.at : (b : Body S) → {k // k ∈ b.fields} → ObjectSlot S
  | .mk _ f _ => f

def Body.wild : Body S → Option (Term S)
  | .mk _ _ wild => wild

@[simp] theorem Body.fields_mk (fields : Finset String) (f : {k // k ∈ fields} → ObjectSlot S)
    (wild : Option (Term S)) : (Body.mk fields f wild).fields = fields := rfl

@[simp] theorem Body.wild_mk (fields : Finset String) (f : {k // k ∈ fields} → ObjectSlot S)
    (wild : Option (Term S)) : (Body.mk fields f wild).wild = wild := rfl

@[simp] theorem Body.at_mk (fields : Finset String) (f : {k // k ∈ fields} → ObjectSlot S)
    (wild : Option (Term S)) : (Body.mk fields f wild).at = f := rfl

/-! ## The guard of a binder

`mu b` denotes the limit of the stages of `b`, and each input reads the stage its own depth names.
That limit is stable only when `b` reads its variable at inputs strictly shallower than its own
input. A container reads its elements one layer down. A sum and a restriction read their
own input. A `held` reads its inner term at `f v`, and `f` can make the input deeper, so a variable
under a `held` has no depth bound at all.

`Term.use i t` says how `t` reads the variable `i`, as a level: `0` when `i` does not occur, `1`
when each occurrence sits under a container and none under a `held`, `2` when an occurrence reads
the input itself and none sits under a `held`, and `3` when an occurrence sits under a `held`. The
level is a `Nat` and not an inductive, because a body's slot table is a key set with a function on
it, and `Finset.sup` over `Nat` is the join over a key set that `Term.depth` already uses. The
functions below produce the four levels and no other value. -/

/-- A container reads its elements one layer down: an occurrence that read the input now reads an
    element. -/
def useUnder (u : Nat) : Nat := if u = 2 then 1 else u

/-- A `held` reads its terms at an input of any depth. -/
def useHeld (u : Nat) : Nat := if u = 0 then 0 else 3

mutual

/-- How `t` reads the variable `i`, as the level the section above defines. -/
def Term.use (i : Nat) : Term S → Nat
  | .prim _ | .opaq | .never => 0
  | .var j => if i = j then 2 else 0
  | .set t => useUnder (Term.use i t)
  | .mu t => Term.use (i + 1) t
  | .refine t _ => Term.use i t
  | .held t P _ _ => useHeld (max (Term.use i t) (Term.use i P))
  | .list pre sp suf =>
      useUnder (max (Term.useL i pre) (max (Term.useO i sp) (Term.useL i suf)))
  | .union opts => Term.useL i opts
  | .object b => useUnder (Body.use i b)

def Body.use (i : Nat) : Body S → Nat
  | .mk fields f wild =>
      max (fields.attach.sup fun k => ObjectSlot.use i (f k)) (Term.useO i wild)

def ObjectSlot.use (i : Nat) : ObjectSlot S → Nat
  | .req t | .optional t => Term.use i t

def Term.useL (i : Nat) : List (Term S) → Nat
  | [] => 0
  | t :: ts => max (Term.use i t) (Term.useL i ts)

def Term.useO (i : Nat) : Option (Term S) → Nat
  | none => 0
  | some t => Term.use i t

end

mutual

/-- **Every binder is guarded**: at each `mu b`, `b` reads `var 0` at level `1` or less. -/
def Term.guarded : Term S → Bool
  | .prim _ | .opaq | .never | .var _ => true
  | .mu t => decide (Term.use 0 t ≤ 1) && Term.guarded t
  | .set t => Term.guarded t
  | .refine t _ => Term.guarded t
  | .held t P _ _ => Term.guarded t && Term.guarded P
  | .list pre sp suf => Term.guardedL pre && Term.guardedO sp && Term.guardedL suf
  | .union opts => Term.guardedL opts
  | .object b => Body.guarded b

def Body.guarded : Body S → Bool
  | .mk fields f wild =>
      decide (∀ k : {k // k ∈ fields}, ObjectSlot.guarded (f k) = true) && Term.guardedO wild

def ObjectSlot.guarded : ObjectSlot S → Bool
  | .req t | .optional t => Term.guarded t

def Term.guardedL : List (Term S) → Bool
  | [] => true
  | t :: ts => Term.guarded t && Term.guardedL ts

def Term.guardedO : Option (Term S) → Bool
  | none => true
  | some t => Term.guarded t

end

mutual
/-- Whether a variable occurs in the term. A term with no variable denotes one codec under every
    environment (`denote_closed`). -/
def Term.hasVar : Term S → Bool
  | .var _ => true
  | .refine t _ | .mu t | .set t => Term.hasVar t
  | .held t P _ _ => Term.hasVar t || Term.hasVar P
  | .list pre sp suf => Term.hasVarL pre || Term.hasVarO sp || Term.hasVarL suf
  | .object b => Body.hasVar b
  | .union os => Term.hasVarL os
  | .prim _ | .opaq | .never => false
/-- …in a body: in a declared slot or in the open block. -/
def Body.hasVar : Body S → Bool
  | .mk fs f w => decide (∃ k : {k // k ∈ fs}, ObjectSlot.hasVar (f k) = true) || Term.hasVarO w
/-- …in a slot's term. -/
def ObjectSlot.hasVar : ObjectSlot S → Bool
  | .req t | .optional t => Term.hasVar t
/-- …in a list of terms. -/
def Term.hasVarL : List (Term S) → Bool
  | [] => false
  | t :: ts => Term.hasVar t || Term.hasVarL ts
/-- …in an optional term. -/
def Term.hasVarO : Option (Term S) → Bool
  | none => false
  | some t => Term.hasVar t
end

/-! ## A structural measure on terms

`denote` recurses structurally and needs no measure. The **proofs** do: `soundness` recurses
on the derivation, and `Typed` is a `Prop`-valued mutual family with no `.brecOn`, so it has to
recurse on the term instead — and `sizeOf` cannot serve, because `Term.object`'s field table is a
*function* and `sizeOf` is blind to functions (`sizeOf f = 0`).

This is the measure that sees through it, and it is not a new idea: it is exactly the shape
`Value.depth` in `Recursion.lean` uses — `attach.sup` over the key set where a list would
fold. What matters is that it is **derived from the term** rather than supplied by a caller, so it
appears in no statement, no `Obligations`, and no rule. That is the whole difference between this
and the `fuel` parameter it replaces. -/

mutual

def Term.depth : Term S → Nat
  | .prim _ | .opaq | .never | .var _ => 1
  | .mu t => Term.depth t + 1
  | .set t => Term.depth t + 1
  | .held t P _ _ => max (Term.depth t) (Term.depth P) + 1
  | .refine t _ => Term.depth t + 1
  | .list pre sp suf =>
      max (Term.depthL pre) (max (Term.depthO sp) (Term.depthL suf)) + 1
  -- one companion, like every other non-leaf row
  | .object b => Body.depth b + 1
  | .union opts => Term.depthL opts + 1
/-- The payload's own budget: the slot table is a key *set* with a function on it, so its
    layer is the largest slot budget over the key set — a `Finset.sup`, where a list would be
    a fold — against the open block's. This is the companion `ObjectSlot.depth` and
    `Body.wildDepth` were always missing: the object row used to inline it, which is why the
    three inequality lemmas below had to quantify over three components. -/
def Body.depth : Body S → Nat
  | .mk fields f wild =>
      max (fields.attach.sup fun k => ObjectSlot.depth (f k)) (Body.wildDepth wild) + 1

def ObjectSlot.depth : ObjectSlot S → Nat
  | .req t | .optional t => Term.depth t + 1

def Body.wildDepth : Option (Term S) → Nat
  | none => 1
  | some t => Term.depth t + 1

def Term.depthL : List (Term S) → Nat
  | [] => 1
  | t :: ts => max (Term.depth t) (Term.depthL ts)

def Term.depthO : Option (Term S) → Nat
  | none => 1
  | some t => Term.depth t

end

theorem Term.depth_pos (t : Term S) : 0 < Term.depth t := by
  cases t <;> simp [Term.depth]

/-- A list element is no deeper than its list. -/
theorem Term.depth_le_depthL : ∀ {ts : List (Term S)} {t}, t ∈ ts → Term.depth t ≤ Term.depthL ts
  | _ :: _, _, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · simp [Term.depthL]
      · exact le_trans (Term.depth_le_depthL h') (by simp [Term.depthL])

theorem Term.depthO_le : ∀ {tail : Option (Term S)} {t}, t ∈ tail → Term.depth t ≤ Term.depthO tail
  | some _, _, h => by cases h; simp [Term.depthO]

/-- A declared field is strictly shallower than the body — the inequality `sizeOf` cannot give,
    and the reason this measure exists. Stated at `Body`, where it belongs: it is a fact about a
    key set and a function on it, and mentions no `Term` at all. -/
theorem Body.depth_lt_field : ∀ (b : Body S) (k : {k // k ∈ b.fields}),
    ObjectSlot.depth (b.at k) < Body.depth b
  | .mk fields f _, k => by
      have : (fun k => ObjectSlot.depth (f k)) k ≤
          fields.attach.sup fun k => ObjectSlot.depth (f k) :=
        Finset.le_sup (f := fun k => ObjectSlot.depth (f k)) (Finset.mem_attach _ k)
      simp only at this
      simp only [Body.depth, Body.at]
      omega

/-- …and the open block's codec, the other half of the payload. -/
theorem Body.depth_lt_rest : ∀ (b : Body S) {t : Term S}, b.wild = some t →
    Term.depth t < Body.depth b
  | .mk _ _ _, _, h => by
      simp only [Body.wild] at h
      subst h
      simp only [Body.depth, Body.wildDepth]
      omega

/-- The body is strictly shallower than the object term — one layer, by `rfl` on the measure. -/
theorem Term.depth_lt_object_body (b : Body S) : Body.depth b < Term.depth (.object b) := by
  simp only [Term.depth]; omega

/-- A declared field's *layer* against the object's, kept under its old name: every downstream
    citation is of this, and the payload's own version is `Body.depth_lt_field`. -/
theorem Term.depth_lt_object (b : Body S) (k : {k // k ∈ b.fields}) :
    ObjectSlot.depth (b.at k) < Term.depth (.object b) :=
  lt_trans (Body.depth_lt_field b k) (Term.depth_lt_object_body b)

/-- …and the two slot shapes, which is what a proof recursing into a declared slot needs.
    A row that matched `.object (.mk fields f wild)` discharges these with `f k = .req t m` in
    hand: `(Body.mk fields f wild).at k` is `f k` by `rfl`, so `assumption` closes it.

    so the `req` lemma covers both and the third one is gone rather than renamed. -/
theorem Term.depth_lt_object_req {b : Body S} (k : {k // k ∈ b.fields}) {t : Term S}
    (h : b.at k = .req t) : Term.depth t < Term.depth (.object b) := by
  have h1 := Term.depth_lt_object b k
  rw [h] at h1; simp only [ObjectSlot.depth] at h1; omega

theorem Term.depth_lt_object_opt {b : Body S} (k : {k // k ∈ b.fields}) {t : Term S}
    (h : b.at k = .optional t) : Term.depth t < Term.depth (.object b) := by
  have h1 := Term.depth_lt_object b k
  rw [h] at h1; simp only [ObjectSlot.depth] at h1; omega

/-- The open block's codec against the object's layer, for the same reason. -/
theorem Term.depth_lt_object_rest {b : Body S} {t : Term S} (h : b.wild = some t) :
    Term.depth t < Term.depth (.object b) :=
  lt_trans (Body.depth_lt_rest b h) (Term.depth_lt_object_body b)

/-! ## The denotation

**Structural, and there is no fuel.** The recursion under a list needs a list companion, and the
field table passes the recursion applied, through `fieldSem`, so no higher-order argument is left.
The environment `ρ` holds the codec of each bound variable, nearest binder first. -/

/-- A union's member: `μ` when unanimous, else `⊤` (§5 `(union)`). -/
def unanimous {M : Type} [DecidableEq M] : List (Option M) → Option M
  | [] => none
  | μ :: μs => if μs.all (· == μ) then μ else none

/-- The codec an environment gives the variable `i`: the bottom where no binder is. -/
def envAt {V A M : Type} (ρ : List (Codec V A M)) (i : Nat) : Codec V A M := ρ.getD i .empty

section Denote
variable {S : Syn} [Sem S]

mutual

/-- Each term, at its certified combinator. -/
noncomputable def denote : Term S → (ρ : List S.C := []) → S.C
  | .prim g, _ => Sem.ground g
  | .set t, ρ =>
      match Sem.set (S := S) with
      | some L => L.lift (denote t ρ)
      | none => .empty
  | .list pre spread suf, ρ =>
      match Sem.list (S := S) with
      | some L => listCodec L.pV L.pA L.μ (denoteList pre ρ) (denoteOpt spread ρ) (denoteList suf ρ)
      | none => .empty
  -- the caller-side restriction is a `restrict`, the combinator of the `refine` row
  | .held inner outer f g, ρ =>
      ((denote inner ρ).through f g).restrict fun v => ((denote outer ρ).e v).isSome
  | .refine inner p, ρ => (denote inner ρ).restrict (Sem.eval p)
  | .opaq, _ => Sem.top (S := S)
  | .object b, ρ => bodySem b ρ
  | .union opts, ρ => altCodec (denoteList opts ρ) (unanimous (denoteμs opts ρ))
  -- §2's degenerate codec is the bottom exactly: empty domains, and the laws hold vacuously
  | .never, _ => .empty
  | .var i, ρ => envAt ρ i
  -- each input reads the stage of the body that its own depth names
  | .mu b, ρ => muCodec Sem.dV (Sem.dA (S := S)) fun c => denote b (c :: ρ)

/-- The payload's semantics: the slot table and the open block, each through its own
    companion. -/
noncomputable def bodySem : Body S → (ρ : List S.C := []) → S.C
  | .mk fields f wild, ρ =>
      match Sem.map (S := S) with
      | some F => objectCodec F.mV F.mA F.μ ⟨fields, fun k => fieldSem (f k) ρ⟩ (wildSem wild ρ)
      | none => .empty

/-- A field's semantics. A companion of `denote` rather than a function of one, which is what
    removed the fuel. -/
noncomputable def fieldSem : ObjectSlot S → (ρ : List S.C := []) → FieldSem S.V (Sem.A S) (Sem.M S)
  | .req t, ρ => .req (denote t ρ)
  | .optional t, ρ => .opt (denote t ρ)

/-- The open block's semantics. **A body with no open block refuses.** -/
noncomputable def wildSem : Option (Term S) → (ρ : List S.C := []) → RestSem S.V (Sem.A S) (Sem.M S)
  | none, _ => .refuse
  | some t, ρ => .codec (denote t ρ)

/-- The options' codecs, in order. -/
noncomputable def denoteList : List (Term S) → (ρ : List S.C := []) → List S.C
  | [], _ => []
  | t :: ts, ρ => denote t ρ :: denoteList ts ρ

/-- The spread's codec, where there is one. -/
noncomputable def denoteOpt : Option (Term S) → (ρ : List S.C := []) → Option S.C
  | none, _ => none
  | some t, ρ => some (denote t ρ)

/-- The options' members, in order. -/
noncomputable def denoteμs : List (Term S) → (ρ : List S.C := []) → List (Option (Sem.M S))
  | [], _ => []
  | t :: ts, ρ => (denote t ρ).μ :: denoteμs ts ρ

end

/-! ## A term with no variable

A term with no variable reads no binder, so the environment does not change the denotation. -/

mutual

/-- **A term with no variable is closed**: two environments give one codec. -/
theorem denote_closed : ∀ (t : Term S), t.hasVar = false → ∀ ρ ρ' : List S.C,
    denote t ρ = denote t ρ'
  | .prim _, _, _, _ => rfl
  | .opaq, _, _, _ => rfl
  | .never, _, _, _ => rfl
  | .var _, h, _, _ => nomatch h
  | .set t, h, ρ, ρ' => by simp only [denote]; rw [denote_closed t h ρ ρ']
  | .refine t _, h, ρ, ρ' => by simp only [denote]; rw [denote_closed t h ρ ρ']
  | .mu b, h, ρ, ρ' => by
      simp only [denote]
      congr 1
      funext c
      exact denote_closed b h (c :: ρ) (c :: ρ')
  | .held t P _ _, h, ρ, ρ' => by
      simp only [Term.hasVar, Bool.or_eq_false_iff] at h
      simp only [denote]
      rw [denote_closed t h.1 ρ ρ', denote_closed P h.2 ρ ρ']
  | .list pre sp suf, h, ρ, ρ' => by
      simp only [Term.hasVar, Bool.or_eq_false_iff] at h
      simp only [denote]
      rw [denoteList_closed pre h.1.1 ρ ρ', denoteOpt_closed sp h.1.2 ρ ρ',
        denoteList_closed suf h.2 ρ ρ']
  | .object b, h, ρ, ρ' => bodySem_closed b h ρ ρ'
  | .union os, h, ρ, ρ' => by
      simp only [denote]
      rw [denoteList_closed os h ρ ρ', denoteμs_closed os h ρ ρ']

/-- …at a body. -/
theorem bodySem_closed : ∀ (b : Body S), b.hasVar = false → ∀ ρ ρ' : List S.C,
    bodySem b ρ = bodySem b ρ'
  | .mk fields f wild, h, ρ, ρ' => by
      simp only [Body.hasVar, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_exists,
        Bool.not_eq_true] at h
      have hf : (fun k => fieldSem (f k) ρ) = (fun k => fieldSem (f k) ρ') :=
        funext fun k => fieldSem_closed (f k) (h.1 k) ρ ρ'
      simp only [bodySem]
      rw [hf, wildSem_closed wild h.2 ρ ρ']

/-- …at a slot. -/
theorem fieldSem_closed : ∀ (s : ObjectSlot S), s.hasVar = false → ∀ ρ ρ' : List S.C,
    fieldSem s ρ = fieldSem s ρ'
  | .req t, h, ρ, ρ' => by simp only [fieldSem]; rw [denote_closed t h ρ ρ']
  | .optional t, h, ρ, ρ' => by simp only [fieldSem]; rw [denote_closed t h ρ ρ']

/-- …at an open block. -/
theorem wildSem_closed : ∀ (w : Option (Term S)), Term.hasVarO w = false → ∀ ρ ρ' : List S.C,
    wildSem w ρ = wildSem w ρ'
  | none, _, _, _ => rfl
  | some t, h, ρ, ρ' => by simp only [wildSem]; rw [denote_closed t h ρ ρ']

/-- …at a list of terms. -/
theorem denoteList_closed : ∀ (ts : List (Term S)), Term.hasVarL ts = false →
    ∀ ρ ρ' : List S.C, denoteList ts ρ = denoteList ts ρ'
  | [], _, _, _ => rfl
  | t :: ts, h, ρ, ρ' => by
      simp only [Term.hasVarL, Bool.or_eq_false_iff] at h
      simp only [denoteList]
      rw [denote_closed t h.1 ρ ρ', denoteList_closed ts h.2 ρ ρ']

/-- …at an optional term. -/
theorem denoteOpt_closed : ∀ (sp : Option (Term S)), Term.hasVarO sp = false →
    ∀ ρ ρ' : List S.C, denoteOpt sp ρ = denoteOpt sp ρ'
  | none, _, _, _ => rfl
  | some t, h, ρ, ρ' => by simp only [denoteOpt]; rw [denote_closed t h ρ ρ']

/-- …at the members of a list of terms. -/
theorem denoteμs_closed : ∀ (ts : List (Term S)), Term.hasVarL ts = false →
    ∀ ρ ρ' : List S.C, denoteμs ts ρ = denoteμs ts ρ'
  | [], _, _, _ => rfl
  | t :: ts, h, ρ, ρ' => by
      simp only [Term.hasVarL, Bool.or_eq_false_iff] at h
      simp only [denoteμs]
      rw [denote_closed t h.1 ρ ρ', denoteμs_closed ts h.2 ρ ρ']

end

end Denote

/-- The termination argument every `Term.depth` recursion in this development uses, written
    once, for every universe. The goal sets of its users differ, so some alternatives are dead
    at each use. That is what the `unreachableTactic` linter reports at those sites, and it is
    why the option is disabled there rather than the block being specialised per use. -/
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

end Calculus.Alg
