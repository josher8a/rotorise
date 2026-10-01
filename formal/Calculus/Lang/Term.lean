import Calculus.Alg.Containers
import Calculus.Alg.Recursion
import Calculus.Alg.Agree
import Calculus.Alg.Converse
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The term language over a universe signature

A universe is a signature, an orientation, and a meaning. The signature `Sig` holds the
primitives, and the predicates and the adapter generators at each absolute side: the term
language `Term B` reads nothing else, so a term is data that code can compute with. A two-sided
row of a term stores one half at each absolute side. The syntax `Syn` is a signature and an
orientation, and the dual syntax flips the orientation. So the dual term type is the term type.

The meaning `Mean B` holds a carrier at each absolute side, the member of the side `true`, the
codec of each primitive, one former record per container, and the canonical top. The class
`Sem S` holds the meaning of the signature of a universe, and one instance serves every
orientation. The codecs of a universe are the codecs of the meaning at every orientation, and the
readings in the namespace `Syn` read the carriers, the predicates and the depths at the
orientation of the universe. `denote` builds each former from the generic combinators, so a
universe writes no denotation.

A former is an `Option`: a universe without the former denotes the term as the bottom. A
carrier can hold no `Finset` of itself, because the kernel refuses the nested occurrence, so
the set former is a codec transformer with its law, and not a prism.
-/

namespace Calculus.Alg

/-! ## The two halves of a pair

A two-sided row of a term stores one half at each absolute side: `false` and `true`. An
orientation reads the half of each side. -/

/-- The half of a pair of side-indexed values at one absolute side. -/
def half {X : Bool → Type} : (s : Bool) → X false → X true → X s
  | false, a, _ => a
  | true, _, b => b

/-! ## The signature and the universe -/

/-- **The signature of a universe**: the primitives, and the predicates and the adapter
    generators at each absolute side. The term language reads this and nothing else, so a term
    is data that code can compute with. The signature names no orientation. -/
structure Sig where
  Ground : Type
  P : Bool → Type
  G : Bool → Type
  decG : (s : Bool) → DecidableEq (G s)

instance (B : Sig) (s : Bool) : DecidableEq (B.G s) := B.decG s

/-- **The syntax of a universe**: a signature and an orientation. The dual universe keeps the
    signature and flips the orientation, so the dual term type is the term type. -/
structure Syn where
  sig : Sig
  o : Orient

instance : CoeOut Syn Sig := ⟨Syn.sig⟩

/-- **The dual syntax**: the signature, at the dual orientation. -/
abbrev Syn.op (S : Syn) : Syn := ⟨S.sig, S.o.op⟩

/-- **The dual of the dual is the syntax, on the nose.** -/
theorem Syn.op_op (S : Syn) : S.op.op = S := rfl

/-- The primitives of a universe. -/
abbrev Syn.Ground (S : Syn) : Type := S.sig.Ground

/-- The caller-side predicates. -/
abbrev Syn.Pred (S : Syn) : Type := S.sig.P S.o.c

/-- The stored-side predicates. -/
abbrev Syn.PredA (S : Syn) : Type := S.sig.P S.o.s

/-- The caller-side generators of the adapters. -/
abbrev Syn.Gen (S : Syn) : Type := S.sig.G S.o.c

/-- The stored-side generators of the adapters. -/
abbrev Syn.GenA (S : Syn) : Type := S.sig.G S.o.s

/-- **An adapter word**: a word over the signed generators. The sign `true` names the converse
    of the generator, the pair with its two functions swapped. -/
abbrev Word (S : Syn) : Type := List (S.Gen × Bool)

/-- **The involution of a word**: the letters in reverse order, each with its sign flipped. -/
def Word.dagger {S : Syn} (k : Word S) : Word S := k.reverse.map fun x => (x.1, !x.2)

/-! ## The formers

A former of the meaning holds one prism of the carrier, its member, and its depth law. The set
former is a codec transformer over the carrier of the meaning. -/

/-- The set former of a universe: the lift, its law, its agreement one layer down, and each half
    of agreement. -/
structure SetF (V M : Type) (member : V → M) (depth : V → Nat) where
  lift : Codec V M → Codec V M
  lawful : ∀ {c}, Lawful member c → Lawful member (lift c)
  agree : ∀ {d c₁ c₂}, AgreeLe depth d c₁ c₂ → AgreeLe depth (d + 1) (lift c₁) (lift c₂)
  /-- The lift keeps each half of agreement: two sets whose element codecs agree on a half agree
      on that half. -/
  agreeS : ∀ {side : Bool} {c d : Codec V M}, AgreeS side c d → AgreeS side (lift c) (lift d)
  /-- The universe's own obligation on an element. Soundness does not read this field. -/
  elem : Codec V M → Prop
  /-- The held set of a set, from the held set of its element. -/
  held : (V → Prop) → V → Prop
  /-- The member of a set, from the member of its element. -/
  member : M → Option M
  /-- **The lift stamps that member.** The judgement computes a set's member from its element's
      member, so the lift must stamp the same member, or the `⇝` index of the judgement says
      nothing about the codec. -/
  lift_μ : ∀ c, (lift c).μ = c.μ.bind member
  /-- The lift of a codec on its carrier is on its carrier. -/
  carrier : ∀ {c : Codec V M}, Carrier c → Carrier (lift c)
  /-- The lift's held set is inside `held` of any bound on the element's held set. -/
  held_of : ∀ {c : Codec V M} {T : V → Prop}, (∀ v, c.T v → T v) → ∀ v, (lift c).T v → held T v

/-- **The list former of a meaning**: one prism of the carrier, its member, and its depth law. -/
structure ListA (V Mem : Type) (mem : V → Mem) (d : V → Nat) where
  p : Ctor (List V) V
  μ : Mem
  hμ : ∀ y, mem (p.into y) = μ
  d_lt : ∀ xs, ∀ x ∈ xs, d x + 1 ≤ d (p.into xs)

/-- **The keyed-map former of a meaning**: the same four facts onto `MapOf`. -/
structure MapA (V Mem : Type) (mem : V → Mem) (d : V → Nat) where
  m : Ctor (MapOf V) V
  μ : Mem
  hμ : ∀ y, mem (m.into y) = μ
  d_lt : ∀ (x : MapOf V) k, d (x.get k) + 1 ≤ d (m.into x)

/-! ## The meaning -/

/-- **The meaning of a signature**: one carrier, the member of the side `true`, and the codec of
    each part of the signature from the side `false` to the side `true`. A class over the signature, so the dual universe finds the meaning of the universe,
    and a term family carries no meaning. -/
class Mean (B : Sig) where
  /-- The carrier of both sides. -/
  V : Type
  Mem : Type
  mem : V → Mem
  decM : DecidableEq Mem
  ground : B.Ground → Codec V Mem
  lawful_ground : ∀ g, Lawful mem (ground g)
  carrier_ground : ∀ g, Carrier (ground g)
  eval : (s : Bool) → B.P s → V → Bool
  /-- The predicate at each side that admits every element. -/
  truth : (s : Bool) → B.P s
  eval_truth : ∀ s x, eval s (truth s) x = true
  /-- The depth of a datum, which bounds the stage of a recursive codec. -/
  d : V → Nat
  d_pos : ∀ x, 0 < d x
  list : Option (ListA V Mem mem d)
  map : Option (MapA V Mem mem d)
  set : Option (SetF V Mem mem d)



/-- The codecs of a meaning: partial bijections of its carrier, with the member of the meaning. -/
abbrev Mean.C (B : Sig) [Mean B] : Type :=
  Codec (Mean.V (B := B)) (Mean.Mem (B := B))

instance Mean.instDecM {B : Sig} [Mean B] : DecidableEq (Mean.Mem (B := B)) := Mean.decM

/-- The predicate of each absolute side is the predicate at that side of a pair. -/
theorem Mean.eval_half {B : Sig} [Mean B] (p : B.P false) (pA : B.P true) :
    ∀ s, Side.elim (Mean.eval false p) (Mean.eval true pA) s = Mean.eval s (half s p pA)
  | false => rfl
  | true => rfl


/-- **The meaning of a universe**: the meaning of its signature. One instance serves every
    orientation, so the dual universe finds the meaning of the universe, and a lemma finds its
    universe by unification before the instance search. -/
class Sem (S : Syn) where
  mean : Mean S.sig

/-- A meaning of a signature is a meaning of the signature at every orientation. -/
instance Sem.ofMean (B : Sig) (o : Orient) [m : Mean B] : Sem ⟨B, o⟩ := ⟨m⟩

/-- The meaning of the signature of a universe. -/
instance (priority := low) Sem.toMean (S : Syn) [h : Sem S] : Mean S.sig := h.mean

/-! ## The meaning read at a universe

The codecs, the top and the member are the meaning itself, at every orientation, and a universe
reads its formers from the meaning (`Mean.list`, `Mean.map`, `Mean.set`). The predicates and the
depths are read at the orientation of the universe: the analyses read a codec at its caller
side. -/

namespace Syn

section
variable (S : Syn) [Sem S]

/-- The carrier of a universe: the one carrier of its meaning. -/
abbrev V : Type := Mean.V (B := S.sig)

/-- The member of a universe: the member of its meaning. -/
abbrev M : Type := Mean.Mem (B := S.sig)

/-- The codecs of a universe: the codecs of its meaning, at every orientation. -/
abbrev C : Type := Mean.C S.sig
end

variable {S : Syn} [Sem S]

/-- The codec of a primitive. -/
abbrev ground (g : S.Ground) : S.C := Mean.ground g

/-- The meaning of a caller-side predicate. -/
abbrev eval : S.Pred → S.V → Bool := Mean.eval S.o.c

/-- The meaning of a stored-side predicate. -/
abbrev evalA : S.PredA → S.V → Bool := Mean.eval S.o.s

/-- The caller-side predicate that admits every value. -/
abbrev truth : S.Pred := Mean.truth S.o.c

/-- The caller-side truth admits every value. -/
theorem eval_truth (v : S.V) : Syn.eval Syn.truth v = true := Mean.eval_truth S.o.c v

/-- The stored-side predicate that admits every attribute. -/
abbrev truthA : S.PredA := Mean.truth S.o.s

/-- The stored-side truth admits every attribute. -/
theorem evalA_truthA (a : S.V) : Syn.evalA Syn.truthA a = true := Mean.eval_truth S.o.s a

/-- The depth of a datum. -/
abbrev d : S.V → Nat := Mean.d

/-- A datum has a positive depth. -/
theorem d_pos (v : S.V) : 0 < Syn.d v := Mean.d_pos v

/-- **The top of a universe is the identity codec of its carrier**: it holds every datum and
    sends each datum to itself, so a codec below it is a partial identity. -/
abbrev top : S.C := idCodec

end Syn

/-! ## The tables of adapters

A table gives each generator of one absolute side its entry function and its exit function. A
universe holds the table of its caller side and the table of its stored side. The denotation
reads the tables at the absolute sides, so the dual universe reads the two tables swapped and
denotes each term by the same codec. -/

/-- **A table of adapters at an absolute side**: the entry function and the exit function of each
    generator of the side. -/
abbrev TableAt (B : Sig) [Mean B] (s : Bool) : Type :=
  B.G s → (Mean.V (B := B) → Mean.V (B := B)) × (Mean.V (B := B) → Mean.V (B := B))

/-- **A table of adapters of a universe**: the table at its caller side. The table of the dual
    universe is the table at the stored side. `denote` reads a table as it reads the environment
    of the bound variables. -/
abbrev Table (S : Syn) [Sem S] : Type := TableAt S.sig S.o.c

section Tables
variable {B : Sig} [Mean B] {s : Bool}

/-- The pair of one signed generator: the converse swaps the two functions. -/
def TableAt.letter (α : TableAt B s) (x : B.G s × Bool) :
    (Mean.V (B := B) → Mean.V (B := B)) × (Mean.V (B := B) → Mean.V (B := B)) :=
  if x.2 then ((α x.1).2, (α x.1).1) else α x.1

/-- **The pair of a word**: the empty word is the identity, and a word composes its letters,
    the first letter outermost on the caller side. -/
def TableAt.word (α : TableAt B s) : List (B.G s × Bool) →
    (Mean.V (B := B) → Mean.V (B := B)) × (Mean.V (B := B) → Mean.V (B := B))
  | [] => (id, id)
  | x :: k => ((α.letter x).1 ∘ (α.word k).1, (α.word k).2 ∘ (α.letter x).2)

/-- **A word of two words is the composite of the two pairs.** -/
theorem TableAt.word_append (α : TableAt B s) (k k' : List (B.G s × Bool)) :
    α.word (k ++ k') = ((α.word k).1 ∘ (α.word k').1, (α.word k').2 ∘ (α.word k).2) := by
  induction k with
  | nil => rfl
  | cons x k ih => simp only [List.cons_append, TableAt.word, ih]; rfl

/-- **The tables at each absolute side**, from the table at the caller side of an orientation
    and the table at its stored side. -/
abbrev tables (o : Orient) (α : TableAt B o.c) (β : TableAt B o.s) : (s : Bool) → TableAt B s :=
  Orient.place o α β

end Tables

/-- **The dagger law**: the pair of the involution of a word is the pair of the word, swapped. -/
theorem Table.word_dagger {S : Syn} [Sem S] (α : Table S) (k : Word S) :
    α.word k.dagger = ((α.word k).2, (α.word k).1) := by
  induction k with
  | nil => rfl
  | cons x k ih =>
      have hx : α.word [(x.1, !x.2)] = ((α.letter x).2, (α.letter x).1) := by
        obtain ⟨a, b⟩ := x
        cases b <;> rfl
      simp only [Word.dagger, List.reverse_cons, List.map_append] at ih ⊢
      rw [TableAt.word_append, ih]
      simp only [List.map_cons, List.map_nil, hx, TableAt.word]

mutual

inductive Term (S : Sig) where
  /-- §3's ground rules, as one row: a primitive of the universe. A universe names its primitives
      (`Syn.Ground`) and the codec of each (`Mean.ground`). -/
  | prim (g : S.Ground)
  /-- §3 `(set)`: the finite-powerset lift of an element term. A lawful element gives a lawful
      set (`lawful_setCodec`), and that law reads nothing about the element's base.

      **The DynamoDB set rules are not structure here.** That a stored set holds elements of one
      member of `S`, `N` or `B` is the store universe's rule, and `Obligations` states it as
      `SetElem`, the way `(union)`'s compatibility is stated. The three element types and the
      absent empty set are the carrier's (`Value.strSet`, `numSet`, `binSet`). So a restricted
      element, a literal element and an adapter element are each spelled at the element:
      `set(refine(string, q))`, `set(literal k v)` and `set(held number string k)`. -/
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
  /-- §3 `(held)`: an adapter at one absolute side `s`, and a restriction of that side. `outer`
      restricts the side `s` by its domain at `s`, and the word `k₀ :: k` only transforms. A table
      gives each word its two functions, so two `held`s of one word carry one pair. The other side
      has no adapter and no restriction.

      **A state with no adapter has no representation.** The word is not empty, and a restriction
      with no adapter is a `refine`. A side whose signature names no generator has no `held` at
      that side. A two-sided adapter is two nested `held`s (`held1_nest`). -/
  | held     (s : Bool) (inner : Term S) (outer : Term S) (k₀ : S.G s × Bool)
      (k : List (S.G s × Bool))
  /-- §3 `(refine)`: the restriction of each side by a predicate of that side. -/
  | refine   (inner : Term S) (p : S.P false) (pA : S.P true)
  /-- §3 `(opaque)`: the universal sum, which each universe denotes by its top. -/
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
      `mu b` itself. The name is not rec, which the recursor holds. `denote` reads each input at
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
inductive Body (S : Sig) where
  | mk (fields : Finset String) (f : {k // k ∈ fields} → ObjectSlot S) (wild : Option (Term S))

/-- §4's current-schema slot. A required name is required on both current-schema sides. -/
inductive ObjectSlot (S : Sig) where
  | req      (t : Term S)
  | optional (t : Term S)

end

variable {S : Sig}

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
  | .refine t _ _ => Term.use i t
  | .held _ t P _ _ => useHeld (max (Term.use i t) (Term.use i P))
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
  | .refine t _ _ => Term.guarded t
  | .held _ t P _ _ => Term.guarded t && Term.guarded P
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
  | .refine t _ _ | .mu t | .set t => Term.hasVar t
  | .held _ t P _ _ => Term.hasVar t || Term.hasVar P
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

mutual
/-- **Whether a `held` occurs in the term.** A variable is not a `held`. A term is held-free
    (`HF`) where this test answers `false`. -/
def hasHeld : Term S → Bool
  | .held _ _ _ _ _ => true
  | .refine t _ _ => hasHeld t
  | .mu b => hasHeld b
  | .list pre sp suf => hasHeldL pre || hasHeldO sp || hasHeldL suf
  | .object b => hasHeldB b
  | .union os => hasHeldL os
  | .set t => hasHeld t
  | .prim _ | .opaq | .never | .var _ => false
/-- …in a list. -/
def hasHeldL : List (Term S) → Bool
  | [] => false
  | t :: ts => hasHeld t || hasHeldL ts
/-- …in an optional term. -/
def hasHeldO : Option (Term S) → Bool
  | none => false
  | some t => hasHeld t
/-- …in a body. -/
def hasHeldB : Body S → Bool
  | .mk fs f w => decide (∃ k : {k // k ∈ fs}, hasHeldS (f k) = true) || hasHeldO w
/-- …in a slot. -/
def hasHeldS : ObjectSlot S → Bool
  | .req t => hasHeld t
  | .optional t => hasHeld t
end

/-! ## A structural measure on terms

`denote` recurses structurally and needs no measure. The **proofs** do: `soundness` recurses
on the derivation, and `Typed` is a `Prop`-valued mutual family with no `.brecOn`, so it has to
recurse on the term instead — and `sizeOf` cannot serve, because `Term.object`'s field table is a
*function* and `sizeOf` is blind to functions (`sizeOf f = 0`).

This is the measure that sees through it, and it is not a new idea: it is exactly the shape
`Attr.depth` in `Recursion.lean` uses — `attach.sup` over the key set where a list would
fold. What matters is that it is **derived from the term** rather than supplied by a caller, so it
appears in no statement, no `Obligations`, and no rule. That is the whole difference between this
and the fuel parameter it replaces. -/

mutual

def Term.depth : Term S → Nat
  | .prim _ | .opaq | .never | .var _ => 1
  | .mu t => Term.depth t + 1
  | .set t => Term.depth t + 1
  | .held _ t P _ _ => max (Term.depth t) (Term.depth P) + 1
  | .refine t _ _ => Term.depth t + 1
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
def envAt {V M : Type} (ρ : List (Codec V M)) (i : Nat) : Codec V M := ρ.getD i .empty

section DenoteAbs
variable {B : Sig} [Mean B] (τ : (s : Bool) → TableAt B s)

mutual

/-- **Each term, at its certified combinator**, over the tables of each absolute side. The
    denotation reads no orientation: each former reads its one prism, and a two-sided row stores
    each half at its absolute side. -/
noncomputable def denoteAbs : Term B → (ρ : List (Mean.C B) := []) → Mean.C B
  | .prim g, _ => Mean.ground g
  | .set t, ρ =>
      match Mean.set (B := B) with
      | some L => L.lift (denoteAbs t ρ)
      | none => .empty
  | .list pre spread suf, ρ =>
      match Mean.list (B := B) with
      | some L => listCodec L.p L.μ (denoteListAbs pre ρ) (denoteOptAbs spread ρ)
          (denoteListAbs suf ρ)
      | none => .empty
  -- the side `s` reads its outer, and its word from its own table
  | .held s inner outer k₀ k, ρ =>
      held1 s (denoteAbs inner ρ) (denoteAbs outer ρ) ((τ s).word (k₀ :: k))
  | .refine inner p pA, ρ => refine2 (denoteAbs inner ρ) (Mean.eval false p) (Mean.eval true pA)
  | .opaq, _ => idCodec
  | .object b, ρ => bodySemAbs b ρ
  | .union opts, ρ => altCodec (denoteListAbs opts ρ) (unanimous (denoteμsAbs opts ρ))
  -- §2's degenerate codec is the bottom exactly: empty domains, and the laws hold vacuously
  | .never, _ => .empty
  | .var i, ρ => envAt ρ i
  -- each input reads the stage of the body that its own depth names
  | .mu b, ρ => muCodec Mean.d fun c => denoteAbs b (c :: ρ)

/-- The payload's semantics: the slot table and the open block, each through its own
    companion. -/
noncomputable def bodySemAbs : Body B → (ρ : List (Mean.C B) := []) → Mean.C B
  | .mk fields f wild, ρ =>
      match Mean.map (B := B) with
      | some F =>
          objectCodec F.m F.μ ⟨fields, fun k => fieldSemAbs (f k) ρ⟩
            (wildSemAbs wild ρ)
      | none => .empty

/-- A field's semantics. A companion of `denoteAbs` rather than a function of one, which is what
    removed the fuel. -/
noncomputable def fieldSemAbs : ObjectSlot B → (ρ : List (Mean.C B) := []) →
    FieldSem (Mean.V (B := B)) (Mean.Mem (B := B))
  | .req t, ρ => .req (denoteAbs t ρ)
  | .optional t, ρ => .opt (denoteAbs t ρ)

/-- The open block's semantics. **A body with no open block refuses.** -/
noncomputable def wildSemAbs : Option (Term B) → (ρ : List (Mean.C B) := []) →
    RestSem (Mean.V (B := B)) (Mean.Mem (B := B))
  | none, _ => .refuse
  | some t, ρ => .codec (denoteAbs t ρ)

/-- The options' codecs, in order. -/
noncomputable def denoteListAbs : List (Term B) → (ρ : List (Mean.C B) := []) → List (Mean.C B)
  | [], _ => []
  | t :: ts, ρ => denoteAbs t ρ :: denoteListAbs ts ρ

/-- The spread's codec, where there is one. -/
noncomputable def denoteOptAbs : Option (Term B) → (ρ : List (Mean.C B) := []) →
    Option (Mean.C B)
  | none, _ => none
  | some t, ρ => some (denoteAbs t ρ)

/-- The options' members, in order. -/
noncomputable def denoteμsAbs : List (Term B) → (ρ : List (Mean.C B) := []) →
    List (Option (Mean.Mem (B := B)))
  | [], _ => []
  | t :: ts, ρ => (denoteAbs t ρ).μ :: denoteμsAbs ts ρ

end

/-! ## A term with no variable

A term with no variable reads no binder, so the environment does not change the denotation. -/

variable {τ}

mutual

/-- **A term with no variable is closed**: two environments give one codec. -/
theorem denoteAbs_closed : ∀ (t : Term B), t.hasVar = false → ∀ ρ ρ' : List (Mean.C B),
    denoteAbs τ t ρ = denoteAbs τ t ρ'
  | .prim _, _, _, _ => rfl
  | .opaq, _, _, _ => rfl
  | .never, _, _, _ => rfl
  | .var _, h, _, _ => nomatch h
  | .set t, h, ρ, ρ' => by simp only [denoteAbs]; rw [denoteAbs_closed t h ρ ρ']
  | .refine t _ _, h, ρ, ρ' => by simp only [denoteAbs]; rw [denoteAbs_closed t h ρ ρ']
  | .mu b, h, ρ, ρ' => by
      simp only [denoteAbs]
      congr 1
      funext c
      exact denoteAbs_closed b h (c :: ρ) (c :: ρ')
  | .held _ t P _ _, h, ρ, ρ' => by
      simp only [Term.hasVar, Bool.or_eq_false_iff] at h
      simp only [denoteAbs]
      rw [denoteAbs_closed t h.1 ρ ρ', denoteAbs_closed P h.2 ρ ρ']
  | .list pre sp suf, h, ρ, ρ' => by
      simp only [Term.hasVar, Bool.or_eq_false_iff] at h
      simp only [denoteAbs]
      rw [denoteListAbs_closed pre h.1.1 ρ ρ', denoteOptAbs_closed sp h.1.2 ρ ρ',
        denoteListAbs_closed suf h.2 ρ ρ']
  | .object b, h, ρ, ρ' => bodySemAbs_closed b h ρ ρ'
  | .union os, h, ρ, ρ' => by
      simp only [denoteAbs]
      rw [denoteListAbs_closed os h ρ ρ', denoteμsAbs_closed os h ρ ρ']

/-- …at a body. -/
theorem bodySemAbs_closed : ∀ (b : Body B), b.hasVar = false → ∀ ρ ρ' : List (Mean.C B),
    bodySemAbs τ b ρ = bodySemAbs τ b ρ'
  | .mk fields f wild, h, ρ, ρ' => by
      simp only [Body.hasVar, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_exists, Bool.not_eq_true] at h
      have hf : (fun k => fieldSemAbs τ (f k) ρ) = (fun k => fieldSemAbs τ (f k) ρ') :=
        funext fun k => fieldSemAbs_closed (f k) (h.1 k) ρ ρ'
      simp only [bodySemAbs]
      rw [hf, wildSemAbs_closed wild h.2 ρ ρ']

/-- …at a slot. -/
theorem fieldSemAbs_closed : ∀ (s : ObjectSlot B), s.hasVar = false →
    ∀ ρ ρ' : List (Mean.C B), fieldSemAbs τ s ρ = fieldSemAbs τ s ρ'
  | .req t, h, ρ, ρ' => by simp only [fieldSemAbs]; rw [denoteAbs_closed t h ρ ρ']
  | .optional t, h, ρ, ρ' => by simp only [fieldSemAbs]; rw [denoteAbs_closed t h ρ ρ']

/-- …at an open block. -/
theorem wildSemAbs_closed : ∀ (w : Option (Term B)), Term.hasVarO w = false →
    ∀ ρ ρ' : List (Mean.C B), wildSemAbs τ w ρ = wildSemAbs τ w ρ'
  | none, _, _, _ => rfl
  | some t, h, ρ, ρ' => by simp only [wildSemAbs]; rw [denoteAbs_closed t h ρ ρ']

/-- …at a list of terms. -/
theorem denoteListAbs_closed : ∀ (ts : List (Term B)), Term.hasVarL ts = false →
    ∀ ρ ρ' : List (Mean.C B), denoteListAbs τ ts ρ = denoteListAbs τ ts ρ'
  | [], _, _, _ => rfl
  | t :: ts, h, ρ, ρ' => by
      simp only [Term.hasVarL, Bool.or_eq_false_iff] at h
      simp only [denoteListAbs]
      rw [denoteAbs_closed t h.1 ρ ρ', denoteListAbs_closed ts h.2 ρ ρ']

/-- …at an optional term. -/
theorem denoteOptAbs_closed : ∀ (sp : Option (Term B)), Term.hasVarO sp = false →
    ∀ ρ ρ' : List (Mean.C B), denoteOptAbs τ sp ρ = denoteOptAbs τ sp ρ'
  | none, _, _, _ => rfl
  | some t, h, ρ, ρ' => by simp only [denoteOptAbs]; rw [denoteAbs_closed t h ρ ρ']

/-- …at the members of a list of terms. -/
theorem denoteμsAbs_closed : ∀ (ts : List (Term B)), Term.hasVarL ts = false →
    ∀ ρ ρ' : List (Mean.C B), denoteμsAbs τ ts ρ = denoteμsAbs τ ts ρ'
  | [], _, _, _ => rfl
  | t :: ts, h, ρ, ρ' => by
      simp only [Term.hasVarL, Bool.or_eq_false_iff] at h
      simp only [denoteμsAbs]
      rw [denoteAbs_closed t h.1 ρ ρ', denoteμsAbs_closed ts h.2 ρ ρ']

end

end DenoteAbs

/-! ## The denotation of a universe

A universe holds the table of its caller side and the table of its stored side. Its denotation is
the absolute denotation at the tables of each absolute side, so the dual universe, with the two
tables swapped, denotes each term by the same codec. -/

section Denote
variable {S : Syn} [Sem S] (α : Table S) (β : Table S.op)

/-- Each term, at its certified combinator. -/
noncomputable abbrev denote (t : Term S) (ρ : List S.C := []) : S.C :=
  denoteAbs (tables S.o α β) t ρ

/-- The payload's semantics. -/
noncomputable abbrev bodySem (b : Body S) (ρ : List S.C := []) : S.C :=
  bodySemAbs (tables S.o α β) b ρ

/-- A field's semantics. -/
noncomputable abbrev fieldSem (s : ObjectSlot S) (ρ : List S.C := []) :
    FieldSem (Mean.V (B := S.sig)) S.M :=
  fieldSemAbs (tables S.o α β) s ρ

/-- The open block's semantics. -/
noncomputable abbrev wildSem (w : Option (Term S)) (ρ : List S.C := []) :
    RestSem (Mean.V (B := S.sig)) S.M :=
  wildSemAbs (tables S.o α β) w ρ

/-- The options' codecs, in order. -/
noncomputable abbrev denoteList (ts : List (Term S)) (ρ : List S.C := []) : List S.C :=
  denoteListAbs (tables S.o α β) ts ρ

/-- The spread's codec, where there is one. -/
noncomputable abbrev denoteOpt (sp : Option (Term S)) (ρ : List S.C := []) : Option S.C :=
  denoteOptAbs (tables S.o α β) sp ρ

/-- The options' members, in order. -/
noncomputable abbrev denoteμs (ts : List (Term S)) (ρ : List S.C := []) : List (Option S.M) :=
  denoteμsAbs (tables S.o α β) ts ρ

/-- The options of no term are no codecs. -/
@[simp] theorem denoteList_nil (ρ : List S.C) : denoteList α β [] ρ = [] := rfl

/-- The options of a list of terms are the codec of the head and the options of the tail. -/
@[simp] theorem denoteList_cons (t : Term S) (ts : List (Term S)) (ρ : List S.C) :
    denoteList α β (t :: ts) ρ = denote α β t ρ :: denoteList α β ts ρ := rfl

/-- No spread has no codec. -/
@[simp] theorem denoteOpt_none (ρ : List S.C) : denoteOpt α β none ρ = none := rfl

/-- A spread has the codec of its term. -/
@[simp] theorem denoteOpt_some (t : Term S) (ρ : List S.C) :
    denoteOpt α β (some t) ρ = some (denote α β t ρ) := rfl

variable {α β}

/-- **A term with no variable is closed**: two environments give one codec. -/
theorem denote_closed (t : Term S) (h : t.hasVar = false) (ρ ρ' : List S.C) :
    denote α β t ρ = denote α β t ρ' :=
  denoteAbs_closed t h ρ ρ'

/-! ## The host rows

At the host orientation, the caller half of a two-sided row is the half `false`, and the stored
half is the half `true`. Where the stored predicate is the truth, the two-sided `refine` is the
one-sided row. A `held` at the side `false` is the host `held`. -/

section Host
variable {B : Sig} [Mean B] {α : Table ⟨B, .host⟩} {β : Table (Syn.op ⟨B, .host⟩)}

/-- **The host `refine` is the caller-side restriction.** -/
theorem denote_refine_host (t : Term B) (p : B.P false) (ρ : List (Syn.C ⟨B, .host⟩)) :
    denote α β (S := ⟨B, .host⟩) (.refine t p (Mean.truth true)) ρ =
      (denote α β t ρ).restrict (Mean.eval false p) := by
  have h : Mean.eval (B := B) true (Mean.truth true) = fun _ => true := funext (Mean.eval_truth true)
  exact congrArg (refine2 (denote α β t ρ) (Mean.eval false p)) h

/-- **The host `held` is the caller-side adapter, restricted by the outer.** -/
theorem denote_held_host (t P : Term B) (k₀ : B.G false × Bool) (k : List (B.G false × Bool))
    (ρ : List (Syn.C ⟨B, .host⟩)) :
    denote α β (S := ⟨B, .host⟩) (.held false t P k₀ k) ρ =
      ((denote α β t ρ).through (α.word (k₀ :: k)).1 (α.word (k₀ :: k)).2).restrict
        fun v => ((denote α β P ρ).e v).isSome :=
  held1_host _ _ _

end Host

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
