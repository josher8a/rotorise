import Calculus.Alg.Containers
import Calculus.Alg.Recursion
import Calculus.Alg.Agree
import Calculus.Alg.Converse
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The universe signature and its meaning

A universe is a signature, an orientation, and a meaning. The signature `Sig` holds the
primitives, and the predicates and the adapter generators at each absolute side: the term
language `Scoped.Term B` reads nothing else, so a term is data that code can compute with. A two-sided
row of a term stores one half at each absolute side. The syntax `Syn` is a signature and an
orientation, and the dual syntax flips the orientation. So the dual term type is the term type.

The meaning `Mean B` holds a carrier at each absolute side, the member of the side `true`, the
codec of each primitive, one former record per container, and the canonical top. The class
`Sem S` holds the meaning of the signature of a universe, and one instance serves every
orientation. The codecs of a universe are the codecs of the meaning at every orientation, and the
readings in the namespace `Syn` read the carriers, the predicates and the depths at the
orientation of the universe. `Scoped.TOp.run` builds each former from the generic combinators,
so a universe writes no denotation.

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

/-- **The signature of a universe**: the primitives, the predicates and the adapter generators at
    each absolute side, and the older readers. The term language reads this and nothing else, so a
    term is data that code can compute with. The signature names no orientation. -/
structure Sig where
  Ground : Type
  P : Bool → Type
  G : Bool → Type
  decG : (s : Bool) → DecidableEq (G s)
  /-- The older readers of `legacy`. A reader is caller code, so the term carries it as data and
      the meaning reads it; no analysis looks inside it. -/
  R : Type
  /-- The constants a `fill` reads at an absent name. -/
  K : Type

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

/-- **The list former of a meaning**: one summand of the carrier, and its depth law. -/
structure ListA (V Mem : Type) (mem : V → Mem) (d : V → Nat) extends Summand (List V) V Mem mem where
  d_lt : ∀ xs, ∀ x ∈ xs, d x + 1 ≤ d (p.into xs)

/-- **The keyed-map former of a meaning**: one summand onto `MapOf`, and its depth law. -/
structure MapA (V Mem : Type) (mem : V → Mem) (d : V → Nat) extends Summand (MapOf V) V Mem mem where
  d_lt : ∀ (x : MapOf V) k, d (x.get k) + 1 ≤ d (p.into x)

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
  /-- The meaning of an older reader: an attribute to the value it reads, where it reads one. -/
  read : B.R → V → Option V
  /-- The value of a constant. -/
  const : B.K → V



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
    universe is the table at the stored side. `Scoped.TOp.run` reads the table at each `held`. -/
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

/-- A union's member: `μ` when unanimous, else `⊤` (the rule `(union)`). -/
def unanimous {M : Type} [DecidableEq M] : List (Option M) → Option M
  | [] => none
  | μ :: μs => if μs.all (· == μ) then μ else none

end Calculus.Alg
