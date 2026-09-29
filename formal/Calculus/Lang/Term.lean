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
orientation. Each reading in the namespace `Syn` is the meaning at the orientation of the
universe. `denote` builds each former from the generic combinators, so a universe writes no
denotation.

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

/-- The half of a pair of one type at one absolute side. -/
abbrev half2 {Z : Type} (s : Bool) (a b : Z) : Z := half (X := fun _ => Z) s a b

/-- A function of the half is the half of the function. -/
theorem half2_apply {Z W : Type} (f : Z → W) (s : Bool) (a b : Z) :
    f (half2 s a b) = half2 s (f a) (f b) := by
  cases s <;> rfl

/-- The half of two functions, at an argument, is the half of the two values. -/
theorem half2_app {Z W : Type} (s : Bool) (f g : Z → W) (x : Z) :
    half2 s f g x = half2 s (f x) (g x) := by
  cases s <;> rfl

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

/-- The half of a pair of words at one absolute side. -/
abbrev halfK {B : Sig} (s : Bool) (k : List (B.G false × Bool)) (kA : List (B.G true × Bool)) :
    List (B.G s × Bool) :=
  half (X := fun s => List (B.G s × Bool)) s k kA

/-! ## The member at an absolute side

The stored side `true` of the host holds the member of the universe. The side `false` names no
member. So the member reads by the stored side of an orientation. -/

/-- The member type at an absolute side. -/
abbrev MemAt (Mem : Type) : Bool → Type
  | false => Unit
  | true => Mem

/-- The member function at an absolute side. -/
def memAt {Car : Bool → Type} {Mem : Type} (mem : Car true → Mem) :
    (s : Bool) → Car s → MemAt Mem s
  | false, _ => ()
  | true, a => mem a

/-- A member of the universe, read at an absolute side. -/
def μAt {Mem : Type} : (s : Bool) → Mem → MemAt Mem s
  | false, _ => ()
  | true, m => m

/-- Equality of members is decidable at each side. -/
def decAt {Mem : Type} (dec : DecidableEq Mem) : (s : Bool) → DecidableEq (MemAt Mem s)
  | false => fun _ _ => isTrue rfl
  | true => dec

/-! ## The formers

A former of the meaning holds one prism per absolute side and the member at the side `true`. An
orientation reads the former as the one-sided record below. -/

/-- The list former at an orientation: a prism from each carrier onto `List`, the member that
    the stored side stamps, and the fact that an element is one layer below its list. -/
structure ListF (V A M : Type) (member : A → M) (dV : V → Nat) (dA : A → Nat) where
  pV : Ctor (List V) V
  pA : Ctor (List A) A
  μ : M
  hμ : ∀ y, member (pA.into y) = μ
  dV_lt : ∀ vs, ∀ x ∈ vs, dV x + 1 ≤ dV (pV.into vs)
  dA_lt : ∀ as, ∀ x ∈ as, dA x + 1 ≤ dA (pA.into as)

/-- The keyed-map former at an orientation: the same four facts onto `MapOf`. -/
structure MapF (V A M : Type) (member : A → M) (dV : V → Nat) (dA : A → Nat) where
  mV : Ctor (MapOf V) V
  mA : Ctor (MapOf A) A
  μ : M
  hμ : ∀ y, member (mA.into y) = μ
  dV_lt : ∀ (m : MapOf V) k, dV (m.get k) + 1 ≤ dV (mV.into m)
  dA_lt : ∀ (m : MapOf A) k, dA (m.get k) + 1 ≤ dA (mA.into m)

/-- The set former of a universe: the lift, its law, its agreement one layer down, and each half
    of agreement. -/
structure SetF (V A M : Type) (member : A → M) (dV : V → Nat) (dA : A → Nat) where
  lift : Codec V A M → Codec V A M
  lawful : ∀ {c}, Lawful member c → Lawful member (lift c)
  agree : ∀ {d c₁ c₂}, AgreeLe dV dA d c₁ c₂ → AgreeLe dV dA (d + 1) (lift c₁) (lift c₂)
  /-- The lift keeps each half of agreement: two sets whose element codecs agree on a half agree
      on that half. -/
  agreeS : ∀ {side : Bool} {c d : Codec V A M}, AgreeS side c d → AgreeS side (lift c) (lift d)
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

section Formers
variable {V A M : Type}

/-- The set former, transported through the converse. The held set, the element obligation and
    the member are the trivial ones: the caller-side held set has no stored-side image. -/
def SetF.op {member : A → M} {dV : V → Nat} {dA : A → Nat} (L : SetF V A M member dV dA) :
    SetF A V Unit (fun _ => ()) dA dV :=
  { lift := fun c => conv (L.lift (unconv c))
    lawful := fun h => Lawful.conv (L.lawful (Lawful.unconv h))
    agree := fun h => ⟨(L.agree ⟨h.p, h.e⟩).p, (L.agree ⟨h.p, h.e⟩).e⟩
    agreeS := fun h => agreeS_conv (L.agreeS (agreeS_unconv h))
    elem := fun _ => True
    held := fun _ _ => True
    member := fun _ => some ()
    carrier := fun _ => carrier_conv _
    held_of := fun _ _ _ => trivial }

end Formers

/-- **The list former of a meaning**: one prism per absolute side, the member at the side `true`,
    and one depth law for both sides. -/
structure ListA (Car : Bool → Type) (Mem : Type) (mem : Car true → Mem)
    (d : (s : Bool) → Car s → Nat) where
  p : (s : Bool) → Ctor (List (Car s)) (Car s)
  μ : Mem
  hμ : ∀ y, mem ((p true).into y) = μ
  d_lt : ∀ s xs, ∀ x ∈ xs, d s x + 1 ≤ d s ((p s).into xs)

/-- **The keyed-map former of a meaning**: the same four facts onto `MapOf`. -/
structure MapA (Car : Bool → Type) (Mem : Type) (mem : Car true → Mem)
    (d : (s : Bool) → Car s → Nat) where
  m : (s : Bool) → Ctor (MapOf (Car s)) (Car s)
  μ : Mem
  hμ : ∀ y, mem ((m true).into y) = μ
  d_lt : ∀ s (x : MapOf (Car s)) k, d s (x.get k) + 1 ≤ d s ((m s).into x)

section Readings
variable {Car : Bool → Type} {Mem : Type} {mem : Car true → Mem} {d : (s : Bool) → Car s → Nat}

/-- **The member law of a former, at each side**, as one statement for every payload: the
    stored prism stamps the member, and the value prism stamps the unit. -/
theorem memAt_into {X : Bool → Type} (p : (s : Bool) → Ctor (X s) (Car s)) {μ : Mem}
    (h : ∀ y, mem ((p true).into y) = μ) : ∀ s y, memAt mem s ((p s).into y) = μAt s μ
  | false, _ => rfl
  | true, y => h y

/-- **The list former read at an orientation.** -/
def ListA.at (L : ListA Car Mem mem d) (o : Orient) :
    ListF (Car o.c) (Car o.s) (MemAt Mem o.s) (memAt mem o.s) (d o.c) (d o.s) :=
  { pV := L.p o.c, pA := L.p o.s, μ := μAt o.s L.μ
    hμ := memAt_into (X := fun s => List (Car s)) L.p L.hμ o.s
    dV_lt := L.d_lt o.c, dA_lt := L.d_lt o.s }

/-- **The keyed-map former read at an orientation.** -/
def MapA.at (F : MapA Car Mem mem d) (o : Orient) :
    MapF (Car o.c) (Car o.s) (MemAt Mem o.s) (memAt mem o.s) (d o.c) (d o.s) :=
  { mV := F.m o.c, mA := F.m o.s, μ := μAt o.s F.μ
    hμ := memAt_into (X := fun s => MapOf (Car s)) F.m F.hμ o.s
    dV_lt := F.d_lt o.c, dA_lt := F.d_lt o.s }

/-- **The set former read at an orientation.** The set former is a codec transformer at the
    host, so the dual reads the transformer through the converse. -/
def setAt (L : SetF (Car false) (Car true) Mem mem (d false) (d true)) :
    (o : Orient) → SetF (Car o.c) (Car o.s) (MemAt Mem o.s) (memAt mem o.s) (d o.c) (d o.s)
  | ⟨(false, true), _⟩ => L
  | ⟨(true, false), _⟩ => SetF.op L
  | ⟨(false, false), h⟩ => absurd rfl h
  | ⟨(true, true), h⟩ => absurd rfl h

/-- **A host codec read at an orientation**: the codec at the host, and its converse at the
    dual. -/
def readC : (o : Orient) → Codec (Car false) (Car true) Mem → Codec (Car o.c) (Car o.s) (MemAt Mem o.s)
  | ⟨(false, true), _⟩, c => c
  | ⟨(true, false), _⟩, c => conv c
  | ⟨(false, false), h⟩, _ => absurd rfl h
  | ⟨(true, true), h⟩, _ => absurd rfl h

/-- **A lawful host codec is lawful at every orientation.** -/
theorem lawful_readC : ∀ (o : Orient) {c : Codec (Car false) (Car true) Mem}, Lawful mem c →
    Lawful (memAt mem o.s) (readC o c)
  | ⟨(false, true), _⟩, _, h => h
  | ⟨(true, false), _⟩, _, h => Lawful.conv h
  | ⟨(false, false), h⟩, _, _ => absurd rfl h
  | ⟨(true, true), h⟩, _, _ => absurd rfl h

/-- A host codec on its carrier is on its carrier at every orientation. -/
theorem carrier_readC : ∀ (o : Orient) {c : Codec (Car false) (Car true) Mem}, Carrier c →
    Carrier (readC o c)
  | ⟨(false, true), _⟩, _, h => h
  | ⟨(true, false), _⟩, c, _ => carrier_conv c
  | ⟨(false, false), h⟩, _, _ => absurd rfl h
  | ⟨(true, true), h⟩, _, _ => absurd rfl h

/-- **A host held set read at an orientation**: the held set at the host, and every value at the
    dual, where the caller-side held set has no stored-side image. -/
def heldAt : (o : Orient) → (Car false → Prop) → Car o.c → Prop
  | ⟨(false, true), _⟩, T => T
  | ⟨(true, false), _⟩, _ => fun _ => True
  | ⟨(false, false), h⟩, _ => absurd rfl h
  | ⟨(true, true), h⟩, _ => absurd rfl h

/-- A bound on the held set of a host codec bounds its reading at every orientation. -/
theorem heldAt_readC : ∀ (o : Orient) {c : Codec (Car false) (Car true) Mem} {T : Car false → Prop},
    (∀ v, c.T v → T v) → ∀ v, (readC o c).T v → heldAt o T v
  | ⟨(false, true), _⟩, _, _, h => h
  | ⟨(true, false), _⟩, _, _, _ => fun _ _ => trivial
  | ⟨(false, false), h⟩, _, _, _ => absurd rfl h
  | ⟨(true, true), h⟩, _, _, _ => absurd rfl h

end Readings

/-! ## The meaning -/

/-- **The meaning of a signature**: a carrier at each absolute side, the member of the side
    `true`, and the codec of each part of the signature from the side `false` to the side
    `true`. A class over the signature, so the dual universe finds the meaning of the universe,
    and a term family carries no meaning. -/
class Mean (B : Sig) where
  Car : Bool → Type
  Mem : Type
  mem : Car true → Mem
  decM : DecidableEq Mem
  ground : B.Ground → Codec (Car false) (Car true) Mem
  lawful_ground : ∀ g, Lawful mem (ground g)
  carrier_ground : ∀ g, Carrier (ground g)
  eval : (s : Bool) → B.P s → Car s → Bool
  /-- The predicate at each side that admits every element. -/
  truth : (s : Bool) → B.P s
  eval_truth : ∀ s x, eval s (truth s) x = true
  d : (s : Bool) → Car s → Nat
  d_pos : ∀ s x, 0 < d s x
  list : Option (ListA Car Mem mem d)
  map : Option (MapA Car Mem mem d)
  set : Option (SetF (Car false) (Car true) Mem mem (d false) (d true))
  /-- The member that the judgement gives a primitive. -/
  groundμ : B.Ground → Option Mem
  top : Codec (Car false) (Car true) Mem
  lawful_top : Lawful mem top
  carrier_top : Carrier top
  /-- The held set that the judgement gives the top, and the top's held set lies inside it. -/
  topHeld : Car false → Prop
  top_held : ∀ v, top.T v → topHeld v

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

Each reading below is the meaning at the orientation of the universe. The caller carrier is the
carrier of the caller side, and the member is the member of the stored side. -/

namespace Syn

section
variable (S : Syn) [Sem S]

/-- The caller carrier of a universe. -/
abbrev V : Type := Mean.Car (B := S.sig) S.o.c

/-- The stored carrier of a universe. -/
abbrev A : Type := Mean.Car (B := S.sig) S.o.s

/-- The member of a universe: the member of its stored side. -/
abbrev M : Type := MemAt (Mean.Mem (B := S.sig)) S.o.s

/-- The codecs of a universe. -/
abbrev C : Type := Codec S.V S.A S.M
end

variable {S : Syn} [Sem S]

/-- The member of a stored element. -/
abbrev member : S.A → S.M := memAt Mean.mem S.o.s

instance decM : DecidableEq S.M := decAt Mean.decM S.o.s

/-- The codec of a primitive. -/
abbrev ground (g : S.Ground) : S.C := readC S.o (Mean.ground g)

/-- The codec of a primitive is lawful at every orientation. -/
theorem lawful_ground (g : S.Ground) : Lawful Syn.member (Syn.ground g) :=
  lawful_readC S.o (Mean.lawful_ground g)

/-- The codec of a primitive is on its carrier at every orientation. -/
theorem carrier_ground (g : S.Ground) : Carrier (Syn.ground g) :=
  carrier_readC S.o (Mean.carrier_ground g)

/-- The meaning of a caller-side predicate. -/
abbrev eval : S.Pred → S.V → Bool := Mean.eval S.o.c

/-- The meaning of a stored-side predicate. -/
abbrev evalA : S.PredA → S.A → Bool := Mean.eval S.o.s

/-- The caller-side predicate that admits every value. -/
abbrev truth : S.Pred := Mean.truth S.o.c

/-- The caller-side truth admits every value. -/
theorem eval_truth (v : S.V) : Syn.eval Syn.truth v = true := Mean.eval_truth S.o.c v

/-- The stored-side predicate that admits every attribute. -/
abbrev truthA : S.PredA := Mean.truth S.o.s

/-- The stored-side truth admits every attribute. -/
theorem evalA_truthA (a : S.A) : Syn.evalA Syn.truthA a = true := Mean.eval_truth S.o.s a

/-- The depth of a caller value. -/
abbrev dV : S.V → Nat := Mean.d S.o.c

/-- The depth of a stored attribute. -/
abbrev dA : S.A → Nat := Mean.d S.o.s

/-- A caller value has a positive depth. -/
theorem dV_pos (v : S.V) : 0 < Syn.dV v := Mean.d_pos S.o.c v

/-- A stored attribute has a positive depth. -/
theorem dA_pos (a : S.A) : 0 < Syn.dA a := Mean.d_pos S.o.s a

/-- The list former of a universe. -/
abbrev list : Option (ListF S.V S.A S.M Syn.member Syn.dV Syn.dA) :=
  (Mean.list (B := S.sig)).map (·.at S.o)

/-- The keyed-map former of a universe. -/
abbrev map : Option (MapF S.V S.A S.M Syn.member Syn.dV Syn.dA) :=
  (Mean.map (B := S.sig)).map (·.at S.o)

/-- The set former of a universe. -/
abbrev set : Option (SetF S.V S.A S.M Syn.member Syn.dV Syn.dA) :=
  (Mean.set (B := S.sig)).map (setAt · S.o)

/-- The member that the judgement gives a primitive. -/
abbrev groundμ (g : S.Ground) : Option S.M := (Mean.groundμ g).map (μAt S.o.s)

/-- The canonical top of a universe. -/
abbrev top : S.C := readC S.o (Mean.top (B := S.sig))

/-- The top is lawful at every orientation. -/
theorem lawful_top : Lawful Syn.member (Syn.top (S := S)) := lawful_readC S.o Mean.lawful_top

/-- The top is on its carrier at every orientation. -/
theorem carrier_top : Carrier (Syn.top (S := S)) := carrier_readC S.o Mean.carrier_top

/-- The held set that the judgement gives the top. -/
abbrev topHeld : S.V → Prop := heldAt S.o (Mean.topHeld (B := S.sig))

/-- The held set of the top lies inside the held set that the judgement gives the top. -/
theorem top_held (v : S.V) : (Syn.top (S := S)).T v → Syn.topHeld v :=
  heldAt_readC S.o Mean.top_held v

end Syn

/-- **A table of adapters**: the caller-side function and the stored-side function of each
    generator. `denote` reads a table as it reads the environment of the bound variables. -/
abbrev Table (S : Syn) [Sem S] : Type := S.Gen → (S.V → S.V) × (S.V → S.V)

/-- The pair of one signed generator: the converse swaps the two functions. -/
def Table.letter {S : Syn} [Sem S] (α : Table S) (x : S.Gen × Bool) : (S.V → S.V) × (S.V → S.V) :=
  if x.2 then ((α x.1).2, (α x.1).1) else α x.1

/-- **The pair of a word**: the empty word is the identity, and a word composes its letters,
    the first letter outermost on the caller side. -/
def Table.word {S : Syn} [Sem S] (α : Table S) : Word S → (S.V → S.V) × (S.V → S.V)
  | [] => (id, id)
  | x :: k => ((α.letter x).1 ∘ (Table.word α k).1, (Table.word α k).2 ∘ (α.letter x).2)

/-- **A word of two words is the composite of the two pairs.** -/
theorem Table.word_append {S : Syn} [Sem S] (α : Table S) (k k' : Word S) :
    α.word (k ++ k') = ((α.word k).1 ∘ (α.word k').1, (α.word k').2 ∘ (α.word k).2) := by
  induction k with
  | nil => rfl
  | cons x k ih => simp only [List.cons_append, Table.word, ih]; rfl

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
      rw [Table.word_append, ih]
      simp only [List.map_cons, List.map_nil, hx, Table.word]

/-- **The top reads every attribute**: the law that makes the top the stored outer that restricts
    nothing. -/
class TopReads (S : Syn) [Sem S] : Prop where
  reads : ∀ a, ((Syn.top (S := S)).p a).isSome = true

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
  /-- §3 `(held)`: a morphism between two restrictions. `outer` restricts the caller side by its
      write domain, and `outerA` restricts the stored side by its read domain. The caller word
      `k` and the stored word `kA` only transform. A table gives each word its two functions, so
      two `held`s of one word carry one pair. A side that states no restriction writes `.opaq`
      as its outer, and a side with no adapter writes the empty word. -/
  | held     (inner : Term S) (outer : Term S) (outerA : Term S) (k : List (S.G false × Bool))
      (kA : List (S.G true × Bool))
  /-- §3 `(refine)`: the restriction of each side by a predicate of that side. -/
  | refine   (inner : Term S) (p : S.P false) (pA : S.P true)
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
  | .held t P PA _ _ => useHeld (max (Term.use i t) (max (Term.use i P) (Term.use i PA)))
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
  | .held t P PA _ _ => Term.guarded t && Term.guarded P && Term.guarded PA
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
  | .held t P PA _ _ => Term.hasVar t || Term.hasVar P || Term.hasVar PA
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
`Value.depth` in `Recursion.lean` uses — `attach.sup` over the key set where a list would
fold. What matters is that it is **derived from the term** rather than supplied by a caller, so it
appears in no statement, no `Obligations`, and no rule. That is the whole difference between this
and the `fuel` parameter it replaces. -/

mutual

def Term.depth : Term S → Nat
  | .prim _ | .opaq | .never | .var _ => 1
  | .mu t => Term.depth t + 1
  | .set t => Term.depth t + 1
  | .held t P PA _ _ => max (Term.depth t) (max (Term.depth P) (Term.depth PA)) + 1
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
def envAt {V A M : Type} (ρ : List (Codec V A M)) (i : Nat) : Codec V A M := ρ.getD i .empty

section Denote
variable {S : Syn} [Sem S] (α : Table S) (β : Table S.op)

mutual

/-- Each term, at its certified combinator. -/
noncomputable def denote : Term S → (ρ : List S.C := []) → S.C
  | .prim g, _ => Syn.ground g
  | .set t, ρ =>
      match Syn.set (S := S) with
      | some L => L.lift (denote t ρ)
      | none => .empty
  | .list pre spread suf, ρ =>
      match Syn.list (S := S) with
      | some L => listCodec L.pV L.pA L.μ (denoteList pre ρ) (denoteOpt spread ρ) (denoteList suf ρ)
      | none => .empty
  -- each side reads its own half, and its own word from its own table
  | .held inner outer outerA k kA, ρ =>
      held2 (denote inner ρ) (half2 S.o.c (denote outer ρ) (denote outerA ρ))
        (half2 S.o.s (denote outer ρ) (denote outerA ρ))
        (α.word (halfK S.o.c k kA)).1 (α.word (halfK S.o.c k kA)).2
        (β.word (halfK S.o.s k kA)).1 (β.word (halfK S.o.s k kA)).2
  | .refine inner p pA, ρ =>
      refine2 (denote inner ρ) (Syn.eval (half S.o.c p pA)) (Syn.evalA (half S.o.s p pA))
  | .opaq, _ => Syn.top (S := S)
  | .object b, ρ => bodySem b ρ
  | .union opts, ρ => altCodec (denoteList opts ρ) (unanimous (denoteμs opts ρ))
  -- §2's degenerate codec is the bottom exactly: empty domains, and the laws hold vacuously
  | .never, _ => .empty
  | .var i, ρ => envAt ρ i
  -- each input reads the stage of the body that its own depth names
  | .mu b, ρ => muCodec Syn.dV (Syn.dA (S := S)) fun c => denote b (c :: ρ)

/-- The payload's semantics: the slot table and the open block, each through its own
    companion. -/
noncomputable def bodySem : Body S → (ρ : List S.C := []) → S.C
  | .mk fields f wild, ρ =>
      match Syn.map (S := S) with
      | some F => objectCodec F.mV F.mA F.μ ⟨fields, fun k => fieldSem (f k) ρ⟩ (wildSem wild ρ)
      | none => .empty

/-- A field's semantics. A companion of `denote` rather than a function of one, which is what
    removed the fuel. -/
noncomputable def fieldSem : ObjectSlot S → (ρ : List S.C := []) → FieldSem S.V (Syn.A S) (Syn.M S)
  | .req t, ρ => .req (denote t ρ)
  | .optional t, ρ => .opt (denote t ρ)

/-- The open block's semantics. **A body with no open block refuses.** -/
noncomputable def wildSem : Option (Term S) → (ρ : List S.C := []) → RestSem S.V (Syn.A S) (Syn.M S)
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
noncomputable def denoteμs : List (Term S) → (ρ : List S.C := []) → List (Option (Syn.M S))
  | [], _ => []
  | t :: ts, ρ => (denote t ρ).μ :: denoteμs ts ρ

end

variable {α β}

/-! ## A term with no variable

A term with no variable reads no binder, so the environment does not change the denotation. -/

mutual

/-- **A term with no variable is closed**: two environments give one codec. -/
theorem denote_closed : ∀ (t : Term S), t.hasVar = false → ∀ ρ ρ' : List S.C,
    denote α β t ρ = denote α β t ρ'
  | .prim _, _, _, _ => rfl
  | .opaq, _, _, _ => rfl
  | .never, _, _, _ => rfl
  | .var _, h, _, _ => nomatch h
  | .set t, h, ρ, ρ' => by simp only [denote]; rw [denote_closed t h ρ ρ']
  | .refine t _ _, h, ρ, ρ' => by simp only [denote]; rw [denote_closed t h ρ ρ']
  | .mu b, h, ρ, ρ' => by
      simp only [denote]
      congr 1
      funext c
      exact denote_closed b h (c :: ρ) (c :: ρ')
  | .held t P PA _ _, h, ρ, ρ' => by
      simp only [Term.hasVar, Bool.or_eq_false_iff] at h
      simp only [denote]
      rw [denote_closed t h.1.1 ρ ρ', denote_closed P h.1.2 ρ ρ', denote_closed PA h.2 ρ ρ']
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
    bodySem α β b ρ = bodySem α β b ρ'
  | .mk fields f wild, h, ρ, ρ' => by
      simp only [Body.hasVar, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_exists,
        Bool.not_eq_true] at h
      have hf : (fun k => fieldSem α β (f k) ρ) = (fun k => fieldSem α β (f k) ρ') :=
        funext fun k => fieldSem_closed (f k) (h.1 k) ρ ρ'
      simp only [bodySem]
      rw [hf, wildSem_closed wild h.2 ρ ρ']

/-- …at a slot. -/
theorem fieldSem_closed : ∀ (s : ObjectSlot S), s.hasVar = false → ∀ ρ ρ' : List S.C,
    fieldSem α β s ρ = fieldSem α β s ρ'
  | .req t, h, ρ, ρ' => by simp only [fieldSem]; rw [denote_closed t h ρ ρ']
  | .optional t, h, ρ, ρ' => by simp only [fieldSem]; rw [denote_closed t h ρ ρ']

/-- …at an open block. -/
theorem wildSem_closed : ∀ (w : Option (Term S)), Term.hasVarO w = false → ∀ ρ ρ' : List S.C,
    wildSem α β w ρ = wildSem α β w ρ'
  | none, _, _, _ => rfl
  | some t, h, ρ, ρ' => by simp only [wildSem]; rw [denote_closed t h ρ ρ']

/-- …at a list of terms. -/
theorem denoteList_closed : ∀ (ts : List (Term S)), Term.hasVarL ts = false →
    ∀ ρ ρ' : List S.C, denoteList α β ts ρ = denoteList α β ts ρ'
  | [], _, _, _ => rfl
  | t :: ts, h, ρ, ρ' => by
      simp only [Term.hasVarL, Bool.or_eq_false_iff] at h
      simp only [denoteList]
      rw [denote_closed t h.1 ρ ρ', denoteList_closed ts h.2 ρ ρ']

/-- …at an optional term. -/
theorem denoteOpt_closed : ∀ (sp : Option (Term S)), Term.hasVarO sp = false →
    ∀ ρ ρ' : List S.C, denoteOpt α β sp ρ = denoteOpt α β sp ρ'
  | none, _, _, _ => rfl
  | some t, h, ρ, ρ' => by simp only [denoteOpt]; rw [denote_closed t h ρ ρ']

/-- …at the members of a list of terms. -/
theorem denoteμs_closed : ∀ (ts : List (Term S)), Term.hasVarL ts = false →
    ∀ ρ ρ' : List S.C, denoteμs α β ts ρ = denoteμs α β ts ρ'
  | [], _, _, _ => rfl
  | t :: ts, h, ρ, ρ' => by
      simp only [Term.hasVarL, Bool.or_eq_false_iff] at h
      simp only [denoteμs]
      rw [denote_closed t h.1 ρ ρ', denoteμs_closed ts h.2 ρ ρ']

end

/-! ## The host rows

At the host orientation, the caller half of a two-sided row is the half `false`, and the stored
half is the half `true`. Where the stored halves are the top of the universe, the truth
predicate, the top as the stored outer, and the empty word, each two-sided row is the one-sided
row. -/

section Host
variable {B : Sig} [Mean B] {α : Table ⟨B, .host⟩} {β : Table (Syn.op ⟨B, .host⟩)}

/-- **The host `refine` is the caller-side restriction.** -/
theorem denote_refine_host (t : Term B) (p : B.P false) (ρ : List (Syn.C ⟨B, .host⟩)) :
    denote α β (S := ⟨B, .host⟩) (.refine t p (Mean.truth true)) ρ =
      (denote α β t ρ).restrict (Mean.eval false p) := by
  have h : Mean.eval (B := B) true (Mean.truth true) = fun _ => true := funext (Mean.eval_truth true)
  rw [denote]
  exact (congrArg _ h).trans (refine2_host _ _)

/-- **The host `held` is the caller-side adapter, restricted by the caller outer**, where the top
    reads every attribute. -/
theorem denote_held_host [TopReads ⟨B, .host⟩] (t P : Term B) (k : Word ⟨B, .host⟩)
    (ρ : List (Syn.C ⟨B, .host⟩)) :
    denote α β (S := ⟨B, .host⟩) (.held t P .opaq k []) ρ =
      ((denote α β t ρ).through (α.word k).1 (α.word k).2).restrict
        fun v => ((denote α β P ρ).e v).isSome :=
  held2_host _ _ _ (TopReads.reads (S := ⟨B, .host⟩)) _ _

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
