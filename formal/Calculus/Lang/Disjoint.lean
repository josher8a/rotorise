import Calculus.Lang.Term
import Calculus.Alg.Rows

/-!
# Disjointness over a universe signature

`Term.disjoint` decides that two terms share no value, by structural recursion on the left
operand, at a pairing of the two operands' binders. `true` says that no value is admitted by both
operands, under every two environments that keep each paired binder pair apart. `false` states
nothing: the test is sound, not complete.

A term denotes a partial isomorphism, and its admission is the domain idempotent. Two terms are
disjoint where the product of the two idempotents is zero, which is orthogonality in an inverse
semigroup. The union certificate asks the test of the two pairs of views (`Calculus.viewsDisjoint`).
Orthogonality is self-dual, so the test reads no orientation: each two-sided row reads both
absolute sides, and the test at the dual universe is the test.

Every row is structure except two leaves: two primitives apart, and two predicates apart. A
universe supplies the two leaves in the class `Leaf`. The rows of `held`, `refine`, `union`,
`set`, `list`, `object`, `opaq`, `var` and `mu` read no fact of a universe. So the test is defined
here one time, and a universe states only its leaves.

`Leaf` holds computable data only, so the test stays computable, and a closed pair reduces in the
kernel.
-/

namespace Calculus.Alg

/-- **The leaves that a universe supplies.** The primitives and the predicates are the only part
    of a term that the test cannot read structurally. The leaves are facts of the signature at
    each absolute side, so the dual universe has the leaves of the universe. -/
class Leaf (B : Sig) where
  /-- Two primitives met: a primitive, or `none` for two primitives that share no value. -/
  prim : B.Ground → B.Ground → Option B.Ground
  /-- Whether a predicate is data that the test can compare with another. -/
  isData : (s : Bool) → B.P s → Bool
  /-- Two predicates met: `none` refuses, `some none` is empty, `some (some r)` is `r`. -/
  pmeet : (s : Bool) → B.P s → B.P s → Option (Option (B.P s))

variable {S : Sig}

/-- A union of what survived a distribution: nothing is the bottom, one survivor is itself, and
    the rest are a union again. -/
def Term.ofOptions : List (Term S) → Term S
  | [] => .never
  | [t] => t
  | ts => .union ts

/-! ## The pairing of binders

The test reads two open terms. A variable of the left operand and a variable of the right operand
are one pair where the two binders were unfolded together. A `Pairing` states that fact:
`p i j = some k` says that the left variable `i` and the right variable `j` are one pair. A
variable that no pairing names is apart from nothing. -/

/-- `p i j = some k`: the left variable `i` and the right variable `j` are one pair of binders,
    the pair `k` counted from the innermost. -/
abbrev Pairing := Nat → Nat → Option Nat

/-- Under a `mu` beside a `mu`: the two new binders pair at `0`, and the pairs outside move up
    one. -/
def pairMu (p : Pairing) : Pairing
  | 0, 0 => some 0
  | i + 1, j + 1 => (p i j).map (· + 1)
  | _, _ => none

/-- Under an unfolding of the left operand: the left binder `0` pairs with nothing. -/
def shiftL (p : Pairing) : Pairing
  | 0, _ => none
  | i + 1, j => p i j

/-- Under an unfolding of the right operand: the right binder `0` pairs with nothing. -/
def shiftR (p : Pairing) : Pairing
  | _, 0 => none
  | i, j + 1 => p i j

/-- The pairing of two closed terms: no binder. -/
def pair0 : Pairing := fun _ _ => none

/-! ## Reading a body name by name -/

/-- **The term an undeclared name holds**: the open block's, and `never` where the body is
    closed. -/
def Body.block (b : Body S) : Term S :=
  match b.wild with
  | none => .never
  | some t => t

/-- **The slot a body gives one name**: the declared slot, or `optional` of the block. A body
    is a total function from the key space to a slot, and this is that function. -/
def Body.slotAt (b : Body S) (k : String) : ObjectSlot S :=
  if h : k ∈ b.fields then b.at ⟨k, h⟩ else .optional b.block

/-- A declared name's slot is the declared one. -/
theorem Body.slotAt_pos {b : Body S} {k : String} (h : k ∈ b.fields) :
    b.slotAt k = b.at ⟨k, h⟩ := by
  unfold Body.slotAt; rw [dif_pos h]

/-- An undeclared name's slot is `optional` of the block. -/
theorem Body.slotAt_neg {b : Body S} {k : String} (h : k ∉ b.fields) :
    b.slotAt k = .optional b.block := by
  unfold Body.slotAt; rw [dif_neg h]

/-! ## The rows of the right operand -/

mutual
/-- **Every row that reads the right operand alone, written once.** The bottom admits nothing. A
    union is disjoint from the left operand where each option is. A recursive term unfolds: its
    body is tested, and its binder pairs with nothing. A refinement admits a part of what its
    inner term admits, so the inner term bounds it. `fam` carries the left operand, already
    applied, at each pairing, and answers every other constructor. -/
def disjSRight (fam : Pairing → Term S → Bool) (p : Pairing) : Term S → Bool
  | .never => true
  | .mu b => disjSRight fam (shiftR p) b
  | .refine y _ _ => disjSRight fam p y
  | .union os => disjSRightL fam p os
  | y => fam p y
/-- The list companion of `disjSRight`: each option is disjoint from the left operand. -/
def disjSRightL (fam : Pairing → Term S → Bool) (p : Pairing) : List (Term S) → Bool
  | [] => true
  | y :: ys => disjSRight fam p y && disjSRightL fam p ys
end

mutual
/-- **The right operand, split at every depth.** The rows of a left `refine` and a left `mu`
    read the right operand through this split. A union splits into its options. A refinement
    keeps its predicate on each option below it, through the wrapper `w`, unless its inner term
    holds a `held` or a variable: there the split drops the predicate, and the inner term bounds
    the refinement. A recursive term is handed whole to the family, and is also unfolded with
    its binder paired with nothing. So a right `refine` or a right `mu` hides no option from
    the left row. -/
def splitR (fam : Pairing → Term S → Bool) (p : Pairing) (w : Term S → Term S) : Term S → Bool
  | .never => true
  | .union os => splitRL fam p w os
  | .refine y q qA =>
      if hasHeld y || y.hasVar then splitR fam p w y
      else splitR fam p (fun t => w (.refine t q qA)) y
  | .mu b => fam p (w (.mu b)) || splitR fam (shiftR p) w b
  | y => fam p (w y)
/-- The list companion of `splitR`. -/
def splitRL (fam : Pairing → Term S → Bool) (p : Pairing) (w : Term S → Term S) :
    List (Term S) → Bool
  | [] => true
  | y :: ys => splitR fam p w y && splitRL fam p w ys
end

/-! ## The families: one per left constructor, flat and non-recursive -/

/-- **A data predicate at the side `s` that no element of the right refinement chain satisfies
    with `q`.** A refinement counts only over a held-free closed term, which lies below the top,
    so two such refinements send one value and one attribute to each other. -/
def predApart [Leaf S] (s : Bool) (q : S.P s) : Term S → Bool
  | .refine y q' qA' => (Leaf.isData s (half s q' qA') && !hasHeld y && !y.hasVar &&
      (match Leaf.pmeet s q (half s q' qA') with | some none => true | _ => false)) ||
        predApart s q y
  | _ => false

/-- **A refinement is apart from the right operand at the side `s`**: the refinement's data
    predicate at `s` holds with no predicate of the right chain, over a held-free closed term. -/
def dataApart [Leaf S] (x : Term S) (s : Bool) (q : S.P s) (y : Term S) : Bool :=
  Leaf.isData s q && !hasHeld x && !x.hasVar && predApart s q y

/-- **The one leaf family**: a primitive is disjoint from a primitive where the leaf says so,
    and from every former, because two formers of different shape classes share no value. The
    top and a function-valued admission are disjoint from nothing. -/
def famPrimD [Leaf S] (g : S.Ground) : Term S → Bool
  | .prim g' => (Leaf.prim g g').isNone
  | .set _ | .list _ _ _ | .object _ => true
  | _ => false

/-- **Two sets are disjoint where their elements are.** A set former has no empty inhabitant, so
    two element terms that share no value give two set terms that share no set. The row asks
    closed elements, because the set laws of a universe are stated over closed elements. -/
def famSetD (a : Term S) (mt : Term S → Bool) : Term S → Bool
  | .set y => !a.hasVar && !y.hasVar && mt y
  | .prim _ | .list _ _ _ | .object _ => true
  | _ => false

/-- **Two variables are disjoint where the pairing names them one pair**, because the
    environments keep each paired binder pair apart. -/
def famVarD (i : Nat) (p : Pairing) : Term S → Bool
  | .var j => (p i j).isSome
  | _ => false

/-- Some position of two aligned rows is disjoint. -/
def anyZip : List (Term S → Bool) → List (Term S) → Bool
  | f :: fs, u :: us => f u || anyZip fs us
  | _, _ => false

/-- **Two `list` shapes, the left as partially applied tests and the right as terms.** Two
    values of different lengths differ, so the two shapes are disjoint where one position of
    each common length is disjoint. **Either side without a spread**: that side fixes the one
    length, and a length the other side refuses is disjoint outright. **Both spreading**: where
    one side dominates, every common length re-spreads the row at `max p₁ p₂ + max s₁ s₂`, so
    one disjoint position of that row decides. Where no side dominates, the test answers
    `false`. -/
def listDisjRow (fpre : List (Term S → Bool)) (fsp : Option (Term S → Bool))
    (fsuf : List (Term S → Bool)) (pre₂ : List (Term S)) (sp₂ : Option (Term S))
    (suf₂ : List (Term S)) : Bool :=
  match fsp, sp₂ with
  | some f, some c =>
      if dominates fpre.length fsuf.length pre₂.length suf₂.length then
        match rowOfG fpre (some f) fsuf (max fpre.length pre₂.length + max fsuf.length suf₂.length),
            rowOfG pre₂ (some c) suf₂ (max fpre.length pre₂.length + max fsuf.length suf₂.length) with
        | some fs, some us => anyZip fs us
        | _, _ => false
      else false
  | none, _ =>
      match rowOfG pre₂ sp₂ suf₂ (fpre.length + fsuf.length) with
      | some us => anyZip (fpre ++ fsuf) us
      | none => true
  | some f, none =>
      match rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length) with
      | some fs => anyZip fs (pre₂ ++ suf₂)
      | none => true

/-- The family of the one positional container: the rows against a `list`, and disjoint from
    every former in another shape class. -/
def famListD (fpre : List (Term S → Bool)) (fsp : Option (Term S → Bool))
    (fsuf : List (Term S → Bool)) : Term S → Bool
  | .list pre₂ sp₂ suf₂ => listDisjRow fpre fsp fsuf pre₂ sp₂ suf₂
  | .prim _ | .set _ | .object _ => true
  | _ => false

/-- **The slot pair at one name is disjoint**: some side requires the name, and the terms are
    disjoint. `g` is the left slot's test against a right slot. `mw` is the left block's test. -/
def slotD (a b : Body S) (g : {k // k ∈ a.fields} → ObjectSlot S → Bool)
    (mw : Term S → Bool) (k : {k // k ∈ a.fields ∪ b.fields}) : Bool :=
  if h : k.1 ∈ a.fields then
    g ⟨k.1, h⟩ (if h' : k.1 ∈ b.fields then b.at ⟨k.1, h'⟩ else .optional b.block)
  else
    match b.at ⟨k.1, (Finset.mem_union.mp k.2).resolve_left h⟩ with
    | .req y => mw y
    | .optional _ | .fill _ _ => false

/-- **Two objects are disjoint at one name.** A body is a total function from the key space to a
    slot, so two bodies share no map where one name of either body holds two disjoint slots.
    The object is disjoint from every former in another shape class. -/
def famObjD (a : Body S) (g : {k // k ∈ a.fields} → ObjectSlot S → Bool)
    (mw : Term S → Bool) : Term S → Bool
  | .object b => decide (∃ k : {k // k ∈ a.fields ∪ b.fields}, slotD a b g mw k = true)
  | .prim _ | .set _ | .list _ _ _ => true
  | _ => false

mutual
/-- **Orthogonality, as a Boolean decision.** `true` says that no value is admitted by both
    operands, under every two environments that keep each paired binder pair apart
    (`disjoint_sound`, `disjoint_soundA`). The recursion is on the left operand, and every row
    keeps the left operand on the left.

    A `held` and the top are disjoint only from the bottom, because their admission is a
    function that the test does not read. A recursive term and a refinement read the right
    operand through `splitR`. Two recursive terms are disjoint where their bodies are disjoint
    with the two binders paired, because then each two stages are disjoint. A recursive term
    also unfolds, and its binder pairs with nothing. A refinement is disjoint where its inner
    term is, or where its data predicate at one absolute side and a data predicate of the
    partner at that side hold together nowhere. -/
def Term.disjoint [Leaf S] (p : Pairing) : Term S → Term S → Bool
  | .never, _ => true
  | .held _ _ _ _ _, y => disjSRight (fun _ _ => false) p y
  | .legacy _ _, y => disjSRight (fun _ _ => false) p y
  | .var i, y => disjSRight (famVarD i) p y
  | .mu b, y =>
      splitR (fun p' y' => (match y' with
        | .mu b' => Term.disjoint (pairMu p') b b'
        | _ => false) || Term.disjoint (shiftL p') b y') p id y
  | .refine x q qA, y =>
      splitR (fun p' y' => Term.disjoint p' x y' || dataApart x false q y' ||
        dataApart x true qA y') p id y
  | .union os, y => Term.disjointL p os y
  | .prim g, y => disjSRight (fun _ => famPrimD g) p y
  | .set a, y => disjSRight (fun q => famSetD a (Term.disjoint q a)) p y
  | .opaq, y => disjSRight (fun _ _ => false) p y
  | .list pre sp suf, y =>
      disjSRight (fun q => famListD (Term.disjointTs q pre)
        (match sp with | none => none | some t => some (Term.disjoint q t))
        (Term.disjointTs q suf)) p y
  | .object (.mk fs f w), y =>
      disjSRight (fun q => famObjD (.mk fs f w) (fun k => ObjectSlot.disjoint q (f k))
        (match w with | none => fun _ => true | some t => Term.disjoint q t)) p y
termination_by structural x _ => x
/-- A union is disjoint from the right operand where each option is. -/
def Term.disjointL [Leaf S] (p : Pairing) : List (Term S) → Term S → Bool
  | [], _ => true
  | x :: xs, y => Term.disjoint p x y && Term.disjointL p xs y
termination_by structural xs _ => xs
/-- The test against each position of a row, partially applied. -/
def Term.disjointTs [Leaf S] (p : Pairing) : List (Term S) → List (Term S → Bool)
  | [] => [] | t :: ts => Term.disjoint p t :: Term.disjointTs p ts
termination_by structural ts => ts
/-- Two slots are disjoint where one requires the name and the terms are disjoint. A fill
    requires the name on the write only, so it is read as `optional`; the side views state it
    exactly. -/
def ObjectSlot.disjoint [Leaf S] (p : Pairing) : ObjectSlot S → ObjectSlot S → Bool
  | .req x, .req y => Term.disjoint p x y
  | .req x, .optional y | .req x, .fill y _ => Term.disjoint p x y
  | .optional x, .req y | .fill x _, .req y => Term.disjoint p x y
  | _, _ => false
termination_by structural f _ => f
end

end Calculus.Alg
