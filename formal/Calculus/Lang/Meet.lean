import Calculus.Lang.Term

/-!
# The meet over a universe signature

`Term.meet` is the intersection of two admissions, as a term, by structural recursion on the left
operand. `some z` is a term that admits a value exactly where both factors admit the value, `some
never` is the empty intersection, and `none` is a refusal: no term states the intersection.

Every row is structure except two leaves: a primitive met with a primitive or with the top, and a
predicate met with a predicate. A universe supplies the two leaves in the class `Leaf`. The rows of
`held`, `refine`, `union`, `set`, `list`, `object`, `opaq`, `var` and `mu` read no fact of a
universe. So the meet is defined here one time, and a universe states only its leaf meet.

`Leaf` holds computable data only, so the meet stays computable, and a closed pair reduces in the
kernel.
-/

namespace Calculus.Alg

/-- **The leaf meet that a universe supplies.** The primitives and the predicates are the only part
    of a term that the meet cannot read structurally. -/
class Leaf (S : Syn) where
  /-- Two primitives met: a primitive, or `none` for the bottom. -/
  prim : S.Ground → S.Ground → Option S.Ground
  /-- A primitive met with the top: the primitive (`true`), or a refusal (`false`). -/
  primTop : S.Ground → Bool
  /-- Whether a predicate is data that the meet can carry. -/
  isData : S.Pred → Bool
  /-- Two predicates met: `none` refuses, `some none` is empty, `some (some r)` is `r`. -/
  pmeet : S.Pred → S.Pred → Option (Option S.Pred)

variable {S : Syn}

/-! ## Reading a field and a term -/

/-- Whether a slot admits nothing at a name that must be present. An `optional` slot at the
    bottom is not this: it is a name that must be absent, which is a body a value can satisfy. -/
def ObjectSlot.isBottom : ObjectSlot S → Bool
  | .req t => t.isNever
  | .optional _ => false

/-- A union of what survived a distribution: nothing is the bottom, one survivor is itself, and
    the rest are a union again. -/
def Term.ofOptions : List (Term S) → Term S
  | [] => .never
  | [t] => t
  | ts => .union ts

/-- A list of answers, as one answer: `none` where any cell refused. -/
def allSome {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some x :: rest => (allSome rest).map (x :: ·)

/-- **A refinement over the bottom is the bottom, and two refinements over one carrier meet.**
    The bottom bubbles up through a slot that must hold a value, and a refinement's inner term
    is one. A second refinement over an already-refined term does not stack: the predicates meet,
    and where the predicate meet is empty the result is the bottom. Both refinement rows of the
    meet call this, so every refinement that the meet builds is normal. -/
def Term.refineOf [Leaf S] (z : Term S) (p : S.Pred) : Term S :=
  match z with
  | .never => .never
  | .refine z' q =>
      match Leaf.pmeet q p with
      | some (some r) => .refine z' r
      | some none     => .never
      | none          => .refine (.refine z' q) p
  | _ => .refine z p

/-- **A list with a declared position at the bottom is the bottom.** Every value the list
    admits fills each declared position, so one position holding nothing empties the list.
    The SPREAD is not such a slot: a value of exactly the declared length omits every spread
    position, so a spread at the bottom reads "exactly the declared positions" rather than
    "nothing". The prefix and the suffix are both declared; the spread is not. -/
def Term.listOf (pre : List (Term S)) (sp : Option (Term S)) (suf : List (Term S)) : Term S :=
  if pre.any Term.isNever || suf.any Term.isNever then .never else .list pre sp suf

/-- The suffix-free case, under the name the tuple rows use. -/
def Term.tupleOf (ts : List (Term S)) (tail : Option (Term S)) : Term S :=
  Term.listOf ts tail []

/-! ## The meet, structurally

Every row keeps the left operand on the left. -/

/-- The partially applied meets of one row, applied position for position. -/
def zipF : List (Term S → Option (Term S)) → List (Term S) → List (Option (Term S))
  | [], _ => [] | _, [] => []
  | f :: fs, u :: us => f u :: zipF fs us

mutual
/-- **Every row that reads the right operand alone, written once.** The bottom, the four whose
    admission is a function, a variable, a recursive term, a refinement and a union answer the
    same way whatever the left operand is, so they are stated here rather than restated per left
    constructor. `fam` carries the left operand, already applied. -/
def meetSRight [Leaf S] (fam : Term S → Option (Term S)) : Term S → Option (Term S)
  | .never => some .never
  | .held _ _ _ _ => none
  -- a closed variable is the bottom, and the meet states no recursive term
  | .var _ => some .never
  | .mu _ => none
  | .refine y p =>
      if Leaf.isData p then (meetSRight fam y).map (fun z => Term.refineOf z p) else none
  | .union os => (allSome (meetSRightL fam os)).bind
      (fun zs => some (Term.ofOptions (zs.filter (fun z => !z.isNever))))
  | y => fam y
/-- The list companion of `meetSRight`. -/
def meetSRightL [Leaf S] (fam : Term S → Option (Term S)) : List (Term S) → List (Option (Term S))
  | [] => [] | y :: ys => meetSRight fam y :: meetSRightL fam ys
end

/-! ### The families: one per left constructor, flat and non-recursive. -/

/-- **The one leaf family**: a primitive meets a primitive through the leaf meet, meets the top
    where the leaf says so, and is the bottom against every other constructor. -/
def famPrim [Leaf S] (g : S.Ground) : Term S → Option (Term S)
  | .prim g' => some (match Leaf.prim g g' with | some h => .prim h | none => .never)
  | .opaq => if Leaf.primTop g then some (.prim g) else none
  | _ => some .never

mutual
/-- Whether a `held` occurs in the term. -/
def hasHeld : Term S → Bool
  | .held _ _ _ _ => true
  | .refine t _ => hasHeld t
  | .mu t => hasHeld t
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

/-- **Two sets meet at their elements.** The meet of the elements is the element of the meet, and
    an element meet at the bottom is a set meet at the bottom, because a set former has no empty
    inhabitant. The row states a set only where the three terms are held-free: there each set
    writes and reads exactly where each element does, while an adapter element can collide two
    values or change the stored member. -/
def famSet (a : Term S) (mt : Term S → Option (Term S)) : Term S → Option (Term S)
  | .set y => match mt y with
      | some z =>
          if z.isNever then some .never
          else if hasHeld a || hasHeld y || hasHeld z then none
          else some (.set z)
      | none => none
  | .opaq => none
  | _ => some .never

/-- The top meets itself, and a primitive where the leaf says so. Every other constructor
    refuses, because the closed form of the top states no shape to intersect. -/
def famOpaq [Leaf S] : Term S → Option (Term S)
  | .prim g => if Leaf.primTop g then some (.prim g) else none
  | .opaq => some .opaq
  | _ => none

/-- **The row a `list` shape assigns to `n` positions**: the prefix, the spread as often as
    the middle needs, then the suffix. `none` is the length the shape refuses. One
    definition serves both operands, because the left operand's positions are partially
    applied meets and the right operand's are terms, and the shape does not care which. -/
def rowOfG {α : Type} (pre : List α) (sp : Option α) (suf : List α) (n : Nat) :
    Option (List α) :=
  match sp with
  | some c =>
      if n < pre.length + suf.length then none
      else some (pre ++ List.replicate (n - pre.length - suf.length) c ++ suf)
  | none => if n = pre.length + suf.length then some (pre ++ suf) else none

/-- **One side dominates the other**, in the prefix and in the suffix at once.

    This is the whole of the `list` meet's refusal, and it is a fact about lengths alone.
    With both shapes spreading, the meet admits a value of length `n` exactly when
    `n ≥ max (p₁+s₁) (p₂+s₂)`, while the widest `list` the answer can spell admits
    `n ≥ max p₁ p₂ + max s₁ s₂`. The second is never smaller, and the two are EQUAL exactly
    when one side's prefix and suffix are both at least the other's. Elsewhere a window of
    lengths sits in the intersection that no single `list` states, because a `list` carries
    one prefix and one suffix and the window needs two shapes. There the meet refuses. -/
def dominates (p₁ s₁ p₂ s₂ : Nat) : Bool :=
  (decide (p₂ ≤ p₁) && decide (s₂ ≤ s₁)) || (decide (p₁ ≤ p₂) && decide (s₁ ≤ s₂))

/-- Two `list` shapes met, the left as partially applied meets and the right as terms.

    Three branches, and only the first can refuse. **Both spreading**: the answer is the
    row at `max p₁ p₂ + max s₁ s₂`, split back into that prefix and that suffix, with the
    spreads met; `dominates` says when that is the exact intersection, and the meet refuses
    otherwise. **Either side without a spread**: that side's arity is fixed, so the answer
    FLATTENS to one prefix of exactly that length with no spread and no suffix; a length the
    other side cannot reach is the empty intersection, which is `.never`. Flattening rather
    than keeping the longer prefix and the longer suffix is what the fixed-arity case needs:
    the two overhangs can collide, and at a fixed arity there is no spread to meet them
    against. -/
def listMeetRow (fpre : List (Term S → Option (Term S))) (fsp : Option (Term S → Option (Term S)))
    (fsuf : List (Term S → Option (Term S))) (pre₂ : List (Term S)) (sp₂ : Option (Term S))
    (suf₂ : List (Term S)) : Option (Term S) :=
  match fsp, sp₂ with
  | some f, some c =>
      if dominates fpre.length fsuf.length pre₂.length suf₂.length then
        match f c,
            rowOfG fpre (some f) fsuf
              (max fpre.length pre₂.length + max fsuf.length suf₂.length),
            rowOfG pre₂ (some c) suf₂
              (max fpre.length pre₂.length + max fsuf.length suf₂.length) with
        | some sp, some fs, some us =>
            (allSome (zipF fs us)).map fun row =>
              Term.listOf (row.take (max fpre.length pre₂.length)) (some sp)
                (row.drop (max fpre.length pre₂.length))
        | none, _, _ => none
        | _, _, _ => some .never
      else none
  | none, _ =>
      match rowOfG fpre none fsuf (fpre.length + fsuf.length),
          rowOfG pre₂ sp₂ suf₂ (fpre.length + fsuf.length) with
      | some fs, some us => (allSome (zipF fs us)).map fun row => Term.listOf row none []
      | _, _ => some .never
  | some f, none =>
      match rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length),
          rowOfG pre₂ none suf₂ (pre₂.length + suf₂.length) with
      | some fs, some us => (allSome (zipF fs us)).map fun row => Term.listOf row none []
      | _, _ => some .never

/-- The family of the one positional container: the one shape a positional value can meet,
    and the bottom at every constructor in another value slot. `opaq` refuses, because its
    closed form states no positional shape to intersect. -/
def famList (fpre : List (Term S → Option (Term S))) (fsp : Option (Term S → Option (Term S)))
    (fsuf : List (Term S → Option (Term S))) : Term S → Option (Term S)
  | .list pre₂ sp₂ suf₂ => listMeetRow fpre fsp fsuf pre₂ sp₂ suf₂
  | .opaq => none
  | _ => some .never

/-- **The term an undeclared name holds**: the open block's, and `never` where the body is
    closed. -/
def Body.block (b : Body S) : Term S :=
  match b.wild with
  | none => .never
  | some t => t

/-- A slot met through one term's meet, keeping the slot's mark. It is `ObjectSlot.meet
    (.optional t)` with `Term.meet t` passed applied, which keeps the recursion structural. -/
def ObjectSlot.through (m : Term S → Option (Term S)) : ObjectSlot S → Option (ObjectSlot S)
  | .req y => (m y).map .req
  | .optional y => (m y).map .optional

/-- **The meet at one name of either body.** A body is a total function from the key space to
    a slot, presented as the declared slots and a default: an undeclared name holds `optional`
    of the block. So a name the left body declares meets the right body's slot at that name,
    and a name only the right body declares meets the left body's block. -/
def objSlot (a b : Body S) (g : {k // k ∈ a.fields} → ObjectSlot S → Option (ObjectSlot S))
    (mw : Term S → Option (Term S)) (k : {k // k ∈ a.fields ∪ b.fields}) :
    Option (ObjectSlot S) :=
  if h : k.1 ∈ a.fields then
    g ⟨k.1, h⟩ (if h' : k.1 ∈ b.fields then b.at ⟨k.1, h'⟩ else .optional b.block)
  else
    ObjectSlot.through mw (b.at ⟨k.1, (Finset.mem_union.mp k.2).resolve_left h⟩)

/-- A met slot that says the name is absent: `optional never`. -/
def ObjectSlot.isAbsentOpt : Option (ObjectSlot S) → Bool
  | some (.optional t) => t.isNever
  | _ => false

/-- **Two objects, met pointwise.** Every name of either body meets at its two slots, and the
    blocks meet as the default. A product is the bottom when any factor is, so a slot at the
    bottom decides before a slot that refuses.

    **The normal form drops a name that states the default**, where the default is `never`: in a
    closed body `optional never` is what an undeclared name already holds. An open default has
    no decidable equality to test, so there every name is kept as written. -/
def objObj (a : Body S) (g : {k // k ∈ a.fields} → ObjectSlot S → Option (ObjectSlot S))
    (mw : Term S → Option (Term S)) (b : Body S) : Option (Term S) :=
  if decide (∃ k : {k // k ∈ a.fields ∪ b.fields},
      ((objSlot a b g mw k).map ObjectSlot.isBottom) = some true) then some .never
  else
    match mw b.block with
    | none => none
    | some zb =>
      if decide (∀ k : {k // k ∈ a.fields ∪ b.fields}, (objSlot a b g mw k).isSome = true) then
        let keep : String → Bool := fun k =>
          if h : k ∈ a.fields ∪ b.fields then
            !(zb.isNever && ObjectSlot.isAbsentOpt (objSlot a b g mw ⟨k, h⟩))
          else false
        some (.object (.mk ((a.fields ∪ b.fields).filter (fun k => keep k = true))
          (fun k => (objSlot a b g mw ⟨k.1, (Finset.mem_filter.mp k.2).1⟩).getD
            (.optional .never))
          (if zb.isNever then none else some zb)))
      else none

/-- The family of an object: the pointwise meet against an object, a refusal at the top, and the
    bottom at every constructor in another value slot. -/
def famObj (a : Body S) (g : {k // k ∈ a.fields} → ObjectSlot S → Option (ObjectSlot S))
    (mw : Term S → Option (Term S)) : Term S → Option (Term S)
  | .object b => objObj a g mw b
  | .opaq => none
  | _ => some .never

mutual
/-- **The intersection of two admissions, as a term**, by structural recursion on the left
    operand. Every row keeps the left operand on the left. The leaf meet answers the primitives
    and the predicates, and every other row is structure. -/
def Term.meet [Leaf S] : Term S → Term S → Option (Term S)
  | .never, _ => some .never
  | .held _ _ _ _, .never => some .never
  | .held _ _ _ _, _ => none
  | .var _, _ => some .never
  | .mu _, .never => some .never
  | .mu _, _ => none
  | .refine _ _, .never => some .never
  | .refine x p, y =>
      if Leaf.isData p then (Term.meet x y).map (fun z => Term.refineOf z p) else none
  | .union _, .never => some .never
  | .union os, y => (allSome (Term.meetSL os y)).bind
      (fun zs => some (Term.ofOptions (zs.filter (fun z => !z.isNever))))
  | .prim g, y => meetSRight (famPrim g) y
  | .set a, y => meetSRight (famSet a (Term.meet a)) y
  | .opaq, y => meetSRight famOpaq y
  | .list pre sp suf, y =>
      meetSRight (famList (Term.meetSTs pre)
        (match sp with | none => none | some t => some (Term.meet t))
        (Term.meetSTs suf)) y
  | .object (.mk fs f w), y =>
      meetSRight (famObj (.mk fs f w) (fun k => ObjectSlot.meet (f k))
        (match w with | none => fun _ => some .never | some t => Term.meet t)) y
termination_by structural x _ => x
/-- The meet of each option of a union with one right operand. -/
def Term.meetSL [Leaf S] : List (Term S) → Term S → List (Option (Term S))
  | [], _ => [] | x :: xs, y => Term.meet x y :: Term.meetSL xs y
termination_by structural xs _ => xs
/-- The meet with each position of a row, partially applied. -/
def Term.meetSTs [Leaf S] : List (Term S) → List (Term S → Option (Term S))
  | [] => [] | t :: ts => Term.meet t :: Term.meetSTs ts
termination_by structural ts => ts
/-- The complete two-mark slot meet. Required presence dominates optional presence. -/
def ObjectSlot.meet [Leaf S] : ObjectSlot S → ObjectSlot S → Option (ObjectSlot S)
  | .req x, .req y => (Term.meet x y).map .req
  | .req x, .optional y => (Term.meet x y).map .req
  | .optional x, .req y => (Term.meet x y).map .req
  | .optional x, .optional y => (Term.meet x y).map .optional
termination_by structural f _ => f
end

/-! ## Reading an answer name by name

A body is read as its slot at every name, so each factor and the meet are stated through one
function. -/

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

/-- **A term's slot at one name**, where the term is an object. The vector bridge states an
    object answer through this, because two bodies are one body exactly when their slots agree
    at every name and their blocks agree. -/
def Term.slotAt : Term S → String → Option (ObjectSlot S)
  | .object b, k => some (b.slotAt k)
  | _, _ => none

/-- **A term's option at one position**: a union's option there, and a term that is not a union
    as its own single option. The bridge states a union of object answers option by option. -/
def Term.optionAt : Term S → Nat → Option (Term S)
  | .union os, i => os[i]?
  | t, 0 => some t
  | _, _ + 1 => none

/-- A term's open block, where the term is an object: `none` inside for a closed body. -/
def Term.blockOf : Term S → Option (Option (Term S))
  | .object b => some b.wild
  | _ => none

end Calculus.Alg
