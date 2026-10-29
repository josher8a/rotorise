import Calculus.Dynamo.Alg.DerivedKey

/-!
# The key match

A key spec chooses the parts of a key from the item. The spec is one of four arms, or a match: a
discriminator names one attribute of the item, and the value of that attribute selects the spec that
continues. A match is the dual of `extract(codec, pattern)`: the arms of the match are the cases of
a coproduct, and the discriminator value is the tag.

The arms of a match are a function from the literal to the spec. A function has one value at a
literal, so two arms with one literal have no representation, and no theorem needs a premise that
the literals differ. The host writes the arms as the keys of one object, which cannot repeat a key
either, or as cases, and construction refuses a literal that two cases name. A literal that the
function does not list maps to the arm `missing`.

The model is parametric in the name of an attribute. A name is opaque: the item is a function
from a name to the printed value, and no definition or theorem reads a name as a top-level
attribute. A later pass can instantiate the name with a path and change no law.

A leaf holds the parts that the host evaluated, as a function of the item, and the length of the
spec. The selection of the leaf reads only the discriminator values. The key of a match is the key
of the arm that the selection reaches (`keyOf_match`), and the key of a leaf is `build`.

Two arms with equal leaves give one key to two items in different arms (`collision`). The key then
does not decode to its arm (`not_decodable`), and the ruling is a mark on the match, not a refusal.
Inside one arm the key is lawful as the leaf is (`leaf_key_split`, `leaf_key_injective`).

A nested match selects the arm that one flat match selects, where the flat match is keyed by the
path of the discriminator values (`select_eq_flat`). So a nested match adds no object to the model.
-/

namespace Calculus

namespace DerivedKey

/-! ## The spec -/

/-- The item as the match reads it: the printed value of an attribute, or none where the attribute
    is absent. A name is opaque. -/
abbrev Item (N : Type) := N → Option String

/-- A leaf: the length of the spec, and the parts that the host evaluated for an item. -/
structure Leaf (N : Type) where
  full : Nat
  parts : Item N → List (Option Comp)

/-- A leaf whose parts do not depend on the item. A row of the vectors holds one item, so its
    leaves are constant. -/
def Leaf.const {N : Type} (full : Nat) (ps : List (Option Comp)) : Leaf N := ⟨full, fun _ => ps⟩

/-- An arm that does not match. A leaf prints parts. `null` gives no key. `attr` gives the printed
    value of one attribute as the key, with no join. `missing` is the arm that the host lacks: the
    host throws there. -/
inductive Arm (N : Type) where
  | leaf (l : Leaf N)
  | null
  | attr (name : N)
  | missing

/-- A key spec: an arm, or a match on one discriminator with an arm for each literal. -/
inductive KeySpec (N : Type) where
  | arm (a : Arm N)
  | match_ (disc : N) (arms : String → KeySpec N)

/-- The arms of a match from a list of literals. A literal that the list does not name is
    `missing`. The first entry of a literal wins, but the result is a function, so the match holds
    one arm for each literal. -/
def KeySpec.ofList {N : Type} (xs : List (String × KeySpec N)) : String → KeySpec N :=
  fun l => (xs.lookup l).getD (.arm .missing)

/-- The arms of a match from cases: a case names a list of literals and one arm, and each literal of
    the case selects the arm. A literal that no case names is `missing`. The host refuses two cases that
    name one literal, so a row has none. Where two cases name one, the first case wins here. -/
def KeySpec.ofCases {N : Type} : List (List String × KeySpec N) → String → KeySpec N
  | [], _ => .arm .missing
  | (ls, a) :: rest, l => if ls.contains l then a else KeySpec.ofCases rest l

/-- **A literal of a case selects the arm of the case**, where no other case names the literal. -/
theorem KeySpec.ofCases_of_mem {N : Type} {xs : List (List String × KeySpec N)} {ls : List String}
    {a : KeySpec N} {l : String} (hm : (ls, a) ∈ xs) (hl : ls.contains l = true)
    (hone : ∀ c ∈ xs, c.1.contains l = true → c = (ls, a)) : KeySpec.ofCases xs l = a := by
  induction xs with
  | nil => cases hm
  | cons c rest ih =>
    obtain ⟨ls', a'⟩ := c
    simp only [KeySpec.ofCases]
    cases h : ls'.contains l
    · have hne : (ls, a) ≠ (ls', a') := by
        intro he
        have : ls = ls' := (Prod.mk.inj he).1
        rw [← this, hl] at h
        exact Bool.noConfusion h
      have hm' : (ls, a) ∈ rest := by
        rcases List.mem_cons.mp hm with h' | h'
        · exact absurd h' hne
        · exact h'
      simp only [Bool.false_eq_true, if_false]
      exact ih hm' fun c hc hcl => hone c (List.mem_cons_of_mem _ hc) hcl
    · have := hone (ls', a') List.mem_cons_self h
      simp only [if_true]
      exact (Prod.mk.inj this).2

/-- **A literal that no case names selects `missing`.** -/
theorem KeySpec.ofCases_of_none {N : Type} {xs : List (List String × KeySpec N)} {l : String}
    (h : ∀ c ∈ xs, c.1.contains l = false) : KeySpec.ofCases xs l = .arm .missing := by
  induction xs with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨ls', a'⟩ := c
    simp only [KeySpec.ofCases]
    have h1 := h (ls', a') List.mem_cons_self
    simp only [h1, Bool.false_eq_true, if_false]
    exact ih fun c hc => h c (List.mem_cons_of_mem _ hc)

/-- The lookup of a literal in the entries of one case, then in the rest. -/
theorem lookup_map_append {β : Type} (ls : List String) (a : β) (rest : List (String × β)) (l : String) :
    (ls.map (fun l' => (l', a)) ++ rest).lookup l = if ls.contains l then some a else rest.lookup l := by
  induction ls with
  | nil => simp
  | cons x ls ih =>
    have e1 : (x :: ls).contains l = (l == x || ls.contains l) := List.contains_cons
    rw [List.map_cons, List.cons_append, e1]
    rcases Bool.eq_false_or_eq_true (l == x) with h | h
    · simp [List.lookup, h]
    · simpa [List.lookup, h] using ih

/-- **A grouped match is another way to write the match of one arm for each literal.** The host
    writes one entry for each literal of each case, and the arms of the two forms are one function. -/
theorem KeySpec.ofCases_eq_ofList {N : Type} (xs : List (List String × KeySpec N)) (l : String) :
    KeySpec.ofCases xs l =
      KeySpec.ofList (xs.flatMap fun c => c.1.map fun l' => (l', c.2)) l := by
  induction xs with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨ls', a'⟩ := c
    simp only [KeySpec.ofCases, KeySpec.ofList, List.flatMap_cons] at ih ⊢
    rw [lookup_map_append]
    cases ls'.contains l
    · simpa using ih
    · simp

/-! ## The selection -/

/-- The arm that an item reaches. An absent discriminator reaches `missing`, as does a literal that
    names no arm. -/
def select {N : Type} (i : Item N) : KeySpec N → Arm N
  | .arm a => a
  | .match_ d arms =>
      match i d with
      | none => .missing
      | some v => select i (arms v)

/-- What the host gave: a throw, no key, the printed attribute as the key, or the segments. -/
inductive Out where
  | refused
  | nothing
  | raw (k : String)
  | segs (ss : List String)
  deriving DecidableEq

/-- The key of an arm for an item. -/
def Arm.key {N : Type} (allowPartial enforce : Bool) (i : Item N) : Arm N → Out
  | .leaf l =>
      match build l.full allowPartial enforce (l.parts i) with
      | none => .refused
      | some ss => .segs ss
  | .null => .nothing
  | .attr n =>
      match i n with
      | none => .nothing
      | some v => .raw v
  | .missing => .refused

/-- The key of a spec for an item: the key of the arm that the item reaches. -/
def keyOf {N : Type} (allowPartial enforce : Bool) (i : Item N) (s : KeySpec N) : Out :=
  (select i s).key allowPartial enforce i

/-! ## The laws of the selection -/

variable {N : Type} {allowPartial enforce : Bool} {i i' : Item N}

/-- **The key of a match is the key of the arm that the item selects.** -/
theorem keyOf_match {d : N} {arms : String → KeySpec N} {v : String} (h : i d = some v) :
    keyOf allowPartial enforce i (.match_ d arms) = keyOf allowPartial enforce i (arms v) := by
  simp [keyOf, select, h]

/-- **The key of a match is `build` on the leaf that the item selects.** -/
theorem keyOf_leaf {s : KeySpec N} {l : Leaf N} (h : select i s = .leaf l) :
    keyOf allowPartial enforce i s =
      match build l.full allowPartial enforce (l.parts i) with
      | none => .refused
      | some ss => .segs ss := by
  simp [keyOf, h, Arm.key]

/-- **An absent discriminator selects nothing.** The host throws. -/
theorem select_absent {d : N} {arms : String → KeySpec N} (h : i d = none) :
    select i (.match_ d arms) = .missing := by
  simp [select, h]

/-- **A literal that names no arm selects nothing.** The host throws. -/
theorem select_unknown {d : N} {arms : String → KeySpec N} {v : String} (h : i d = some v)
    (hv : arms v = .arm .missing) : select i (.match_ d arms) = .missing := by
  simp [select, h, hv]

/-- The key of an item that selects nothing is a refusal. -/
theorem keyOf_refused {s : KeySpec N} (h : select i s = .missing) :
    keyOf allowPartial enforce i s = .refused := by
  simp [keyOf, h, Arm.key]

/-- A match whose arm is `null` gives no key. -/
theorem keyOf_null {s : KeySpec N} (h : select i s = .null) :
    keyOf allowPartial enforce i s = .nothing := by
  simp [keyOf, h, Arm.key]

/-! ## Flattening -/

/-- The discriminator values that an item reads on its way through a spec. The path stops at an
    absent discriminator. -/
def trace {N : Type} (i : Item N) : KeySpec N → List String
  | .arm _ => []
  | .match_ d arms =>
      match i d with
      | none => []
      | some v => v :: trace i (arms v)

/-- The flat match: one arm for each path of discriminator values. A path that ends before an arm,
    or goes past an arm, is `missing`. -/
def flat {N : Type} : KeySpec N → List String → Arm N
  | .arm a, [] => a
  | .arm _, _ :: _ => .missing
  | .match_ _ _, [] => .missing
  | .match_ _ arms, v :: p => flat (arms v) p

/-- **Flattening.** A nested match selects the arm that the flat match selects at the path of the
    discriminator values. The iterated coproduct is a coproduct, so a nested match needs no object
    that a flat match lacks. The proof reads no premise on the arms. -/
theorem select_eq_flat (s : KeySpec N) : select i s = flat s (trace i s) := by
  induction s with
  | arm a => rfl
  | match_ d arms ih =>
      cases h : i d with
      | none => simp [select, trace, flat, h]
      | some v => simp [select, trace, flat, h, ih v]

/-! ## The key inside one arm -/

/-- The segments of a leaf as characters. -/
def charSegs (ss : List String) : List (List Char) := ss.map String.toList

/-- **Inside one arm the read of the key gives the segments back.** The leaf is lawful where it has
    a segment and no segment holds the separator, which is the domain of `keyCodec_lawful`. -/
theorem leaf_key_split (c : Char) {s : KeySpec N} {l : Leaf N} {ss : List String}
    (hl : select i s = .leaf l) (hb : build l.full allowPartial enforce (l.parts i) = some ss)
    (hne : ss ≠ []) (hn : NoSep c (charSegs ss)) :
    keyOf allowPartial enforce i s = .segs ss ∧
      split c (join c (charSegs ss)) = charSegs ss := by
  refine ⟨by simp [keyOf_leaf hl, hb], split_join c _ ?_ hn⟩
  simpa [charSegs] using hne

/-- **Two items that reach one arm and print one key hold one segment list**, where both lists are
    lawful. The key decodes to the segments of its arm. -/
theorem leaf_key_injective (c : Char) {a b : List String}
    (ha : a ≠ []) (hb : b ≠ []) (hna : NoSep c (charSegs a)) (hnb : NoSep c (charSegs b))
    (h : join c (charSegs a) = join c (charSegs b)) : charSegs a = charSegs b :=
  join_injective c (by simpa [charSegs] using ha) (by simpa [charSegs] using hb) hna hnb h

/-! ## The collision of two arms -/

/-- **Two arms with equal leaves give one key to two items in different arms.** The items hold
    the literals `x` and `y`, the arms of the two literals are one arm, and the arm gives one key at
    the two items. -/
theorem collision {d : N} {arms : String → KeySpec N} {x y : String} {a : Arm N}
    (hx : arms x = .arm a) (hy : arms y = .arm a) (hi : i d = some x) (hi' : i' d = some y)
    (he : a.key allowPartial enforce i = a.key allowPartial enforce i') :
    keyOf allowPartial enforce i (.match_ d arms) =
      keyOf allowPartial enforce i' (.match_ d arms) := by
  simp [keyOf, select, hi, hi', hx, hy, he]

/-- **The key does not decode to its arm.** No function of the key gives the literal at both
    items. The ruled answer to the collision is a mark, because the model has no decoder to refuse
    for. -/
theorem not_decodable {d : N} {arms : String → KeySpec N} {x y : String} {a : Arm N}
    (hxy : x ≠ y) (hx : arms x = .arm a) (hy : arms y = .arm a) (hi : i d = some x)
    (hi' : i' d = some y) (he : a.key allowPartial enforce i = a.key allowPartial enforce i') :
    ¬ ∃ f : Out → String, f (keyOf allowPartial enforce i (.match_ d arms)) = x ∧
      f (keyOf allowPartial enforce i' (.match_ d arms)) = y := by
  rintro ⟨f, h1, h2⟩
  rw [collision hx hy hi hi' he] at h1
  exact hxy (h1.symm.trans h2)

/-- **A leaf that does not read the item meets the collision.** -/
theorem collision_const {d : N} {arms : String → KeySpec N} {x y : String} {full : Nat}
    {ps : List (Option Comp)} (hx : arms x = .arm (.leaf (.const full ps)))
    (hy : arms y = .arm (.leaf (.const full ps))) (hi : i d = some x) (hi' : i' d = some y) :
    keyOf allowPartial enforce i (.match_ d arms) =
      keyOf allowPartial enforce i' (.match_ d arms) :=
  collision hx hy hi hi' rfl

/-! ## The case of the owner -/

/-- An item of the owner's case: the attributes `TAG`, `SPECIE` and `BREED`. -/
def animal (tag specie breed : Option String) : Item String
  | "TAG" => tag
  | "SPECIE" => specie
  | "BREED" => breed
  | _ => none

/-- `TAG` is `OBJECT` or `ANIMAL`. Under `ANIMAL`, `SPECIE` is `CAT`, `DOG` or `HORSE`. Under `DOG`,
    `BREED` gives the key. -/
def ownerSpec : KeySpec String :=
  .match_ "TAG" (KeySpec.ofList
    [ ("OBJECT", .arm .null)
    , ("ANIMAL", .match_ "SPECIE" (KeySpec.ofList
        [ ("CAT", .arm .null)
        , ("DOG", .match_ "BREED" (KeySpec.ofList [("PUG", .arm (.leaf (.const 1 [some (.named "B" "pug")])))]))
        , ("HORSE", .arm .null) ])) ])

/-- The path of a dog item, and the arm that the flat match gives at the path. -/
theorem owner_path :
    trace (animal (some "ANIMAL") (some "DOG") (some "PUG")) ownerSpec = ["ANIMAL", "DOG", "PUG"] := by
  decide

/-- `SPECIE` exists only under `ANIMAL`: an object that holds a `SPECIE` still selects `null`. -/
theorem owner_object_ignores_specie :
    keyOf false false (animal (some "OBJECT") (some "DOG") none) ownerSpec = .nothing := by
  decide

/-- A dog with no `BREED` selects nothing, and the host throws. -/
theorem owner_dog_without_breed :
    keyOf false false (animal (some "ANIMAL") (some "DOG") none) ownerSpec = .refused := by
  decide

/-- A pug reaches the leaf, and the key is the segments of the leaf. -/
theorem owner_pug :
    keyOf false false (animal (some "ANIMAL") (some "DOG") (some "PUG")) ownerSpec =
      .segs ["B", "pug"] := by
  decide

/-- The two items of a collision: two literals, one arm. -/
def twin : KeySpec String :=
  .match_ "K" (KeySpec.ofList
    [("x", .arm (.leaf (.const 1 [some (.named "A" "1")]))),
     ("y", .arm (.leaf (.const 1 [some (.named "A" "1")])))])

/-- **The collision has an instance.** Two items with different literals print one key. -/
theorem twin_collides :
    keyOf false false (fun n => if n = "K" then some "x" else none) twin =
      keyOf false false (fun n => if n = "K" then some "y" else none) twin ∧
    keyOf false false (fun n => if n = "K" then some "x" else none) twin = .segs ["A", "1"] := by
  decide

end DerivedKey

end Calculus
