import Calculus.Merge
import Calculus.Orthogonality

/-!
# The meet

`Term.meet` is the intersection of two admissions, as a term. It is a derived function and not a
constructor: `some z` says a value satisfies `z` exactly when it satisfies both factors, `some
never` says nothing satisfies both, and `none` is a
refusal — the pair is one whose admission is a function rather than data, so no term states the
intersection. `held`, `legacy`, `custom` and `lazy` refuse on that ground at every partner, `opaq`
refuses where its closed form cannot be compared with an exact held set, and `refine` refuses at a
`closure`. A pair that admits a common value and stores it at two members has no meet either, and
that is a refusal and not an empty one: `string` and `decimal` both admit text, one writes `S` and
the other `N`, so `never` would claim they share no value when they share every value.

**The write side agrees only where both factors name a member**, and that is weaker than "all three
write the same way". `μSyn` answers `none` for two different reasons — a term that writes no value
at all (`never`) and a term that names no *single* stored member (`union`, `opaq`, `lazy`,
`custom`) — so a factor answering `none` constrains nothing. The two examples at the foot of this
file are the witnesses: `union [string, null] ∧ null` is `null` and `opaq ∧ string` is `string`,
and in each the meet names a member neither shared with its `none`-answering factor. The condition the
rows keep is that where both factors name a member they name the same one, and the meet names it
too; `string ∧ decimal` is refused by exactly that condition.

**The meet and the merge are two operations.** `Body.merge` (`Merge.lean`) joins two bodies over
*disjoint* names and is the record product: its held set is the product of the factors' held sets
through the split, and the map it admits is one neither factor admits. The meet intersects
admissions. `array(string) ∧ tuple(string 'a')` is `tuple(string 'a')` and is a meet;
`object {a} ⊗ object {b}` is `object {a, b}` and is a merge. The meet's object row does not call
`Body.merge`; only `Rest.merge` is shared, and the rests are the one place the two agree.

**An object's declared names meet by intersection.** `objAdmV` quantifies over the names the
*value* carries and `AdmRest` is `none` at `drop` and at `refuse` alike, so a closed object refuses
an undeclared name on the value side under either policy: the declared set is an upper bound. Two
upper bounds meet at their intersection. The required names unite, and a required name outside the
intersection makes the object `never`, because that name must be present and the other factor
refuses it.

The witness that the union of the declared names is wrong: `object {x : req string}` and
`object {y : req string}`, both `drop`, against the value `{x := "1", y := "2"}`. Each factor
refuses it, for the name the other declares. An object over the union of the two names admits it,
so the union rule answers `true` where both factors answer `false`.
-/

namespace Calculus


/-! ## Reading a field and a term -/

/-- Whether a term is the bottom, as a `Bool` the rows below branch on. -/
def Term.isNever : Term → Bool
  | .never => true
  | _ => false

/-- Whether a field's name must be present. `optional` is the only mark that admits absence, which
    is the reading `Body.spec` and `valPresentT` already take. -/
def Field.isReq : Field → Bool
  | .optional _ => false
  | _ => true

/-- Whether a field admits nothing at a name that must be present. An `optional` field at the
    bottom is not this: it is a name that must be absent, which is a body a value can satisfy. -/
def Field.isBottom : Field → Bool
  | .req t => t.isNever
  | .fallback t _ => t.isNever
  | .optional _ => false

/-- Whether a predicate is data a term can carry through a meet. `closure` is the caller's own
    function and is the one case `Pred` keeps open. -/
def Pred.isData : Pred → Bool
  | .closure _ => false
  | _ => true

/-- A union of what survived a distribution: nothing is the bottom, one survivor is itself, and
    the rest are a union again. -/
def Term.ofOptions : List Term → Term
  | [] => .never
  | [t] => t
  | ts => .union ts

/-- The names both bodies declare. `Finset.filter` and not `∩`: the intersection's membership API
    is not a sanctioned route to `Classical.choice`, and `Finset.mem_filter` is. -/
def Body.shared (a b : Body) : Finset Name := a.fields.filter (fun k => k ∈ b.fields)

/-- A shared name is one the left body declares. -/
theorem Body.mem_shared_left {a b : Body} {k : Name} (h : k ∈ Body.shared a b) : k ∈ a.fields :=
  (Finset.mem_filter.mp h).1

/-- …and one the right body declares. -/
theorem Body.mem_shared_right {a b : Body} {k : Name} (h : k ∈ Body.shared a b) : k ∈ b.fields :=
  (Finset.mem_filter.mp h).2

/-- Whether every name one body requires is a name the other declares. A required name the other
    factor refuses is a name that must be present and cannot be, which is the bottom. -/
def Body.reqShared (a b : Body) : Bool :=
  decide (∀ k : {k // k ∈ a.fields}, Field.isReq (a.at k) = true → k.1 ∈ b.fields)

/-- Both fields at a shared name are strictly shallower than their bodies — the inequality the
    object row's recursion needs, named once so the termination proof cites it rather than
    rebuilding it from two lemmas at each site. -/
theorem Body.depth_lt_shared (a b : Body) (k : {k // k ∈ Body.shared a b}) :
    Field.depth (a.at ⟨k.1, Body.mem_shared_left k.2⟩)
      + Field.depth (b.at ⟨k.1, Body.mem_shared_right k.2⟩) < Body.depth a + Body.depth b := by
  have h1 := Body.depth_lt_field a ⟨k.1, Body.mem_shared_left k.2⟩
  have h2 := Body.depth_lt_field b ⟨k.1, Body.mem_shared_right k.2⟩
  omega

/-- A list of answers, as one answer: `none` where any cell refused. Outside the recursion, so
    the rows below reach a list through `List.attach` and a `map` rather than through a mutual
    companion — which is what makes every recursive call strictly shallower in one measure. -/
def allSome {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some x :: rest => (allSome rest).map (x :: ·)

/-- The termination argument every row of the meet uses, written once.

    The measure is a pair: the sum of the two arguments' depths, and a rank that separates a body
    from the field function it reads at the same depth. So a goal is a `Prod.Lex`, and the first
    alternative that fits is the one that names why the call is shallower — a union's option, a
    tuple's position, a declared field, or the rest policy's codec. -/
macro (name := meetWf) "meet_wf" : tactic => `(tactic|
  (all_goals
    first
      | decreasing_tactic
      | (apply Prod.Lex.left
         first
           | exact Body.depth_lt_shared _ _ _
           | exact Nat.add_lt_add_right (Body.depth_lt_field _ _) _
           | (have hle := Term.depth_le_depthL ‹_ ∈ _›
              simp only [Term.depth]
              omega)
           | (have hz := List.of_mem_zip ‹_ ∈ _›
              have h1 := Term.depth_le_depthL hz.1
              have h2 := Term.depth_le_depthL hz.2
              simp only [Term.depth]
              omega)
           | (simp only [Field.depth, Term.depth, Body.depth, Term.depthO]
              omega)
           | exact Nat.add_lt_add_right (Body.depth_lt_rest _ (by assumption)) _
           | omega)
      | (apply Prod.Lex.right
         omega)))

/-! ## The meet -/

mutual

/-- **The intersection of two admissions, as a term.** One row per pair of constructors. -/
def Term.meet : Term → Term → Option Term
  -- the bottom absorbs, on either side
  | .never, _ => some .never
  | _, .never => some .never
  -- **the four whose admission is a function and not data.** A reader cannot say what they admit
  -- without running them, so no term states the intersection.
  | .held _ _ _, _ | .legacy _ _, _ | .custom _ _, _ | .lazy _, _ => none
  | _, .held _ _ _ | _, .legacy _ _ | _, .custom _ _ | _, .lazy _ => none
  -- **a union distributes**, on either side: meet each option, drop the bottoms, refuse where a
  -- cell refuses. What survives is a union again, one survivor, or the bottom.
  | .union os, y =>
      (allSome (os.attach.map fun ⟨t, _⟩ => Term.meet t y)).map
        (fun zs => Term.ofOptions (zs.filter (fun z => !z.isNever)))
  | x, .union os =>
      (allSome (os.attach.map fun ⟨t, _⟩ => Term.meet t x)).map
        (fun zs => Term.ofOptions (zs.filter (fun z => !z.isNever)))
  -- **a refinement conjoins**: the predicate is data, so it rides on the meet of the inner terms.
  | .refine x p, y => if p.isData then (Term.meet x y).map (fun z => .refine z p) else none
  | x, .refine y p => if p.isData then (Term.meet x y).map (fun z => .refine z p) else none
  -- the ground bases: the same base is itself, and two different value kinds meet nowhere
  | .string, .string => some .string
  | .boolean, .boolean => some .boolean
  | .binary, .binary => some .binary
  | .null, .null => some .null
  | .number, .number => some .number
  | .decimal, .decimal => some .decimal
  -- **`string` and `decimal` part on the stored side.** Both admit text; `string` writes `S` and
  -- `decimal` writes `N`, so a value they share is stored two ways and there is no meet. The
  -- literal rows below repeat this, because a literal at either base inherits the pair.
  | .string, .decimal => none
  | .decimal, .string => none
  -- **The `string` family and the `decimal` family never meet.** A family is the base, a literal
  -- at it, and a `refine` over either: every member writes `.str`, and the two store it at `S`
  -- and at `N`. So every cell putting one family against the other answers `none`, and a
  -- container inherits that answer through its element, because `none` survives `.map` and
  -- `allSome`. `never` is the empty intersection alone, and this pair shares every stored
  -- numeral.
  --
  -- **a literal against a base is the literal at that base, and nothing at any other** — except
  -- that pair, which refuses rather than answering the bottom.
  | .literal k v, .string =>
      match k, v with
      | .string, v => some (.literal .string v)
      | .decimal, _ => none
      | _, _ => some .never
  | .string, .literal k v =>
      match k, v with
      | .string, v => some (.literal .string v)
      | .decimal, _ => none
      | _, _ => some .never
  | .literal k v, .boolean => if k = .boolean then some (.literal k v) else some .never
  | .boolean, .literal k v => if k = .boolean then some (.literal k v) else some .never
  | .literal k v, .binary => if k = .binary then some (.literal k v) else some .never
  | .binary, .literal k v => if k = .binary then some (.literal k v) else some .never
  | .literal k v, .null => if k = .null then some (.literal k v) else some .never
  | .null, .literal k v => if k = .null then some (.literal k v) else some .never
  | .literal k v, .number => if k = .number then some (.literal k v) else some .never
  | .number, .literal k v => if k = .number then some (.literal k v) else some .never
  | .literal k v, .decimal =>
      match k, v with
      | .decimal, v => some (.literal .decimal v)
      | .string, _ => none
      | _, _ => some .never
  | .decimal, .literal k v =>
      match k, v with
      | .decimal, v => some (.literal .decimal v)
      | .string, _ => none
      | _, _ => some .never
  -- **two literals: the same value, or nothing.**
  | .literal k v, .literal k' v' => Term.meetLit k v k' v'
  -- the containers
  | .array x, .array y => (Term.meet x y).map .array
  | .record x, .record y => (Term.meet x y).map .record
  -- **`set string` and `set decimal` are `string ∧ decimal` one container out.** Both write a
  -- `strSet` and they store it at `SS` and at `NS`, so they share every set of stored numerals
  -- and have no meet. `never` would claim they share none. Every other pair of bases writes a
  -- different `Value` constructor and so shares nothing.
  | .set .string, .set .decimal => none
  | .set .decimal, .set .string => none
  | .set b, .set b' => if b = b' then some (.set b) else some .never
  | .opaq l, .opaq l' => some (.opaq (l && l'))
  -- **an array against a tuple is the tuple**, each declared position and the tail met with the
  -- array's one element term.
  | .array x, .tuple ts tail =>
      match allSome (ts.attach.map fun ⟨t, _⟩ => Term.meet t x),
            (match tail with
             | none => some none
             | some t => (Term.meet t x).map some) with
      | some vs, some tl => some (.tuple vs tl)
      | _, _ => none
  | .tuple ts tail, .array x =>
      match allSome (ts.attach.map fun ⟨t, _⟩ => Term.meet t x),
            (match tail with
             | none => some none
             | some t => (Term.meet t x).map some) with
      | some vs, some tl => some (.tuple vs tl)
      | _, _ => none
  -- **two tuples meet by arity.** Equal arity meets positionwise and meets the tails. Unequal
  -- arity with no tail on either side admits no common array, which is the bottom. Unequal arity
  -- *with* a tail refuses: aligning a declared position against a tail position is a rule this
  -- development has not stated, and answering it here would state it by accident.
  | .tuple ts tail, .tuple us tail' =>
      if ts.length = us.length then
        match allSome ((ts.zip us).attach.map fun ⟨p, _⟩ => Term.meet p.1 p.2),
              (match tail, tail' with
               | none, none => some none
               | some t, some u => (Term.meet t u).map some
               | _, _ => none) with
        | some vs, some tl => some (.tuple vs tl)
        | _, _ => none
      else if tail.isNone && tail'.isNone then some .never
      else none
  -- **an object against a record** holds every name through one codec on one side and through a
  -- declared field on the other, so only a `codec` rest meets a record.
  | .object b, .record x => Body.meetRec b x
  | .record x, .object b => Body.meetRec b x
  | .object a, .object b => Body.meetTerm a b
  -- **`opaque` against a ground base.** It admits every value of every self-identifying kind, so
  -- at `string`, `boolean`, `binary` and `null` the base is the finer term. `decimal` refuses, for
  -- the reason `string ∧ decimal` refuses: one writes `S` and the other `N`. `number` follows the
  -- policy, the lossy one holding every number and the `refuse` one none.
  | .opaq _, .string => some .string
  | .string, .opaq _ => some .string
  | .opaq _, .boolean => some .boolean
  | .boolean, .opaq _ => some .boolean
  | .opaq _, .binary => some .binary
  | .binary, .opaq _ => some .binary
  | .opaq _, .null => some .null
  | .null, .opaq _ => some .null
  | .opaq l, .number => if l then some .number else some .never
  | .number, .opaq l => if l then some .number else some .never
  | .opaq _, _ => none
  | _, .opaq _ => none
  -- everything left is two constructors that write different value kinds
  | _, _ => some .never
termination_by x y => (Term.depth x + Term.depth y, 1)
-- the one inequality the default tactic does not see: a union's options are one layer below the
-- union, and `Term.depth`'s row is where that is written
decreasing_by meet_wf

/-- Two literals: the same value at the same base, or nothing.

    `number` refuses, because `DecidableEq WFDouble` is a field of `numericHost` and a row here
    would be noncomputable — the reason `OrthL` declines at that base. -/
def Term.meetLit : (k : GroundKind) → k.Carrier → (k' : GroundKind) → k'.Carrier → Option Term
  | .string, v, .string, v' => if v = v' then some (.literal .string v) else some .never
  | .decimal, v, .decimal, v' => if v = v' then some (.literal .decimal v) else some .never
  | .boolean, v, .boolean, v' => if v = v' then some (.literal .boolean v) else some .never
  | .binary, v, .binary, v' => if v = v' then some (.literal .binary v) else some .never
  -- `Unit` has one inhabitant, so two null literals name the same value
  | .null, v, .null, _ => some (.literal .null v)
  | .number, _, .number, _ => none
  -- the same shared pair as the rows above, with both sides pinned
  | .string, _, .decimal, _ => none
  | .decimal, _, .string, _ => none
  | _, _, _, _ => some .never






/-- Two fields at one name. `req` against `optional` is `req`: the name must be present for one
    factor, so it must be present for the meet. `fallback` refuses against any mark, its default
    being a value the other factor has not been asked about. -/
def Field.meet : Field → Field → Option Field
  | .req x, .req y => (Term.meet x y).map .req
  | .req x, .optional y => (Term.meet x y).map .req
  | .optional x, .req y => (Term.meet x y).map .req
  | .optional x, .optional y => (Term.meet x y).map .optional
  | _, _ => none
termination_by f g => (Field.depth f + Field.depth g, 1)
decreasing_by meet_wf

/-- Two bodies, over the names both declare.

    The declared set is the intersection and the required set is the union, which is what two upper
    bounds meet to. A required name the other factor does not declare makes the object the bottom:
    the name must be present, and the other factor refuses a value carrying it.

    A field whose terms meet to the bottom is kept rather than dropped. At `optional` the two read
    the same — a name the body does not declare and a name at `optional never` are both refused
    when present — and keeping it leaves the key set fixed for every row below. At `req` it is the
    body that becomes the bottom, which is the `isBottom` test. -/
def Body.meetTerm (a b : Body) : Option Term :=
  if Body.reqShared a b && Body.reqShared b a then
    if Body.meetOk a b then
      match Rest.merge a.rest b.rest with
      | some r =>
          if decide (∀ k, Field.isBottom (Body.meetField a b k) = false) then
            some (.object (.mk (Body.shared a b) (fun k => Body.meetField a b k) r))
          else some .never
      | none => none
    else none
  else some .never
termination_by (Body.depth a + Body.depth b, 1)
decreasing_by meet_wf

/-- One field of the meet of two bodies, total, with the refusal read separately by
    {@link Body.meetOk}. Total rather than partial so the body below carries a plain function on
    its key set instead of a proof-dependent one; where `Body.meetOk` holds, this is the meet. -/
def Body.meetField (a b : Body) (k : {k // k ∈ Body.shared a b}) : Field :=
  (Field.meet (a.at ⟨k.1, Body.mem_shared_left k.2⟩) (b.at ⟨k.1, Body.mem_shared_right k.2⟩)).getD
    (.optional .never)
termination_by (Body.depth a + Body.depth b, 0)
decreasing_by meet_wf

/-- …and whether every shared name's two fields meet at all. -/
def Body.meetOk (a b : Body) : Bool :=
  decide (∀ k : {k // k ∈ Body.shared a b},
    (Field.meet (a.at ⟨k.1, Body.mem_shared_left k.2⟩)
      (b.at ⟨k.1, Body.mem_shared_right k.2⟩)).isSome = true)
termination_by (Body.depth a + Body.depth b, 0)
decreasing_by meet_wf

/-- A field met with one term, the mark kept. The record's value term says what every name holds,
    and it says nothing about whether a name is present, so the object's mark survives. -/
def Field.meetT : Field → Term → Option Field
  | .req x, y => (Term.meet x y).map .req
  | .optional x, y => (Term.meet x y).map .optional
  | .fallback _ _, _ => none
termination_by f x => (Field.depth f + Term.depth x, 1)
decreasing_by meet_wf

/-- One field of an object met with a record's value term, total on the same terms as
    {@link Body.meetField}. -/
def Body.meetRecField (b : Body) (x : Term) (k : {k // k ∈ b.fields}) : Field :=
  (Field.meetT (b.at k) x).getD (.optional .never)
termination_by (Body.depth b + Term.depth x, 0)
decreasing_by meet_wf

/-- …and whether every declared field meets it. -/
def Body.meetRecOk (b : Body) (x : Term) : Bool :=
  decide (∀ k : {k // k ∈ b.fields}, (Field.meetT (b.at k) x).isSome = true)
termination_by (Body.depth b + Term.depth x, 0)
decreasing_by meet_wf

/-- An object against a record. Only a `codec` rest reads an undeclared name the way a record
    does, so the other two refuse; the record's value term meets every declared field and the
    rest's own codec. -/
def Body.meetRec (b : Body) (x : Term) : Option Term :=
  match _hr : b.rest with
  | .codec t =>
      if Body.meetRecOk b x then
        match Term.meet t x with
        | some r =>
            if decide (∀ k, Field.isBottom (Body.meetRecField b x k) = false) then
              some (.object (.mk b.fields (fun k => Body.meetRecField b x k) (.codec r)))
            else some .never
        | none => none
      else none
  | _ => none
termination_by (Body.depth b + Term.depth x, 1)
decreasing_by meet_wf

end

/-! ## What the rows answer

Worked pairs, one per class, checked by the equation compiler rather than described. The first is
the example the meet exists for: an array admits every length and a tuple pins one, so the meet is
the tuple. -/

example : Term.meet (.array .string) (.tuple [.literal .string "a"] none)
    = some (.tuple [.literal .string "a"] none) := by simp [Term.meet, allSome]

/-- Two value kinds that never meet. -/
example : Term.meet .string .number = some .never := by simp [Term.meet]

/-- A literal against its own base is the literal: the finer of the two. -/
example : Term.meet (.literal .string "a") .string = some (.literal .string "a") := by
  simp [Term.meet]

/-- …and against another value of the same base, nothing. -/
example : Term.meet (.literal .string "a") (.literal .string "b") = some .never := by
  simp [Term.meet, Term.meetLit]

/-- `string` and `decimal` admit the same text and store it at different members, so the pair has
    no meet rather than an empty one. -/
example : Term.meet .string .decimal = none := by simp [Term.meet]

/-- **The same refusal reaches a literal at either base**, because a `decimal` literal's values
    are `.str`. These four rows answered the bottom, which claims the pair shares no value while
    it shares one, and the two literals below are the same mistake one level further in. -/
example : Term.meet (.literal .decimal ⟨"1", by decide⟩) .string = none := by simp [Term.meet]

example : Term.meet (.literal .string "1") .decimal = none := by simp [Term.meet]

example : Term.meet (.literal .string "1") (.literal .decimal ⟨"1", by decide⟩) = none := by
  simp [Term.meet, Term.meetLit]

/-- The value the refusal is about: both terms admit it, and they store it at `S` and at `N`. -/
example : Adm (.literal .decimal ⟨"1", by decide⟩) (.str "1") = true := by
  simp [Adm, AdmLit, inL]
  decide

example : Adm Term.string (.str "1") = true := by simp [Adm]

/-- A literal at a base that shares nothing with the partner is still the bottom. -/
example : Term.meet (.literal .string "1") .boolean = some .never := by simp [Term.meet]

/-- A refinement carries the cell, and so does a container: `none` survives `.map`. -/
example : Term.meet (.refine .string (.members .string ⟨{"1"}, Finset.singleton_nonempty _⟩))
    .decimal = none := by simp [Term.meet]

example : Term.meet (.array .string) (.array .decimal) = none := by simp [Term.meet]

/-- …while two terms that write different constructors are still the bottom, container or not. -/
example : Term.meet .number .decimal = some .never := by simp [Term.meet]

/-- **The null point needs no row of its own.** A null point is the null term joined by a union,
    so the union rows distribute over it and the ground rows answer each cell. This is the pair
    that had a row and got it wrong: the wrapper this replaced dropped the point at every
    partner but another wrapper and a `null`, and `opaq` holds the point. -/
example : Term.meet (.union [.string, .null]) (.opaq true) = some (.union [.string, .null]) := by
  simp [Term.meet, allSome, Term.ofOptions, Term.isNever]

/-- …and against the null term alone the string cell is the bottom, so one option survives. -/
example : Term.meet (.union [.string, .null]) .null = some .null := by
  simp [Term.meet, allSome, Term.ofOptions, Term.isNever]

/-- …and the same refusal one container out. A set of stored numerals satisfies both bases, so
    the pair shares values and has no meet. -/
example : Term.meet (.set .string) (.set .decimal) = none := by simp [Term.meet]

example : Adm (.set .string) (.strSet ⟨{"1"}, Finset.singleton_nonempty _⟩) = true := by
  simp [Adm, SetBase.adm]

example : Adm (.set .decimal) (.strSet ⟨{"1"}, Finset.singleton_nonempty _⟩) = true := by
  simp [Adm, SetBase.adm, isStored, Numeral.Stored]
  decide

/-! ### Why the write-agreement condition is conditional

Two meets that are not the bottom and whose factor names no member. They are why the condition the
rows keep is "where both factors name a member" rather than "all three name the same member": a
`μSyn` of `none` is a term that names no single stored member, not a term that writes nothing. -/

example : μSyn (Term.union [.string, .null]) = none := by simp [μSyn, μSynList, unanimous]

example : ¬ (μSyn Term.null = μSyn (Term.union [.string, .null])) := by
  simp [μSyn, μSynList, unanimous]

example : Term.meet (.opaq true) .string = some .string := by simp [Term.meet]

example : ¬ (μSyn Term.string = μSyn (Term.opaq true)) := by simp [μSyn]

end Calculus
