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

**The same on the read side, and `never` is the empty intersection of BOTH halves.** `number` and
`decimal` write different value kinds, so they share no value and the bottom is right about the
write side. They read the same member `N`, so they share every stored numeral the host re-reads
and the bottom is wrong about the read side. A pair disjoint on one half only is not disjoint,
which is why `Orth1` conjoins the two occupancies; `never` is for a pair disjoint on both, and
everything else refuses. `decimal` is the base that meets `string` on values and `number` on
members, and both crosses refuse.

**The write side agrees only where both factors name a member**, and that is weaker than "all three
write the same way". `μSyn` answers `none` for two different reasons — a term that writes no value
at all (`never`) and a term that names no *single* stored member (`union`, `opaq`, `lazy`,
`custom`) — so a factor answering `none` constrains nothing. The two examples at the foot of this
file are the witnesses: `union [string, null] ∧ null` is `null` and `opaq ∧ string` is `string`,
and in each the meet names a member neither shared with its `none`-answering factor.

The condition the rows keep reads off the MEET and not off the factors: where the meet names a
member, any member a factor names is that one, which is `meet_writes`. The other direction is
false and the two examples beside that theorem are why. A bottom names no member, so two factors
naming different members meet at a term that names none — `literal boolean ∧ string` is the
bottom, and `BOOL` and `S` never have to agree. Excluding the bottom does not repair it either,
because a refinement over the bottom is not the bottom: `refine string p ∧ boolean` is
`refine never p`, which names no member and is not `never`.

**A union carries a certificate, and the meet reads it.** `Adm (.union os)` is `selOptV`, which
admits where *exactly one* option admits structurally. That is the join of the options' admissions
only when the options carry `unionOk`: pairwise `Orth`, so no value is refused for being admitted
twice, and no open object, so each option's structural test is its row. Without it the meet has
nothing to state, and the two examples at the foot of this file are the two ways it fails.

**The meet and the merge are two operations.** `Body.merge` (`Merge.lean`) joins two bodies over
*disjoint* names and is the record product: its held set is the product of the factors' held sets
through the split, and the map it admits is one neither factor admits. The meet intersects
admissions. `array(string) ∧ tuple(string 'a')` is `tuple(string 'a')` and is a meet;
`object {a} ⊗ object {b}` is `object {a, b}` and is a merge. The meet's object row does not call
`Body.merge`; only `Rest.merge` is shared, and the rests are the one place the two agree.

**An object's declared names meet by intersection, and only where both halves read the set the
same way.** `objAdmV` quantifies over the names the *value* carries and `AdmRest` is `none` at
`drop` and at `refuse` alike, so a closed object refuses an undeclared name on the value side under
either policy: the declared set is an upper bound. Two upper bounds meet at their intersection. The
required names unite, and **with both rests closed** a required name outside the intersection makes
the object `never`, because that name must be present and the other factor refuses it. An *open*
factor refuses no name: its rest holds one the factor does not declare. So the rests are read
first, and a `codec` on either side answers the refusal before the required-name test is consulted.

The witness that the union of the declared names is wrong: `object {x : req string}` and
`object {y : req string}`, both `drop`, against the value `{x := "1", y := "2"}`. Each factor
refuses it, for the name the other declares. An object over the union of the two names admits it,
so the union rule answers `true` where both factors answer `false`.

**A shared name's two fields meet at the stronger mark, and an unshared one parts the halves.**
A mark says whether the name must be present when the object is written and when it is read, and
those two bits are not the same bit: `fallback` forces the write and not the read, because its
stand-in answers a read that finds no name. Intersecting conjoins each bit, so a shared name meets
at the stronger of the two marks — `optional < fallback < req` — which is `Field.meet`. A name one
body declares and the other does not has no second mark to join: under a closed rest a `req` name
makes the object the bottom, because it must be written and the partner refuses it, and a
`fallback` name refuses outright, because the write side is empty there and the read side is not.

**The intersection is wrong on the read side under `drop`, so that pair refuses too.** `objAdmA`
filters by `keepT`, and `keepT` at `drop` keeps the declared names alone, so a `drop` object
*skips* an undeclared name rather than refusing it. That is what `drop` means for a read. The
declared set therefore bounds the read from below where it bounds the write from above, and an
intersection is the meet of two upper bounds and the join of two lower ones. The same two bodies
each read `{x := true}`, because each skips the name the other declares, while the intersection
declares neither name and reads every map. `Body.dropFits` states the condition under which the two
halves agree: a `drop` factor must declare every name the other factor declares. Two `drop` factors
must then declare the same names, a `drop` factor against a `refuse` one must declare every name
the `refuse` one declares, and two `refuse` factors are free. Every other pair refuses, the
required-name test included, because a `drop` factor skips the required name it does not declare.
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

/-- Pairwise `Orth` over a list. Lives here rather than beside `Orth` because the meet is its one
    caller. -/
def orthAll : List Term → Bool
  | [] => true
  | t :: ts => ts.all (fun u => Orth t u) && orthAll ts

/-- Whether a field's presence rule is the same on both halves. `req` must be present for both
    and `optional` may be absent for both. `fallback` parts them: the write side writes the name
    and the read side reads the stand-in when the name is absent. -/
def Field.presenceAgrees : Field → Bool
  | .fallback _ _ => false
  | _ => true

/-- Whether an object option's two halves answer the same question about names, which is what
    `keysOk` needs in order to be that option's row. `keysOk` is the write side's name test, and
    a union dispatches on it, so a read that disagrees with it is a read the union refuses.

    Two names part the halves. An **undeclared** name: `refuse` refuses it on both halves, and
    `drop` refuses it when it writes and skips it when it reads. A **declared and absent** name:
    `req` must be present for both and `optional` may be absent for both, while `fallback` must
    be written and reads to its stand-in, so `keysOk` requires the name and `reqPresentT` does
    not. A term that is not an object declares no names and the question does not arise. -/
def objectNamesAgree : Term → Bool
  | .object b =>
      (match b.rest with | .refuse => true | _ => false) &&
      decide (∀ k : {k // k ∈ b.fields}, Field.presenceAgrees (b.at k) = true)
  | _ => true

/-- **The certificate a union must carry for its admission to be the join of its options'.**
    Three conditions, and each answers a way the admission can fall short of the join.

    Pairwise `Orth` bounds the structural admitters at one, so nothing is refused for being
    admitted twice.

    No *open* object. `keysOk` refuses a name the object does not declare, and an open object
    holds that name through its rest, so a union carrying one refuses an input that option admits.

    Every object option's two halves agree about names. This is the same sentence one half over,
    twice. A `drop` object skips an undeclared name on the read side, and `keysOk` refuses that
    name just as it does the one an open object holds; `Rest.isOpen` is `false` at `drop`, so the
    second condition does not catch it. A `fallback` field reads to its stand-in when its name is
    absent, and `keysOk` requires that name because the write side writes it. The write side needs
    neither: `objAdmV` has no keep filter and `valPresentT` counts a `fallback` as present. -/
def unionOk (os : List Term) : Bool :=
  orthAll os && os.all (fun t => !t.isOpenObject) && os.all objectNamesAgree

/-- The certificate, in the form the separation lemmas take. -/
theorem pairwise_of_orthAll : ∀ {ts : List Term}, orthAll ts = true →
    List.Pairwise (fun x y => Orth x y = true) ts
  | [], _ => .nil
  | _ :: _, h => by
      simp only [orthAll, Bool.and_eq_true, List.all_eq_true] at h
      exact .cons (fun u hu => h.1 u hu) (pairwise_of_orthAll h.2)

/-- A union of what survived a distribution: nothing is the bottom, one survivor is itself, and
    the rest are a union again. -/
def Term.ofOptions : List Term → Term
  | [] => .never
  | [t] => t
  | ts => .union ts

/-- …and the answer the meet gives at a union: the survivors, where both the options met and
    the survivors carry the certificate. The meet is the lattice's meet, and an uncertified
    union is not in the lattice, so the pair has no meet to state. Both sides are tested and
    not one: `Body.meetRec` answers an OPEN object, so a certified list of options can meet to
    an uncertified one. -/
def Term.ofOptionsGuarded (os ts : List Term) : Option Term :=
  if unionOk os && unionOk ts then some (Term.ofOptions ts) else none

/-- The names both bodies declare. `Finset.filter` and not `∩`: the intersection's membership API
    is not a sanctioned route to `Classical.choice`, and `Finset.mem_filter` is. -/
def Body.shared (a b : Body) : Finset Name := a.fields.filter (fun k => k ∈ b.fields)

/-- A shared name is one the left body declares. -/
theorem Body.mem_shared_left {a b : Body} {k : Name} (h : k ∈ Body.shared a b) : k ∈ a.fields :=
  (Finset.mem_filter.mp h).1

/-- …and one the right body declares. -/
theorem Body.mem_shared_right {a b : Body} {k : Name} (h : k ∈ Body.shared a b) : k ∈ b.fields :=
  (Finset.mem_filter.mp h).2

/-- Whether every name one body requires is a name the other declares. **A bottom test only
    against a factor that refuses the name on both halves**: a `codec` rest holds the name, and a
    `drop` rest refuses it on the write side and skips it on the read side. So `Body.meetTerm`
    reads the rests first, and puts the pair to `Body.dropFits` before it consults this test. -/
def Body.reqShared (a b : Body) : Bool :=
  decide (∀ k : {k // k ∈ a.fields}, Field.isReq (a.at k) = true → k.1 ∈ b.fields)

/-- Whether a field carries a stand-in. -/
def Field.isFallback : Field → Bool
  | .fallback _ _ => true
  | _ => false

/-- Whether every `fallback` name one body declares is a name the other declares too. The cell
    where it fails is the one that refuses: a stand-in name the partner does not declare is a name
    the write side must write and the partner refuses, so the pair is empty on the write side,
    while the read side reads the stand-in and needs no name at all. -/
def Body.fbShared (a b : Body) : Bool :=
  decide (∀ k : {k // k ∈ a.fields}, Field.isFallback (a.at k) = true → k.1 ∈ b.fields)

/-- Whether a `drop` factor declares every name the other factor declares. The declared set is an
    upper bound on the write side, where an undeclared name is refused, and a lower bound on the
    read side under `drop`, where an undeclared name is skipped. The intersection is the meet of
    two upper bounds and the join of two lower ones, so the two halves agree only where a `drop`
    factor's declared set contains the other's. -/
def Body.dropFits (a b : Body) : Bool :=
  match a.rest with
  | .drop => decide (∀ k ∈ b.fields, k ∈ a.fields)
  | _ => true

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

-- The presence table added five rows to `Field.meet`, and each one puts another goal to
-- `meet_wf`. The default budget is reached inside the termination proof of the block, not inside
-- any proof about it.
set_option maxHeartbeats 1000000 in
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
  -- **a certified union distributes**, on either side: meet each option, drop the bottoms,
  -- refuse where a cell refuses. What survives is a union again, one survivor, or the bottom.
  -- Both lists are put to `unionOk` and the pair refuses where either fails, because a union
  -- whose admission is not the join of its options' is not in the lattice and has no meet to
  -- state. Both sides are tested: `Body.meetRec` answers an open object, so certified options
  -- can meet to an uncertified list.
  | .union os, y =>
      (allSome (os.attach.map fun ⟨t, _⟩ => Term.meet t y)).bind
        (fun zs => Term.ofOptionsGuarded os (zs.filter (fun z => !z.isNever)))
  | x, .union os =>
      (allSome (os.attach.map fun ⟨t, _⟩ => Term.meet t x)).bind
        (fun zs => Term.ofOptionsGuarded os (zs.filter (fun z => !z.isNever)))
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
  -- **The `number` family and the `decimal` family never meet either**, and for the other half
  -- of the rule: one member `N`, different slots, so the pair stores nothing together and reads
  -- a stored numeral together. Every cell pairing the two families answers `none`, and the
  -- containers inherit it the same way.
  --
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
  | .literal k v, .number =>
      match k, v with
      | .number, v => some (.literal .number v)
      | .decimal, _ => none
      | _, _ => some .never
  | .number, .literal k v =>
      match k, v with
      | .number, v => some (.literal .number v)
      | .decimal, _ => none
      | _, _ => some .never
  | .literal k v, .decimal =>
      match k, v with
      | .decimal, v => some (.literal .decimal v)
      | .string, _ => none
      | .number, _ => none
      | _, _ => some .never
  | .decimal, .literal k v =>
      match k, v with
      | .decimal, v => some (.literal .decimal v)
      | .string, _ => none
      | .number, _ => none
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
  | .set .number, .set .decimal => none
  | .set .decimal, .set .number => none
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
  -- **The `number` family and the `decimal` family never meet.** They write different value
  -- kinds, so the bottom is right about the write side, and they read the same member `N`, so
  -- the bottom is wrong about the read side: every stored numeral the host re-reads is an
  -- attribute both admit. A pair that shares an attribute has no meet, for the reason a pair
  -- that shares a value has none.
  | .number, .decimal => none
  | .decimal, .number => none
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
  -- the same shared pairs as the rows above, with both sides pinned: `string` shares values
  -- with `decimal`, and `number` shares the member `N` with it
  | .string, _, .decimal, _ => none
  | .decimal, _, .string, _ => none
  | .number, _, .decimal, _ => none
  | .decimal, _, .number, _ => none
  | _, _, _, _ => some .never






/-- **Two fields at one name: the meet of the terms, at the stronger mark.**

    A mark carries two presence bits, whether the name must be present when the object is
    *written* and whether it must be present when the object is *read*. `optional` forces neither,
    `fallback` forces the write alone, because its stand-in answers a read that finds no name, and
    `req` forces both. Intersecting admissions conjoins constraints, so each bit is a join, and
    the three marks are a chain under it: `optional < fallback < req`. The mark of the meet is the
    stronger of the two, and the pair "read forces, write does not" names no mark because no mark
    has it.

    So `req` against a `fallback` is `req` and the stand-in goes: `req` forces the name present, so
    a read never finds it missing and never reaches the stand-in. `optional` against a `fallback`
    is that `fallback`, which is the only mark forcing the write and not the read.

    **Two `fallback` fields refuse, and that is a defect and not a rule.** They meet at the same
    mark whenever their stand-ins agree, and `Value` has no `DecidableEq` in this tree, so the row
    cannot ask. `Term.meetLit` declines at `number` for the same shape one type down, and
    `docs/defects.md` carries the pair as one entry. -/
def Field.meet : Field → Field → Option Field
  | .req x, .req y => (Term.meet x y).map .req
  | .req x, .optional y => (Term.meet x y).map .req
  | .optional x, .req y => (Term.meet x y).map .req
  | .req x, .fallback y _ => (Term.meet x y).map .req
  | .fallback x _, .req y => (Term.meet x y).map .req
  | .optional x, .optional y => (Term.meet x y).map .optional
  | .optional x, .fallback y d => (Term.meet x y).map (.fallback · d)
  | .fallback x d, .optional y => (Term.meet x y).map (.fallback · d)
  | .fallback _ _, .fallback _ _ => none
termination_by f g => (Field.depth f + Field.depth g, 1)
decreasing_by meet_wf

/-- Two bodies, over the names both declare.

    The rests decide first. `Rest.merge` answers `none` at a codec on either side, and an open
    factor is one that holds a name it does not declare, so the required-name test below is a
    bottom test only once both rests are closed.

    The declared set is the intersection and the required set is the union, which is what two upper
    bounds meet to. With both rests closed, a required name the other factor does not declare makes
    the object the bottom: the name must be present, and the other factor refuses a value carrying
    it.

    **The declared set is an upper bound on the write side only.** Under `drop` the read side skips
    an undeclared name rather than refusing it, so the declared set bounds the read from below and
    the intersection is the join there. `Body.dropFits` refuses the pair where the two halves
    disagree, and the required-name test below is a bottom test only once it holds: a `drop` factor
    that does not declare a required name skips it rather than refusing it.

    A field whose terms meet to the bottom is kept rather than dropped. At `optional` the two read
    the same — a name the body does not declare and a name at `optional never` are both refused
    when present — and keeping it leaves the key set fixed for every row below. At `req` it is the
    body that becomes the bottom, which is the `isBottom` test. -/
def Body.meetTerm (a b : Body) : Option Term :=
  match Rest.merge a.rest b.rest with
  | some r =>
      if Body.fbShared a b && Body.fbShared b a then
        if Body.dropFits a b && Body.dropFits b a then
          if Body.reqShared a b && Body.reqShared b a then
            if Body.meetOk a b then
              if decide (∀ k, Field.isBottom (Body.meetField a b k) = false) then
                some (.object (.mk (Body.shared a b) (fun k => Body.meetField a b k) r))
              else some .never
            else none
          else some .never
        else none
      else none
  | none => none
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

/-- **`number` and `decimal` refuse too, and for the other half of the rule.** They write
    different value kinds, so the bottom is right about what they store together — nothing. They
    read the same member `N`, so the bottom is wrong about what they read together: a stored
    numeral the host re-reads is an attribute both admit. A pair that shares an attribute has no
    meet, for the reason a pair that shares a value has none. -/
example : Term.meet .number .decimal = none := by simp [Term.meet]

example : Term.meet (.set .number) (.set .decimal) = none := by simp [Term.meet]

/-- The attribute the refusal is about: both terms read it, and the bottom reads nothing. -/
example (x : WFNumeral) (h : Numeral.Stored x.1 = true) : AdmA Term.decimal (.n x) = true := h

/-- **The null point needs no row of its own.** A null point is the null term joined by a union,
    so the union rows distribute over it and the ground rows answer each cell. This is the pair
    that had a row and got it wrong: the wrapper this replaced dropped the point at every
    partner but another wrapper and a `null`, and `opaq` holds the point. -/
example : Term.meet (.union [.string, .null]) (.opaq true) = some (.union [.string, .null]) := by
  simp [Term.meet, allSome, Term.ofOptions, Term.ofOptionsGuarded, unionOk, orthAll,
    Orth, Orth1, occV, occA, occOnly, Slot.all, Member.all, Term.isNever, Term.isOpenObject,
    objectNamesAgree]

/-- …and against the null term alone the string cell is the bottom, so one option survives. -/
example : Term.meet (.union [.string, .null]) .null = some .null := by
  simp [Term.meet, allSome, Term.ofOptions, Term.ofOptionsGuarded, unionOk, orthAll,
    Orth, Orth1, occV, occA, occOnly, Slot.all, Member.all, Term.isNever, Term.isOpenObject,
    objectNamesAgree]

/-- …and the same refusal one container out. A set of stored numerals satisfies both bases, so
    the pair shares values and has no meet. -/
example : Term.meet (.set .string) (.set .decimal) = none := by simp [Term.meet]

example : Adm (.set .string) (.strSet ⟨{"1"}, Finset.singleton_nonempty _⟩) = true := by
  simp [Adm, SetBase.adm]

example : Adm (.set .decimal) (.strSet ⟨{"1"}, Finset.singleton_nonempty _⟩) = true := by
  simp [Adm, SetBase.adm, isStored, Numeral.Stored]
  decide

/-- **An open factor refuses no name, so the required-name test is not a bottom test against
    one.** The left body requires `x` and the right does not declare it, which the required-name
    test reads as a refusal; the right body's rest holds `x` instead. The two examples below are
    the value both admit, so the pair shares a value and the answer is the refusal. -/
example :
    Term.meet
        (.object (.mk {"x"} (fun _ => .req .string) (.codec .string)))
        (.object (.mk {"y"} (fun _ => .optional .string) (.codec .string)))
      = none := by
  rw [Term.meet.eq_def]
  simp [Body.meetTerm, Rest.merge]

/-- The left body admits `{x := "1"}` through its declared field… -/
example : Adm (.object (.mk {"x"} (fun _ => .req .string) (.codec .string)))
    (.map {"x"} (fun _ => .str "1")) = true := by
  simp [Adm, AdmBody, valPresentT, objAdmV, entryP, MapOf.at, AdmField]

/-- …and the right body admits it through its rest, at a name it does not declare. -/
example : Adm (.object (.mk {"y"} (fun _ => .optional .string) (.codec .string)))
    (.map {"x"} (fun _ => .str "1")) = true := by
  simp [Adm, AdmBody, valPresentT, objAdmV, entryP, MapOf.at, AdmField, AdmRest]
  apply decide_eq_true
  intro k
  rw [if_neg (by have hk := k.2; simp only [Finset.mem_singleton] at hk; simp [hk])]

/-! ### The presence table

Nine cells, one per pair of marks, and the two an unshared name answers. Each is the join of the
two presence bits, and the term is the meet of the terms. -/

/-- `req` against `req`, `optional` and `fallback`: the name must be present for one factor, so it
    must be present for the meet, and a `fallback`'s stand-in never answers under it. -/
example : Field.meet (.req .string) (.req .string) = some (.req .string) := by
  simp [Field.meet, Term.meet]

example : Field.meet (.req .string) (.optional .string) = some (.req .string) := by
  simp [Field.meet, Term.meet]

example : Field.meet (.optional .string) (.req .string) = some (.req .string) := by
  simp [Field.meet, Term.meet]

example : Field.meet (.req .string) (.fallback .string (.str "d")) = some (.req .string) := by
  simp [Field.meet, Term.meet]

example : Field.meet (.fallback .string (.str "d")) (.req .string) = some (.req .string) := by
  simp [Field.meet, Term.meet]

/-- `optional` against `optional` forces neither half… -/
example : Field.meet (.optional .string) (.optional .string) = some (.optional .string) := by
  simp [Field.meet, Term.meet]

/-- …and against a `fallback` the stand-in survives, because that is the one mark forcing the
    write and not the read. -/
example : Field.meet (.optional .string) (.fallback .string (.str "d"))
    = some (.fallback .string (.str "d")) := by simp [Field.meet, Term.meet]

example : Field.meet (.fallback .string (.str "d")) (.optional .string)
    = some (.fallback .string (.str "d")) := by simp [Field.meet, Term.meet]

/-- Two stand-ins refuse, even these two, which are equal. `Value` has no `DecidableEq` here, so
    the row cannot ask; `docs/defects.md` carries it. -/
example : Field.meet (.fallback .string (.str "d")) (.fallback .string (.str "d")) = none := by
  simp [Field.meet]

/-- An unshared `req` name under a closed rest is the bottom: it must be written and the partner
    refuses it, and on the read side the partner refuses it too. -/
example : Term.meet
    (.object (.mk {"x"} (fun _ => .req .string) .refuse))
    (.object (.mk ∅ (fun _ => .optional .never) .refuse)) = some .never := by
  rw [Term.meet.eq_def]
  simp [Body.meetTerm, Rest.merge, Body.fbShared, Field.isFallback, Body.dropFits,
    Body.reqShared, Field.isReq]

/-- **…and an unshared `fallback` name refuses**, because the two halves part there. The write
    side must write the name and the partner refuses it, so nothing is written; the read side
    needs no name at all and both factors read the map that omits it. -/
example : Term.meet
    (.object (.mk {"x"} (fun _ => .fallback .string (.str "d")) .refuse))
    (.object (.mk ∅ (fun _ => .optional .never) .refuse)) = none := by
  rw [Term.meet.eq_def]
  simp [Body.meetTerm, Rest.merge, Body.fbShared, Field.isFallback]

/-- **`drop` skips an undeclared name on the read side, so the declared set bounds the read from
    below.** These two bodies declare one name each, and the intersection declares neither. On the
    write side each factor refuses a map carrying the other's name and the intersection refuses it
    too, so the write side is right. On the read side each factor skips the name it does not
    declare, so each reads `{x := true}` — and the intersection, declaring nothing, reads every
    map, where the left factor refuses that one. No object states both halves and the pair
    refuses. -/
example : Term.meet
    (.object (.mk {"x"} (fun _ => .optional .string) .drop))
    (.object (.mk {"y"} (fun _ => .optional .string) .drop)) = none := by
  rw [Term.meet.eq_def]
  simp [Body.meetTerm, Rest.merge, Body.dropFits]

/-- The same pair at `req`, where the answer was the bottom: the required-name test reads a name
    the other body does not declare as a refusal, and under `drop` the other body skips it. -/
example : Term.meet
    (.object (.mk {"x"} (fun _ => .req .string) .drop))
    (.object (.mk {"y"} (fun _ => .req .string) .drop)) = none := by
  rw [Term.meet.eq_def]
  simp [Body.meetTerm, Rest.merge, Body.dropFits]

/-- …and the mirror, where the meet refuses what both factors read. The `drop` factor skips `y`
    and the `refuse` factor reads it through its own field, so both admit `{y := "1"}`; the
    intersection declares nothing and the merged `refuse` refuses it. -/
example : Term.meet
    (.object (.mk ∅ (fun _ => .optional .never) .drop))
    (.object (.mk {"y"} (fun _ => .optional .string) .refuse)) = none := by
  rw [Term.meet.eq_def]
  simp [Body.meetTerm, Rest.merge, Body.dropFits]

/-- Two `refuse` factors keep the intersection. `refuse` reads an undeclared name the way it
    writes one, so the declared set is an upper bound on both halves and the two agree. -/
example : Term.meet
    (.object (.mk {"x"} (fun _ => .optional .string) .refuse))
    (.object (.mk {"y"} (fun _ => .optional .string) .refuse))
    = some (.object (.mk (Body.shared (.mk {"x"} (fun _ => .optional .string) .refuse)
                                      (.mk {"y"} (fun _ => .optional .string) .refuse))
        (fun k => Body.meetField (.mk {"x"} (fun _ => .optional .string) .refuse)
                                 (.mk {"y"} (fun _ => .optional .string) .refuse) k) .refuse)) := by
  rw [Term.meet.eq_def]
  simp only [Body.meetTerm, Rest.merge, Body.dropFits, Body.reqShared, Body.meetOk,
    Field.isBottom, Field.isReq, Body.shared]
  rfl

/-- **An uncertified union has no meet, and there are two ways to be uncertified.** These two
    options declare the same name with the same mark and no literal, so nothing tells them
    apart: both admit a map carrying `a` *structurally*, `selOptV` finds two admitters and
    refuses, and the union admits less than the join of its options. -/
example : unionOk [.object (.mk {"a"} (fun _ => .req .string) .refuse),
    .object (.mk {"a"} (fun _ => .req .boolean) .refuse)] = false := by
  simp [unionOk, orthAll, Orth, Orth1, OrthM, OrthS, OrthL, occV, occA, occOnly, Slot.all,
    Member.all, reqNotDeclared, Body.spec, altsOfField, specOf, litDisjAt, altsDisj, MapOf.at,
    Finset.mem_singleton]

/-- **A `drop` object is the third way, and it is the open object's defect one half over.** The
    rest is closed, so the value side refuses an undeclared name and `keysOk` is that option's
    write row. The read side skips the name instead, so the option reads a map `keysOk` refuses,
    and a singleton union is enough to show it. -/
example : unionOk [.object (.mk {"x"} (fun _ => .optional .string) .drop)] = false := by
  simp [unionOk, orthAll, Term.isOpenObject, Rest.isOpen, objectNamesAgree]

/-- …and the same body at `refuse` carries the certificate. -/
example : unionOk [.object (.mk {"x"} (fun _ => .optional .string) .refuse)] = true := by
  simp [unionOk, orthAll, Term.isOpenObject, Rest.isOpen, objectNamesAgree,
    Field.presenceAgrees, MapOf.at]

/-- **A `fallback` field is the fourth way, and it is about a declared name rather than an
    undeclared one.** The field reads to its stand-in when the name is absent, so the option
    reads a map that omits the name, while `keysOk` requires every non-`optional` name to be
    present because the write side writes it. The rest is `refuse` here, so this is not the row
    above. -/
example : unionOk [.object (.mk {"x"} (fun _ => .fallback .string (.str "d")) .refuse)]
    = false := by
  simp [unionOk, orthAll, Term.isOpenObject, Rest.isOpen, objectNamesAgree,
    Field.presenceAgrees, MapOf.at]

/-- …and an **open** object is the second way, on its own. Its rest holds a name it does not
    declare, while an object option is admitted by `keysOk`, which refuses that name. So one
    such option makes the union refuse a value the option admits, and a singleton union is
    enough. -/
example : unionOk [.object (.mk {"a"} (fun _ => .req .string) (.codec .string))] = false := by
  simp [unionOk, orthAll, Term.isOpenObject, Rest.isOpen]

/-! ### Why the write-agreement condition is conditional

Two meets that are not the bottom and whose factor names no member. They are why the condition the
rows keep is "where both factors name a member" rather than "all three name the same member": a
`μSyn` of `none` is a term that names no single stored member, not a term that writes nothing. -/

example : μSyn (Term.union [.string, .null]) = none := by simp [μSyn, μSynList, unanimous]

example : ¬ (μSyn Term.null = μSyn (Term.union [.string, .null])) := by
  simp [μSyn, μSynList, unanimous]

example : Term.meet (.opaq true) .string = some .string := by simp [Term.meet]

example : ¬ (μSyn Term.string = μSyn (Term.opaq true)) := by simp [μSyn]

/-! ## The homomorphism

`Adm` carries the meet to conjunction. The proof is one `fun_cases` row per pair of
constructors, under a strong induction on the summed depth; the lemmas each class needs are
stated first.
-/


/-! ## The levers -/

/-! ## What `opaque` admits

`Adm (.opaq l) v` is `dom(e)` of `opaqCodecω l`, and a scalar's budget is one layer, so each
row below is the corresponding unfolding at fuel `0+1`. -/

/-- `opaque` writes every string, so `string` is the finer term. -/
theorem Adm_opaq_str (l : Bool) (s : String) : Adm (.opaq l) (.str s) = true := by
  show ((opaqCodec (Value.depth (.str s)) l).e (.str s)).isSome = true
  rw [show Value.depth (.str s) = 0 + 1 from rfl, opaqCodec_e_str]
  simp [stringCodec]

/-- …every boolean. -/
theorem Adm_opaq_bool (l : Bool) (b : Bool) : Adm (.opaq l) (.bool b) = true := by
  show ((opaqCodec (Value.depth (.bool b)) l).e (.bool b)).isSome = true
  rw [show Value.depth (.bool b) = 0 + 1 from rfl, opaqCodec_e_bool]
  simp [booleanCodec]

/-- …every byte string. -/
theorem Adm_opaq_bin (l : Bool) (b : Bytes) : Adm (.opaq l) (.bin b) = true := by
  show ((opaqCodec (Value.depth (.bin b)) l).e (.bin b)).isSome = true
  rw [show Value.depth (.bin b) = 0 + 1 from rfl, opaqCodec_e_bin]
  simp [binaryCodec]

/-- …and the null point. -/
theorem Adm_opaq_null (l : Bool) : Adm (.opaq l) .null = true := by
  show ((opaqCodec (Value.depth .null) l).e .null).isSome = true
  rw [show Value.depth .null = 0 + 1 from rfl, opaqCodec_e_null]
  simp [nullCodec]

/-- A number only under the lossy policy, and then exactly on `D`: the refusing policy carries
    the empty codec at that option. -/
theorem Adm_opaq_num (l : Bool) (d : Double) :
    Adm (.opaq l) (.num d) = (l && inD (.num d)) := by
  show ((opaqCodec (Value.depth (.num d)) l).e (.num d)).isSome = _
  rw [show Value.depth (.num d) = 0 + 1 from rfl, opaqCodec_e_num]
  cases l <;> simp [numberCodec, Codec.empty, inD]
  split <;> simp_all



/-- Two terms whose occupancies are disjoint share no value, so their conjunction is the
    bottom. This closes every row that answers `never` because the two write different
    `Value` constructors. -/
theorem Adm_and_false {x y : Term} (h : Orth1 x y = true) (v : Value) :
    (Adm x v && Adm y v) = false := by
  cases hx : Adm x v with
  | false => simp
  | true =>
    cases hy : Adm y v with
    | false => simp
    | true =>
      have h2 := occV_disjoint_of_Orth1 h (occV_sound x v hx)
      rw [occV_sound y v hy] at h2
      exact absurd h2 (by simp)

/-! The four whose admission is a function. On the left they refuse at every partner but the
    bottom; on the right the same, and the left rows fire first so only `never` needs naming. -/

/-- A term whose admission is a function refuses at every partner but the bottom. -/
theorem meet_held_none (t : Term) (f g : Value → Value) {y : Term} (hy : y ≠ .never) :
    Term.meet (.held t f g) y = none := by cases y <;> simp [Term.meet] ; exact absurd rfl hy
/-- …the same for `legacy`, whose read side carries the caller's own table. -/
theorem meet_legacy_none (t : Term) (r : Attr → Option Value) {y : Term} (hy : y ≠ .never) :
    Term.meet (.legacy t r) y = none := by cases y <;> simp [Term.meet] ; exact absurd rfl hy
/-- …for `custom`, which is two arbitrary partial functions. -/
theorem meet_custom_none (ce : Value → Option Attr) (cp : Attr → Option Value) {y : Term}
    (hy : y ≠ .never) : Term.meet (.custom ce cp) y = none := by
  cases y <;> simp [Term.meet] ; exact absurd rfl hy
/-- …and for `lazy`, whose subterm is behind a thunk. -/
theorem meet_lazy_none (t : Term) {y : Term} (hy : y ≠ .never) :
    Term.meet (.lazy t) y = none := by cases y <;> simp [Term.meet] ; exact absurd rfl hy

/-- The bottom absorbs on the right at every partner: the row for it precedes the four that
    refuse, so even a function-carrying term meets it. -/
theorem meet_never_right (x : Term) : Term.meet x .never = some .never := by
  cases x <;> simp [Term.meet]

/-- The same four on the right, where the left rows fire first so only the bottom needs naming. -/
theorem meet_heldR_none {x : Term} (hx : x ≠ .never) (t : Term) (f g : Value → Value) :
    Term.meet x (.held t f g) = none := by cases x <;> simp [Term.meet] ; exact absurd rfl hx
/-- …`legacy` on the right. -/
theorem meet_legacyR_none {x : Term} (hx : x ≠ .never) (t : Term) (r : Attr → Option Value) :
    Term.meet x (.legacy t r) = none := by cases x <;> simp [Term.meet] ; exact absurd rfl hx
/-- …`custom` on the right. -/
theorem meet_customR_none {x : Term} (hx : x ≠ .never)
    (ce : Value → Option Attr) (cp : Attr → Option Value) :
    Term.meet x (.custom ce cp) = none := by cases x <;> simp [Term.meet] ; exact absurd rfl hx
/-- …and `lazy` on the right. -/
theorem meet_lazyR_none {x : Term} (hx : x ≠ .never) (t : Term) :
    Term.meet x (.lazy t) = none := by cases x <;> simp [Term.meet] ; exact absurd rfl hx

/-- A wire set has an element, so a base that refuses every element refuses the set. Without
    the element the refusal would read as vacuous truth. -/
theorem NEFinset.mem_exists {α : Type} (S : NEFinset α) : ∃ x, x ∈ S.1 := S.2

/-- …in the form the set rows leave, where the element is what refutes the vacuous reading. -/
theorem NEFinset.not_forall_notMem {α : Type} (S : NEFinset α) : ¬ ∀ a, a ∉ S.1 :=
  fun hall => S.2.elim (fun a ha => hall a ha)

/-- A list admits under the meet exactly where it admits under both factors. -/
theorem allP_and {p q r : VP} (h : ∀ v, r v = (p v && q v)) (xs : List Value) :
    allP r xs = (allP p xs && allP q xs) := by
  induction xs with
  | nil => simp [allP]
  | cons a as ihx =>
    simp only [allP, h, ihx]
    simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

/-- …and a key set the same way. -/
theorem decide_forall_and {α : Sort*} {p q r : α → Bool}
    [Decidable (∀ k, r k = true)] [Decidable (∀ k, p k = true)] [Decidable (∀ k, q k = true)]
    (h : ∀ k, r k = (p k && q k)) :
    decide (∀ k, r k = true) = (decide (∀ k, p k = true) && decide (∀ k, q k = true)) := by
  simp only [h, Bool.and_eq_true, forall_and]
  simp

/-- A list of answers that all succeeded pairs each source with its answer. -/
theorem allSome_map_forall₂ {α β : Type} (f : α → Option β) :
    ∀ {xs : List α} {ys : List β}, allSome (xs.map f) = some ys →
      List.Forall₂ (fun x y => f x = some y) xs ys := by
  intro xs
  induction xs with
  | nil => intro ys h; simp only [List.map_nil, allSome, Option.some.injEq] at h; subst h; exact .nil
  | cons a as ihx =>
    intro ys h
    rw [List.map_cons] at h
    cases hf : f a with
    | none => rw [hf] at h; simp only [allSome, reduceCtorEq] at h
    | some b =>
      rw [hf] at h
      simp only [allSome, Option.map_eq_some_iff] at h
      obtain ⟨zs, hzs, rfl⟩ := h
      exact .cons hf (ihx hzs)

/-- What an array met with a tuple answers: the tuple's shape, with every declared position and
    the tail met against the array's element term. -/
theorem meet_array_tuple {a : Term} {ts : List Term} {tail : Option Term} {z : Term}
    (h : Term.meet (.array a) (.tuple ts tail) = some z) :
    ∃ vs tl, z = .tuple vs tl ∧
      List.Forall₂ (fun t v => Term.meet t a = some v) ts vs ∧
      ((tail = none ∧ tl = none) ∨
        ∃ t u, tail = some t ∧ tl = some u ∧ Term.meet t a = some u) := by
  rw [Term.meet.eq_def] at h
  simp only [] at h
  split at h
  next vs tl hA hB =>
    rw [Option.some.injEq] at h
    subst h
    refine ⟨vs, tl, rfl, allSome_map_forall₂ _ (by simpa using hA), ?_⟩
    cases tail with
    | none => exact Or.inl ⟨rfl, by simpa using hB.symm⟩
    | some t =>
      obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp (by simpa using hB)
      exact Or.inr ⟨t, u, rfl, rfl, hu⟩
  next => exact absurd h (by simp)



/-- `allP` is `alignP` with no declared position and a uniform tail. -/
theorem allP_eq_alignP (P : VP) (ws : List Value) : allP P ws = alignP [] (some P) ws := by
  induction ws with
  | nil => rfl
  | cons w ws ihw => simp only [allP, alignP, ihw]

/-- An array against a tuple: every declared position and the tail meet the array's element row, so the aligned answer is the conjunction. -/
theorem alignP_meet_all {P : VP} :
    ∀ {Ps Qs : List VP}, List.Forall₂ (fun p q => ∀ w, q w = (p w && P w)) Ps Qs →
    ∀ {pt qt : Option VP},
      (pt = none ∧ qt = none) ∨
        (∃ p q, pt = some p ∧ qt = some q ∧ ∀ w, q w = (p w && P w)) →
    ∀ ws, alignP Qs qt ws = (allP P ws && alignP Ps pt ws) := by
  intro Ps Qs hPQ pt qt htl ws
  induction ws generalizing Ps Qs with
  | nil =>
    cases hPQ with
    | nil => rcases htl with ⟨rfl, rfl⟩ | ⟨p, q, rfl, rfl, _⟩ <;> simp [alignP, allP]
    | cons _ _ => simp [alignP, allP]
  | cons w ws ihw =>
    cases hPQ with
    | nil =>
      rcases htl with ⟨rfl, rfl⟩ | ⟨p, q, rfl, rfl, hpq⟩
      · simp [alignP, allP]
      · simp only [alignP, allP, hpq, ihw .nil]
        simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
    | cons hpq hrest =>
      simp only [alignP, allP, hpq, ihw hrest]
      simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

/-- The positions of a tuple, lifted from the meet of the terms to the meet of the rows. -/
theorem AdmList_forall₂ {a : Term} {n : Nat}
    (ih : ∀ x y, Term.depth x + Term.depth y ≤ n → ∀ z, Term.meet x y = some z →
          ∀ w, Adm z w = (Adm x w && Adm y w)) :
    ∀ {ts vs : List Term}, Term.depthL ts + Term.depth a ≤ n →
      List.Forall₂ (fun t v => Term.meet t a = some v) ts vs →
      List.Forall₂ (fun p q => ∀ w, q w = (p w && Adm a w)) (AdmList ts) (AdmList vs) := by
  intro ts
  induction ts with
  | nil => intro vs _ hts; cases hts; exact .nil
  | cons t ts' ihx =>
    intro vs hd hts
    cases hts with
    | cons hh hrest =>
      have h1 : Term.depth t ≤ Term.depthL (t :: ts') := by simp [Term.depthL]
      have h2 : Term.depthL ts' ≤ Term.depthL (t :: ts') := by simp [Term.depthL]
      simp only [AdmList]
      exact .cons (ih t a (by omega) _ hh) (ihx (by omega) hrest)



/-- …and the same answer with the tuple on the left. -/
theorem meet_tuple_array {a : Term} {ts : List Term} {tail : Option Term} {z : Term}
    (h : Term.meet (.tuple ts tail) (.array a) = some z) :
    ∃ vs tl, z = .tuple vs tl ∧
      List.Forall₂ (fun t v => Term.meet t a = some v) ts vs ∧
      ((tail = none ∧ tl = none) ∨
        ∃ t u, tail = some t ∧ tl = some u ∧ Term.meet t a = some u) := by
  rw [Term.meet.eq_def] at h
  simp only [] at h
  split at h
  next vs tl hA hB =>
    rw [Option.some.injEq] at h
    subst h
    refine ⟨vs, tl, rfl, allSome_map_forall₂ _ (by simpa using hA), ?_⟩
    cases tail with
    | none => exact Or.inl ⟨rfl, by simpa using hB.symm⟩
    | some t =>
      obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp (by simpa using hB)
      exact Or.inr ⟨t, u, rfl, rfl, hu⟩
  next => exact absurd h (by simp)

/-- The two bounds the array-against-tuple row needs, with the array on the left. -/
theorem tuple_bounds_l {a : Term} {ts : List Term} {tail : Option Term} {n : Nat}
    (hle : Term.depth (.array a) + Term.depth (.tuple ts tail) ≤ n + 1) :
    Term.depthL ts + Term.depth a ≤ n ∧
      ∀ t, tail = some t → Term.depth t + Term.depth a ≤ n := by
  simp only [Term.depth] at hle
  have h1 := Nat.le_max_left (Term.depthL ts) (Term.depthO tail)
  have h2 := Nat.le_max_right (Term.depthL ts) (Term.depthO tail)
  refine ⟨by omega, ?_⟩
  rintro t rfl
  have hd : Term.depthO (some t) = Term.depth t := rfl
  omega

/-- …and with the tuple on the left. -/
theorem tuple_bounds_r {a : Term} {ts : List Term} {tail : Option Term} {n : Nat}
    (hle : Term.depth (.tuple ts tail) + Term.depth (.array a) ≤ n + 1) :
    Term.depthL ts + Term.depth a ≤ n ∧
      ∀ t, tail = some t → Term.depth t + Term.depth a ≤ n :=
  tuple_bounds_l (a := a) (by omega)

/-- A tail lifted from the meet of the terms to the meet of the rows. -/
theorem tailMeet_lift {a : Term} {n : Nat}
    (ih : ∀ x y, Term.depth x + Term.depth y ≤ n → ∀ z, Term.meet x y = some z →
          ∀ w, Adm z w = (Adm x w && Adm y w))
    {tail tl : Option Term}
    (hb : ∀ t, tail = some t → Term.depth t + Term.depth a ≤ n)
    (htl : (tail = none ∧ tl = none) ∨
      ∃ t u, tail = some t ∧ tl = some u ∧ Term.meet t a = some u) :
    (AdmOptT tail = none ∧ AdmOptT tl = none) ∨
      ∃ p q, AdmOptT tail = some p ∧ AdmOptT tl = some q ∧
        ∀ w, q w = (p w && Adm a w) := by
  rcases htl with ⟨rfl, rfl⟩ | ⟨t, u, rfl, rfl, hu⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨Adm t, Adm u, rfl, rfl, ih t a (hb t rfl) u hu⟩

/-- Two tuples of one arity: the positions meet positionwise and the tails meet. -/
theorem alignP_meet_zip :
    ∀ {Ps Qs Rs : List VP},
      List.Forall₂ (fun (pq : VP × VP) r => ∀ w, r w = (pq.1 w && pq.2 w)) (Ps.zip Qs) Rs →
      Ps.length = Qs.length →
    ∀ {pt qt rt : Option VP},
      ((pt = none ∧ qt = none ∧ rt = none) ∨
        ∃ p q r, pt = some p ∧ qt = some q ∧ rt = some r ∧ ∀ w, r w = (p w && q w)) →
    ∀ ws, alignP Rs rt ws = (alignP Ps pt ws && alignP Qs qt ws) := by
  intro Ps Qs Rs hF hlen pt qt rt htl ws
  induction ws generalizing Ps Qs Rs with
  | nil =>
    cases Ps with
    | nil =>
      cases Qs with
      | nil =>
        cases hF
        rcases htl with ⟨rfl, rfl, rfl⟩ | ⟨p, q, r, rfl, rfl, rfl, _⟩ <;> simp [alignP]
      | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons p Ps' =>
      cases Qs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons q Qs' =>
        rw [List.zip_cons_cons] at hF
        cases hF with
        | cons _ _ => simp [alignP]
  | cons w ws ihw =>
    cases Ps with
    | nil =>
      cases Qs with
      | nil =>
        cases hF
        rcases htl with ⟨rfl, rfl, rfl⟩ | ⟨p, q, r, rfl, rfl, rfl, hr⟩
        · simp [alignP]
        · simp only [alignP, hr, ihw (Ps := []) (Qs := []) .nil rfl]
          simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
      | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons p Ps' =>
      cases Qs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons q Qs' =>
        rw [List.zip_cons_cons] at hF
        cases hF with
        | cons hr hrest =>
          simp only [alignP, hr, ihw hrest (by simpa using hlen)]
          simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

/-- A tuple with no tail pins the length of the array it admits. -/
theorem alignP_none_length : ∀ {Ps : List VP} {ws : List Value},
    alignP Ps none ws = true → ws.length = Ps.length := by
  intro Ps
  induction Ps with
  | nil => intro ws h; cases ws with
    | nil => rfl
    | cons _ _ => simp [alignP] at h
  | cons p Ps' ihp =>
    intro ws h
    cases ws with
    | nil => simp [alignP] at h
    | cons w ws' =>
      simp only [alignP, Bool.and_eq_true] at h
      simp [ihp h.2]



/-- `attach` then `map` is `map`, with the function named so the rewrite is first order. -/
theorem attach_map_fun {α β : Type} (l : List α) (f : α → β) :
    l.attach.map (fun x => f x.1) = l.map f := by simp
/-- What two tuples answer: one arity meeting positionwise, or the bottom where two arities
    with no tail admit no common array. -/
theorem meet_tuple_tuple {ts us : List Term} {tail tail' : Option Term} {z : Term}
    (h : Term.meet (.tuple ts tail) (.tuple us tail') = some z) :
    (∃ vs tl, z = .tuple vs tl ∧ ts.length = us.length ∧
        List.Forall₂ (fun (p : Term × Term) v => Term.meet p.1 p.2 = some v) (ts.zip us) vs ∧
        ((tail = none ∧ tail' = none ∧ tl = none) ∨
          ∃ t u w, tail = some t ∧ tail' = some u ∧ tl = some w ∧ Term.meet t u = some w))
    ∨ (z = .never ∧ ts.length ≠ us.length ∧ tail = none ∧ tail' = none) := by
  rw [Term.meet.eq_def] at h
  simp only [] at h
  split at h
  next hlen =>
    split at h
    next vs tl hA hB =>
      rw [Option.some.injEq] at h
      subst h
      refine Or.inl ⟨vs, tl, rfl, hlen,
        allSome_map_forall₂ _ (by rw [← attach_map_fun (ts.zip us) (fun p => p.1.meet p.2)]
                                  exact hA), ?_⟩
      cases tail with
      | none =>
        cases tail' with
        | none => exact Or.inl ⟨rfl, rfl, by simpa using hB.symm⟩
        | some u => exact absurd hB (by simp)
      | some t =>
        cases tail' with
        | none => exact absurd hB (by simp)
        | some u =>
          obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp (by simpa using hB)
          exact Or.inr ⟨t, u, w, rfl, rfl, rfl, hw⟩
    next => exact absurd h (by simp)
  next hlen =>
    split at h
    next hn =>
      rw [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hn
      exact Or.inr ⟨rfl, hlen, hn.1, hn.2⟩
    next => exact absurd h (by simp)



/-- The rows of a term list are as many as the terms. -/
theorem AdmList_length (ts : List Term) : (AdmList ts).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ihx => simp only [AdmList, List.length_cons, ihx]

/-- The two bounds two tuples need. -/
theorem tuple_bounds_tt {ts us : List Term} {tail tail' : Option Term} {n : Nat}
    (hle : Term.depth (.tuple ts tail) + Term.depth (.tuple us tail') ≤ n + 1) :
    Term.depthL ts + Term.depthL us ≤ n ∧
      ∀ t u, tail = some t → tail' = some u → Term.depth t + Term.depth u ≤ n := by
  simp only [Term.depth] at hle
  have h1 := Nat.le_max_left (Term.depthL ts) (Term.depthO tail)
  have h2 := Nat.le_max_right (Term.depthL ts) (Term.depthO tail)
  have h3 := Nat.le_max_left (Term.depthL us) (Term.depthO tail')
  have h4 := Nat.le_max_right (Term.depthL us) (Term.depthO tail')
  refine ⟨by omega, ?_⟩
  rintro t u rfl rfl
  have e1 : Term.depthO (some t) = Term.depth t := rfl
  have e2 : Term.depthO (some u) = Term.depth u := rfl
  omega

/-- Two tuples of one arity, lifted position by position from the meet of the terms to the meet of the rows. -/
theorem AdmList_forall₂_zip {n : Nat}
    (ih : ∀ x y, Term.depth x + Term.depth y ≤ n → ∀ z, Term.meet x y = some z →
          ∀ w, Adm z w = (Adm x w && Adm y w)) :
    ∀ {ts us vs : List Term}, Term.depthL ts + Term.depthL us ≤ n →
      List.Forall₂ (fun (p : Term × Term) v => Term.meet p.1 p.2 = some v) (ts.zip us) vs →
      List.Forall₂ (fun (pq : VP × VP) r => ∀ w, r w = (pq.1 w && pq.2 w))
        ((AdmList ts).zip (AdmList us)) (AdmList vs) := by
  intro ts
  induction ts with
  | nil =>
    intro us vs _ hF
    rw [List.zip_nil_left] at hF
    cases hF
    simp only [AdmList, List.zip_nil_left]
    exact .nil
  | cons t ts' ihx =>
    intro us vs hd hF
    cases us with
    | nil =>
      rw [List.zip_nil_right] at hF
      cases hF
      simp only [AdmList, List.zip_nil_right]
      exact .nil
    | cons u us' =>
      rw [List.zip_cons_cons] at hF
      cases hF with
      | cons hh hrest =>
        have h1 : Term.depth t ≤ Term.depthL (t :: ts') := by simp [Term.depthL]
        have h2 : Term.depthL ts' ≤ Term.depthL (t :: ts') := by simp [Term.depthL]
        have h3 : Term.depth u ≤ Term.depthL (u :: us') := by simp [Term.depthL]
        have h4 : Term.depthL us' ≤ Term.depthL (u :: us') := by simp [Term.depthL]
        simp only [AdmList, List.zip_cons_cons]
        exact .cons (ih t u (by omega) _ hh) (ihx (by omega) hrest)

/-- Two tuples’ tails, lifted the same way. -/
theorem tailMeet_lift2 {n : Nat}
    (ih : ∀ x y, Term.depth x + Term.depth y ≤ n → ∀ z, Term.meet x y = some z →
          ∀ w, Adm z w = (Adm x w && Adm y w))
    {tail tail' tl : Option Term}
    (hb : ∀ t u, tail = some t → tail' = some u → Term.depth t + Term.depth u ≤ n)
    (htl : (tail = none ∧ tail' = none ∧ tl = none) ∨
      ∃ t u w, tail = some t ∧ tail' = some u ∧ tl = some w ∧ Term.meet t u = some w) :
    (AdmOptT tail = none ∧ AdmOptT tail' = none ∧ AdmOptT tl = none) ∨
      ∃ p q r, AdmOptT tail = some p ∧ AdmOptT tail' = some q ∧ AdmOptT tl = some r ∧
        ∀ w, r w = (p w && q w) := by
  rcases htl with ⟨rfl, rfl, rfl⟩ | ⟨t, u, w, rfl, rfl, rfl, hw⟩
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨Adm t, Adm u, Adm w, rfl, rfl, rfl, ih t u (hb t u rfl rfl) w hw⟩



/-- Every option but the numeric one ignores the policy, so the two policies write a scalar
    the same way at every budget. -/
theorem opaq_e_str_agree (n : Nat) (s : String) :
    (opaqCodec n false).e (.str s) = (opaqCodec n true).e (.str s) := by
  cases n with
  | zero => rfl
  | succ m => rw [opaqCodec_e_str, opaqCodec_e_str]

/-- …and every byte string, at every budget. -/
theorem opaq_e_bin_agree (n : Nat) (b : Bytes) :
    (opaqCodec n false).e (.bin b) = (opaqCodec n true).e (.bin b) := by
  cases n with
  | zero => rfl
  | succ m => rw [opaqCodec_e_bin, opaqCodec_e_bin]

/-- …and the refusing policy writes no number at any budget, which is what makes a set of
    numbers unwritable rather than written differently. -/
theorem opaq_e_num_false (n : Nat) (d : Double) : (opaqCodec n false).e (.num d) = none := by
  cases n with
  | zero => rfl
  | succ m => rw [opaqCodec_e_num]; rfl

/-- A traversal carries a pointwise implication between the two element functions. -/
theorem traverse_mono {α β : Type} {f g : α → Option β}
    (h : ∀ x a, f x = some a → g x = some a) :
    ∀ {xs : List α} {as : List β}, traverse f xs = some as → traverse g xs = some as := by
  intro xs
  induction xs with
  | nil => intro as hh; exact hh
  | cons x xs ihx =>
    intro as hh
    simp only [traverse] at hh ⊢
    cases hf : f x with
    | none => rw [hf] at hh; exact nomatch hh
    | some b =>
      rw [hf] at hh
      cases ht : traverse f xs with
      | none => rw [ht] at hh; exact nomatch hh
      | some bs =>
        rw [ht] at hh
        rw [h x b hf, ihx ht]
        exact hh

/-- …and so does the image of a function on a key set. -/
theorem funImage_mono {β : Type} {keys : Finset Name} {g g' : {k // k ∈ keys} → Option β}
    {t : {k // k ∈ keys} → β}
    (hm : ∀ k b, g k = some b → g' k = some b) (hh : funImage g = some t) :
    funImage g' = some t := by
  have hall : ∀ k, g' k = some (t k) := fun k => hm k (t k) (funImage_some hh k)
  unfold funImage
  rw [dif_pos (fun k => by rw [hall k]; rfl)]
  exact congrArg some (funext fun k => Option.some.inj (by rw [Option.some_get, hall k]))

/-- A codec that writes no element writes no set: the wire set has an element to refuse at. -/
theorem encSet_none_of_refuse {α : Type} (c : Codec) (inj : α → Value) (S : NEFinset α)
    (h : ∀ x, c.e (inj x) = none) : encSet c inj S = none := by
  obtain ⟨x0, hx0⟩ := S.2
  have key : ∀ {β : Type} [DecidableEq β] (out : Attr → Option β),
      neSetImage (fun x => (c.e (inj x)).bind out) S = none := by
    intro β _ out
    cases hs : setImage (fun x => (c.e (inj x)).bind out) S.1 with
    | none => exact neSetImage_none hs
    | some T => exact absurd (setImage_some hs x0 hx0) (by rw [h x0]; exact fun hc => Bool.noConfusion hc)
  unfold encSet
  rw [key, key, key]
  rfl



/-- Two codecs agreeing on the elements write the same wire set. -/
theorem encSet_congr_e {α : Type} (c d : Codec) (inj : α → Value) (S : NEFinset α)
    (h : ∀ x, c.e (inj x) = d.e (inj x)) : encSet c inj S = encSet d inj S := by
  unfold encSet
  rw [neSetImage_congr (f := fun x => (c.e (inj x)).bind sC.out)
        (g := fun x => (d.e (inj x)).bind sC.out) (fun x _ => by rw [h x]),
      neSetImage_congr (f := fun x => (c.e (inj x)).bind nC.out)
        (g := fun x => (d.e (inj x)).bind nC.out) (fun x _ => by rw [h x]),
      neSetImage_congr (f := fun x => (c.e (inj x)).bind bC.out)
        (g := fun x => (d.e (inj x)).bind bC.out) (fun x _ => by rw [h x])]

/-- **The refusing policy is below the lossy one.** Where `opaque` at `refuse` writes, `opaque`
    at `lossy` writes the same attribute: the numeric option is the only one that differs, and
    it is empty on the refusing side. -/
theorem opaq_e_mono : ∀ (n : Nat) (v : Value) (a : Attr),
    (opaqCodec n false).e v = some a → (opaqCodec n true).e v = some a := by
  intro n
  induction n with
  | zero => intro v a hh; exact nomatch hh
  | succ m ihm =>
    intro v a hh
    cases v with
    | str s => rw [opaqCodec_e_str] at hh ⊢; exact hh
    | bool b => rw [opaqCodec_e_bool] at hh ⊢; exact hh
    | bin b => rw [opaqCodec_e_bin] at hh ⊢; exact hh
    | null => rw [opaqCodec_e_null] at hh ⊢; exact hh
    | num d => rw [opaq_e_num_false] at hh; exact nomatch hh
    | strSet S =>
      rw [opaqCodec_e_strSet] at hh ⊢
      show encSet (opaqCodec m true) Value.str S = some a
      rw [← encSet_congr_e (opaqCodec m false) (opaqCodec m true) Value.str S
            (opaq_e_str_agree m)]
      exact hh
    | binSet S =>
      rw [opaqCodec_e_binSet] at hh ⊢
      show encSet (opaqCodec m true) Value.bin S = some a
      rw [← encSet_congr_e (opaqCodec m false) (opaqCodec m true) Value.bin S
            (opaq_e_bin_agree m)]
      exact hh
    | numSet S =>
      rw [opaqCodec_e_numSet] at hh
      rw [show (setCodec (opaqCodec m false)).e (.numSet S)
            = encSet (opaqCodec m false) Value.num S from rfl,
          encSet_none_of_refuse _ _ _ (opaq_e_num_false m)] at hh
      exact nomatch hh
    | arr vs =>
      rw [opaqCodec_e_arr] at hh ⊢
      show ((traverse (opaqCodec m true).e vs).map Attr.l) = some a
      replace hh : ((traverse (opaqCodec m false).e vs).map Attr.l) = some a := hh
      obtain ⟨as, has, rfl⟩ := Option.map_eq_some_iff.mp hh
      rw [traverse_mono (fun x b hb => ihm x b hb) has]
      rfl
    | map keys f =>
      rw [opaqCodec_e_map] at hh ⊢
      show ((funImage (fun k => (opaqCodec m true).e (f k))).map (Attr.m keys)) = some a
      replace hh : ((funImage (fun k => (opaqCodec m false).e (f k))).map (Attr.m keys))
          = some a := hh
      obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hh
      rw [funImage_mono (fun k b hb => ihm _ b hb) hg]
      rfl



/-- `opaque`'s row is `dom(e)` of its codec, budgeted by the value's own depth. -/
theorem Adm_opaq_eq (l : Bool) (v : Value) :
    Adm (.opaq l) v = ((opaqCodec (Value.depth v) l).e v).isSome := rfl

/-- The meet of two `opaque`s is `opaque` at the conjunction of the policies, because the
    refusing policy writes a subset of what the lossy one writes. -/
theorem Adm_opaq_and (l l' : Bool) (v : Value) :
    Adm (.opaq (l && l')) v = (Adm (.opaq l) v && Adm (.opaq l') v) := by
  rw [Adm_opaq_eq, Adm_opaq_eq, Adm_opaq_eq]
  cases hf : (opaqCodec (Value.depth v) false).e v with
  | none => cases l <;> cases l' <;> simp [hf]
  | some a =>
    have ht := opaq_e_mono _ v a hf
    cases l <;> cases l' <;> simp [hf, ht]

/-- A rest policy that merges is closed on both sides and closed in the answer, so an
    undeclared name is refused by all three. -/
theorem Rest.merge_admRest {p q r : Rest} (h : Rest.merge p q = some r) :
    AdmRest p = none ∧ AdmRest q = none ∧ AdmRest r = none := by
  cases p <;> cases q <;> simp only [Rest.merge, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> exact ⟨rfl, rfl, rfl⟩

/-- Two fields that meet carry two terms that meet, and each field's row is its term's. The
    depths come with it, because the object row's bound is stated on the fields. -/
theorem AdmField_meet {f g fm : Field} (h : Field.meet f g = some fm) :
    ∃ x y z, Term.meet x y = some z ∧
      AdmField f = Adm x ∧ AdmField g = Adm y ∧ AdmField fm = Adm z ∧
      Field.depth f = Term.depth x + 1 ∧ Field.depth g = Term.depth y + 1 := by
  cases f <;> cases g <;>
    simp only [Field.meet, Option.map_eq_some_iff, reduceCtorEq, false_and, exists_false] at h <;>
    obtain ⟨z, hz, rfl⟩ := h <;>
    exact ⟨_, _, z, hz, rfl, rfl, rfl, rfl, rfl⟩


/-- A name is shared exactly when both bodies declare it. -/
theorem mem_shared_iff {a b : Body} {k : Name} :
    k ∈ Body.shared a b ↔ k ∈ a.fields ∧ k ∈ b.fields := Finset.mem_filter

/-- **The value side of the object row.** Every present name goes through the meet of the two
    fields where both declare it, and is refused where either does not. -/
theorem objAdmV_meet {a b : Body}
    (ihf : ∀ (k : {k // k ∈ Body.shared a b}) (w : Value),
      AdmField (Body.meetField a b k) w
        = (AdmField (a.at ⟨k.1, Body.mem_shared_left k.2⟩) w
            && AdmField (b.at ⟨k.1, Body.mem_shared_right k.2⟩) w))
    (keys : Finset Name) (g : {k // k ∈ keys} → Value) :
    objAdmV ⟨Body.shared a b, fun k => AdmField (Body.meetField a b k)⟩ none keys g
      = (objAdmV ⟨a.fields, fun k => AdmField (a.at k)⟩ none keys g
         && objAdmV ⟨b.fields, fun k => AdmField (b.at k)⟩ none keys g) := by
  simp only [objAdmV, entryP, MapOf.at]
  refine decide_forall_and (fun k => ?_)
  by_cases hk : k.1 ∈ Body.shared a b
  · have ha := Body.mem_shared_left hk
    have hb := Body.mem_shared_right hk
    simp only [dif_pos hk, dif_pos ha, dif_pos hb]
    exact ihf ⟨k.1, hk⟩ (g k)
  · have hnab : ¬ (k.1 ∈ a.fields ∧ k.1 ∈ b.fields) := fun hh => hk (mem_shared_iff.mpr hh)
    simp only [dif_neg hk]
    by_cases ha : k.1 ∈ a.fields
    · simp only [dif_pos ha, dif_neg (fun hh => hnab ⟨ha, hh⟩), Bool.and_false]
    · simp only [dif_neg ha, Bool.false_and]



/-- `valPresentT` in the form the object row uses: a declared name that must be present is
    present. -/
theorem valPresentT_req (fields : Finset Name) (fld : {k // k ∈ fields} → Field)
    (keys : Finset Name) :
    valPresentT fields fld keys
      = decide (∀ k : {k // k ∈ fields}, Field.isReq (fld k) = true → k.1 ∈ keys) := by
  unfold valPresentT
  refine decide_eq_decide.mpr ⟨fun hh k hreq => ?_, fun hh k => ?_⟩
  · have hk := hh k
    cases hf : fld k with
    | req t => rw [hf] at hk; exact of_decide_eq_true hk
    | fallback t d => rw [hf] at hk; exact of_decide_eq_true hk
    | optional t => rw [hf] at hreq; exact absurd hreq (by simp [Field.isReq])
  · cases hf : fld k with
    | optional t => rfl
    | req t => exact decide_eq_true (hh k (by rw [hf]; rfl))
    | fallback t d => exact decide_eq_true (hh k (by rw [hf]; rfl))



/-- The meet of two fields must be present when either factor's must: `Field.meet` answers
    `optional` only where both do. -/
theorem isReq_of_meet {f g fm : Field} (h : Field.meet f g = some fm) :
    Field.isReq fm = (Field.isReq f || Field.isReq g) := by
  cases f <;> cases g <;>
    simp only [Field.meet, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨z, _, rfl⟩ := h <;> rfl

/-- The meet of two fields at a shared name must be present when either factor's must. -/
theorem isReq_meetField {a b : Body} (hok : Body.meetOk a b = true)
    (k : {k // k ∈ Body.shared a b}) :
    Field.isReq (Body.meetField a b k)
      = (Field.isReq (a.at ⟨k.1, Body.mem_shared_left k.2⟩)
         || Field.isReq (b.at ⟨k.1, Body.mem_shared_right k.2⟩)) := by
  unfold Body.meetOk at hok
  obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (of_decide_eq_true hok k)
  unfold Body.meetField
  rw [hfm, Option.getD_some]
  exact isReq_of_meet hfm

/-- A declared name that must be present is present, read off the admission. -/
theorem mem_keys_of_isReq {c : Body} {keys : Finset Name}
    (hv : valPresentT c.fields c.at keys = true) {k : Name} (hc : k ∈ c.fields)
    (hreq : Field.isReq (c.at ⟨k, hc⟩) = true) : k ∈ keys := by
  rw [valPresentT_req] at hv
  exact of_decide_eq_true hv ⟨k, hc⟩ hreq

/-- **The presence side of the object row.** A declared name that must be present is present,
    and the required names of the meet are the union of the factors' — which is a statement
    about the intersection only because `Body.reqShared` holds both ways. -/
theorem valPresentT_meet {a b : Body} (hab : Body.reqShared a b = true)
    (hba : Body.reqShared b a = true) (hok : Body.meetOk a b = true) (keys : Finset Name) :
    valPresentT (Body.shared a b) (fun k => Body.meetField a b k) keys
      = (valPresentT a.fields a.at keys && valPresentT b.fields b.at keys) := by
  rw [valPresentT_req, valPresentT_req, valPresentT_req, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  unfold Body.reqShared at hab hba
  have hA := of_decide_eq_true hab
  have hB := of_decide_eq_true hba
  constructor
  · intro hs
    refine ⟨fun k hreq => ?_, fun k hreq => ?_⟩
    · have hk : k.1 ∈ Body.shared a b := mem_shared_iff.mpr ⟨k.2, hA k hreq⟩
      refine hs ⟨k.1, hk⟩ ?_
      rw [isReq_meetField hok ⟨k.1, hk⟩, hreq, Bool.true_or]
    · have hk : k.1 ∈ Body.shared a b := mem_shared_iff.mpr ⟨hB k hreq, k.2⟩
      refine hs ⟨k.1, hk⟩ ?_
      rw [isReq_meetField hok ⟨k.1, hk⟩, hreq, Bool.or_true]
  · rintro ⟨hA', hB'⟩ k hreq
    rw [isReq_meetField hok k, Bool.or_eq_true] at hreq
    rcases hreq with hr | hr
    · exact hA' ⟨k.1, Body.mem_shared_left k.2⟩ hr
    · exact hB' ⟨k.1, Body.mem_shared_right k.2⟩ hr



/-- A body admits a map by two tests: the declared names that must be present are, and every present name passes its row. -/
theorem AdmBody_map (c : Body) (keys : Finset Name) (g : {k // k ∈ keys} → Value) :
    AdmBody c (.map keys g)
      = (valPresentT c.fields c.at keys
         && objAdmV ⟨c.fields, fun k => AdmField (c.at k)⟩ (AdmRest c.rest) keys g) := by
  cases c; rfl

/-- A body admits nothing that is not a map. -/
theorem AdmBody_of_not_map {c : Body} {v : Value} (h : ∀ keys g, v ≠ .map keys g) :
    AdmBody c v = false := by
  cases c with
  | mk fields fld rest =>
    cases v with
    | map keys g => exact absurd rfl (h keys g)
    | _ => rfl

/-- The bottom is the only term that reads as the bottom. -/
theorem eq_never_of_isNever {t : Term} (h : t.isNever = true) : t = .never := by
  cases t <;> simp only [Term.isNever, Bool.false_eq_true] at h <;> rfl

/-- **The required-name test is sound once the partner is closed.** If both bodies admit one
    map, every name the left requires is a name the right declares: the value carries it, and a
    closed body refuses a name it does not declare. -/
theorem reqShared_of_adm {a b : Body} (hrb : AdmRest b.rest = none)
    {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (hA : AdmBody a (.map keys g) = true) (hB : AdmBody b (.map keys g) = true) :
    Body.reqShared a b = true := by
  rw [AdmBody_map, Bool.and_eq_true] at hA hB
  have hB2 := hB.2
  unfold objAdmV at hB2
  have hrow := of_decide_eq_true hB2
  refine decide_eq_true (fun k hreq => ?_)
  refine Decidable.byContradiction (fun hnb => ?_)
  have hk := mem_keys_of_isReq hA.1 k.2 hreq
  have := hrow ⟨k.1, hk⟩
  rw [entryP, MapOf.at, dif_neg hnb, hrb] at this
  exact absurd this (by simp)



/-- A field that admits nothing at a name that must be present is a field that must be present. -/
theorem isReq_of_isBottom {f : Field} (h : Field.isBottom f = true) : Field.isReq f = true := by
  cases f <;> simp only [Field.isBottom, Field.isReq, Bool.false_eq_true] at h ⊢

/-- …and it admits no value at all. -/
theorem AdmField_of_isBottom {f : Field} (h : Field.isBottom f = true) (w : Value) :
    AdmField f w = false := by
  cases f with
  | req t => rw [show t = .never from eq_never_of_isNever h]; rfl
  | fallback t d => rw [show t = .never from eq_never_of_isNever h]; rfl
  | optional t => exact absurd h (by simp [Field.isBottom])

/-- A present name that the body declares goes through that name's field. -/
theorem objAdmV_row {c : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (hB : objAdmV ⟨c.fields, fun k => AdmField (c.at k)⟩ (AdmRest c.rest) keys g = true)
    {k : Name} (hk : k ∈ keys) (hc : k ∈ c.fields) :
    AdmField (c.at ⟨k, hc⟩) (g ⟨k, hk⟩) = true := by
  unfold objAdmV at hB
  have hh := of_decide_eq_true hB ⟨k, hk⟩
  rwa [entryP, MapOf.at, dif_pos hc] at hh

/-- **No shared field meets to the bottom at a value both bodies admit.** A field that does
    must be present for one factor, so the value carries the name, and the two rows at it
    conjoin to the meet's row — which admits nothing. -/
theorem isBottom_false_of_adm {a b : Body}
    (ihf : ∀ (k : {k // k ∈ Body.shared a b}) (w : Value),
      AdmField (Body.meetField a b k) w
        = (AdmField (a.at ⟨k.1, Body.mem_shared_left k.2⟩) w
            && AdmField (b.at ⟨k.1, Body.mem_shared_right k.2⟩) w))
    (hok : Body.meetOk a b = true)
    {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (hA : AdmBody a (.map keys g) = true) (hB : AdmBody b (.map keys g) = true) :
    ∀ k, Field.isBottom (Body.meetField a b k) = false := by
  rw [AdmBody_map, Bool.and_eq_true] at hA hB
  intro k
  refine Bool.eq_false_iff.mpr (fun hbot => ?_)
  have ha := Body.mem_shared_left k.2
  have hb := Body.mem_shared_right k.2
  have hreq : Field.isReq (Body.meetField a b k) = true := isReq_of_isBottom hbot
  rw [isReq_meetField hok k, Bool.or_eq_true] at hreq
  have hk : k.1 ∈ keys := by
    rcases hreq with hr | hr
    · exact mem_keys_of_isReq hA.1 ha hr
    · exact mem_keys_of_isReq hB.1 hb hr
  have hrowA := objAdmV_row hA.2 hk ha
  have hrowB := objAdmV_row hB.2 hk hb
  have := ihf k (g ⟨k.1, hk⟩)
  rw [AdmField_of_isBottom hbot, hrowA, hrowB] at this
  exact absurd this (by simp)



/-- What two objects answer: the refusal where the rests do not merge or a `drop` factor does not
    declare every name the other declares, the bottom where the required names do not fit the
    intersection or a shared field meets to the bottom, and otherwise the object over the shared
    names. -/
theorem meet_object_object {a b : Body} {z : Term}
    (h : Term.meet (.object a) (.object b) = some z) :
    ∃ r, Rest.merge a.rest b.rest = some r ∧
      ((z = .never ∧ ¬ (Body.reqShared a b = true ∧ Body.reqShared b a = true))
       ∨ (Body.reqShared a b = true ∧ Body.reqShared b a = true ∧ Body.meetOk a b = true ∧
          ((z = .never ∧ ¬ (∀ k, Field.isBottom (Body.meetField a b k) = false))
           ∨ z = .object (.mk (Body.shared a b) (fun k => Body.meetField a b k) r)))) := by
  rw [Term.meet.eq_def] at h
  simp only [] at h
  unfold Body.meetTerm at h
  split at h
  next r hr =>
    refine ⟨r, hr, ?_⟩
    split at h
    next =>
      split at h
      next =>
        split at h
        next hreq =>
          rw [Bool.and_eq_true] at hreq
          split at h
          next hok =>
            split at h
            next _ => exact Or.inr ⟨hreq.1, hreq.2, hok, Or.inr (Option.some.inj h).symm⟩
            next hnb =>
              exact Or.inr ⟨hreq.1, hreq.2, hok,
                Or.inl ⟨(Option.some.inj h).symm, fun hall => hnb (decide_eq_true hall)⟩⟩
          next => exact absurd h (by simp)
        next hreq =>
          exact Or.inl ⟨(Option.some.inj h).symm, fun hc => hreq (Bool.and_eq_true _ _ ▸ hc)⟩
      next => exact absurd h (by simp)
    next => exact absurd h (by simp)
  next => exact absurd h (by simp)






/-- A field met with a record's term carries two terms that meet, and each field's row is its term's. -/
theorem AdmField_meetT {f fm : Field} {y : Term} (h : Field.meetT f y = some fm) :
    ∃ tx tz, Term.meet tx y = some tz ∧
      AdmField f = Adm tx ∧ AdmField fm = Adm tz ∧ Field.depth f = Term.depth tx + 1 := by
  cases f <;>
    simp only [Field.meetT, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨tz, hz, rfl⟩ := h <;>
    exact ⟨_, tz, hz, rfl, rfl, rfl⟩

/-- …and keeps the field's mark, because the record says nothing about presence. -/
theorem isReq_of_meetT {f fm : Field} {y : Term} (h : Field.meetT f y = some fm) :
    Field.isReq fm = Field.isReq f := by
  cases f <;>
    simp only [Field.meetT, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨tz, _, rfl⟩ := h <;> rfl

/-- What an object and a record answer: only a `codec` rest reads an undeclared name the way a
    record does, so the other two refuse; the record's value term meets every declared field and
    the rest's own codec. -/
theorem meet_object_record {b : Body} {x z : Term}
    (h : Body.meetRec b x = some z) :
    ∃ t r, b.rest = .codec t ∧ Term.meet t x = some r ∧ Body.meetRecOk b x = true ∧
      ((z = .never ∧ ¬ (∀ k, Field.isBottom (Body.meetRecField b x k) = false))
       ∨ z = .object (.mk b.fields (fun k => Body.meetRecField b x k) (.codec r))) := by
  unfold Body.meetRec at h
  split at h
  next t ht =>
    split at h
    next hok =>
      split at h
      next r hmr =>
        refine ⟨t, r, ht, hmr, hok, ?_⟩
        split at h
        next _ => exact Or.inr (Option.some.inj h).symm
        next hnb =>
          exact Or.inl ⟨(Option.some.inj h).symm, fun hall => hnb (decide_eq_true hall)⟩
      next => exact absurd h (by simp)
    next => exact absurd h (by simp)
  next => exact absurd h (by simp)



/-- The record says nothing about presence, so the marks and the presence test are the
    object's. -/
theorem valPresentT_meetRec {b : Body} {x : Term} (hok : Body.meetRecOk b x = true)
    (keys : Finset Name) :
    valPresentT b.fields (fun k => Body.meetRecField b x k) keys
      = valPresentT b.fields b.at keys := by
  rw [valPresentT_req, valPresentT_req]
  unfold Body.meetRecOk at hok
  refine decide_eq_decide.mpr (forall_congr' fun k => ?_)
  obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (of_decide_eq_true hok k)
  unfold Body.meetRecField
  rw [hfm, Option.getD_some, isReq_of_meetT hfm]

/-- …and every present name goes through its field and the record's term alike, a declared
    name through the field and an undeclared one through the rest. -/
theorem objAdmV_meetRec {b : Body} {x t r : Term}
    (ihf : ∀ (k : {k // k ∈ b.fields}) (w : Value),
      AdmField (Body.meetRecField b x k) w = (AdmField (b.at k) w && Adm x w))
    (iht : ∀ w, Adm r w = (Adm t w && Adm x w))
    (keys : Finset Name) (g : {k // k ∈ keys} → Value) :
    objAdmV ⟨b.fields, fun k => AdmField (Body.meetRecField b x k)⟩ (some (Adm r)) keys g
      = (objAdmV ⟨b.fields, fun k => AdmField (b.at k)⟩ (some (Adm t)) keys g
         && decide (∀ k : {k // k ∈ keys}, Adm x (g k) = true)) := by
  simp only [objAdmV, entryP, MapOf.at]
  refine decide_forall_and (fun k => ?_)
  by_cases hk : k.1 ∈ b.fields
  · simp only [dif_pos hk]
    exact ihf ⟨k.1, hk⟩ (g k)
  · simp only [dif_neg hk]
    exact iht (g k)

/-- No declared field meets the record's term to the bottom at a value both admit. -/
theorem isBottom_false_of_admRec {b : Body} {x : Term} (hok : Body.meetRecOk b x = true)
    (ihf : ∀ (k : {k // k ∈ b.fields}) (w : Value),
      AdmField (Body.meetRecField b x k) w = (AdmField (b.at k) w && Adm x w))
    {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (hA : AdmBody b (.map keys g) = true)
    (hR : decide (∀ k : {k // k ∈ keys}, Adm x (g k) = true) = true) :
    ∀ k, Field.isBottom (Body.meetRecField b x k) = false := by
  rw [AdmBody_map, Bool.and_eq_true] at hA
  intro k
  refine Bool.eq_false_iff.mpr (fun hbot => ?_)
  have hisreq : Field.isReq (Body.meetRecField b x k) = Field.isReq (b.at k) := by
    unfold Body.meetRecOk at hok
    obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (of_decide_eq_true hok k)
    unfold Body.meetRecField
    rw [hfm, Option.getD_some]
    exact isReq_of_meetT hfm
  have hreq : Field.isReq (b.at k) = true := hisreq ▸ isReq_of_isBottom hbot
  have hk : k.1 ∈ keys := mem_keys_of_isReq hA.1 k.2 hreq
  have hrow := objAdmV_row hA.2 hk k.2
  have hrec := of_decide_eq_true hR ⟨k.1, hk⟩
  have := ihf k (g ⟨k.1, hk⟩)
  rw [AdmField_of_isBottom hbot, hrow, hrec] at this
  exact absurd this (by simp)




/-- Every present name is declared, where the rest refuses an undeclared one. -/
theorem mem_fields_of_adm {b : Body} (hr : AdmRest b.rest = none)
    {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (h : AdmBody b (.map keys g) = true) : ∀ k ∈ keys, k ∈ b.fields := by
  rw [AdmBody_map, Bool.and_eq_true] at h
  have h2 := h.2
  unfold objAdmV at h2
  intro k hk
  refine Decidable.byContradiction (fun hnb => ?_)
  have hh := of_decide_eq_true h2 ⟨k, hk⟩
  rw [entryP, MapOf.at, dif_neg hnb, hr] at hh
  exact absurd hh (by simp)

/-- A field's row carries its literal alternatives, where it has any. -/
theorem altsOkV_of_AdmField {f : Field} {v : Value} (h : AdmField f v = true) :
    altsOkV (altsOfField f) v = true := by
  cases f with
  | req t => cases t <;> first | rfl | exact h
  | optional t => cases t <;> first | rfl | exact h
  | fallback t d => cases t <;> first | rfl | exact h

/-- **A closed object's structural test is its row.** Where the rest refuses an undeclared
    name, a value the body admits passes `keysOk` and `literalsOk`. An OPEN object is the case
    this fails at, which is why `unionOk` excludes one. -/
theorem structural_of_AdmBody {b : Body} (hr : AdmRest b.rest = none)
    {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (h : AdmBody b (.map keys g) = true) :
    (keysOk b.spec keys && literalsOk b.spec keys g) = true := by
  have hsub := mem_fields_of_adm hr h
  have h' := h
  rw [AdmBody_map, Bool.and_eq_true] at h'
  cases b with
  | mk fields fld rest =>
    refine Bool.and_eq_true _ _ |>.mpr ⟨?_, ?_⟩
    · exact keysOk_of_names hsub (fun k hreq => mem_keys_of_isReq h'.1 k.2 hreq)
    · refine decide_eq_true (fun k => ?_)
      have hkf : k.1 ∈ fields := hsub k.1 k.2
      show litOkV _ k.1 (g k) = true
      rw [litOkV, show (Body.spec (.mk fields fld rest)).at k.1
            = some ⟨_, altsOfField (fld ⟨k.1, hkf⟩)⟩ from by
          rw [Body.spec, MapOf.at, dif_pos hkf]]
      exact altsOkV_of_AdmField (objAdmV_row h'.2 k.2 hkf)



/-- A list admits a value exactly when one of its terms does. -/
theorem AdmAny_iff : ∀ {os : List Term} {v : Value},
    AdmAny os v = true ↔ ∃ t ∈ os, Adm t v = true
  | [], v => by simp
  | t :: ts, v => by
      rw [AdmAny_cons, Bool.or_eq_true, AdmAny_iff]
      constructor
      · rintro (h | ⟨u, hu, h⟩)
        · exact ⟨t, by simp, h⟩
        · exact ⟨u, by simp [hu], h⟩
      · rintro ⟨u, hu, h⟩
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact Or.inl h
        · exact Or.inr ⟨u, hu', h⟩

/-- **A certified union's admission is the join of its options'.** `selOptV` answers where
    exactly one option admits structurally; the certificate makes that at most one, and makes
    each option's structural test its row. -/
theorem selOptV_eq_AdmAny {os : List Term} (hc : unionOk os = true) (v : Value) :
    selOptV (AdmSpecs os) v = AdmAny os v := by
  simp only [unionOk, Bool.and_eq_true, List.all_eq_true] at hc
  have hclosed : ∀ t ∈ os, t.isOpenObject = false := fun t ht => by
    have := hc.1.2 t ht; simpa using this
  have hbridge : ∀ t ∈ os, Adm t v = true → admitOptV (specOf t, Adm t) v = true := by
    intro t ht h
    cases t with
    | object b =>
      have hr : AdmRest b.rest = none := by
        cases hrest : b.rest with
        | drop => rfl
        | refuse => rfl
        | codec _ =>
          exact absurd (hclosed _ ht) (by simp [Term.isOpenObject, hrest, Rest.isOpen])
      cases b with
      | mk fields fld rest =>
        cases v with
        | map keys g => simpa only [admitOptV, specOf] using structural_of_AdmBody hr h
        | _ => exact absurd h (by simp [Adm, AdmBody])
    | _ => exact h
  have hlen : (os.filter (fun t => admitOptV (specOf t, Adm t) v)).length ≤ 1 := by
    have hone := (admitsAtMostOne_of_orth (pairwise_of_orthAll hc.1.1)).1 v
    rwa [semsOf, ← optionSems_eq, filter_AdmSpecs (fun t _ => Adm_exact t) v,
      List.length_map] at hone
  rw [selOptV, AdmSpecs_eq, filter_map_AdmSpecs]
  cases hL : os.filter (fun t => admitOptV (specOf t, Adm t) v) with
  | nil =>
    refine (Bool.eq_false_iff.mpr (fun hany => ?_)).symm ▸ rfl
    obtain ⟨t, ht, hat⟩ := AdmAny_iff.mp hany
    have : t ∈ os.filter (fun t => admitOptV (specOf t, Adm t) v) :=
      List.mem_filter.mpr ⟨ht, hbridge t ht hat⟩
    rw [hL] at this
    exact absurd this (by simp)
  | cons o rest =>
    cases rest with
    | cons _ _ => rw [hL] at hlen; simp at hlen
    | nil =>
      have ho : o ∈ os ∧ admitOptV (specOf o, Adm o) v = true := by
        have : o ∈ os.filter (fun t => admitOptV (specOf t, Adm t) v) := by rw [hL]; simp
        exact ⟨List.mem_of_mem_filter this, (List.mem_filter.mp this).2⟩
      simp only [List.map_cons, List.map_nil]
      cases hao : Adm o v with
      | true => exact (AdmAny_iff.mpr ⟨o, ho.1, hao⟩).symm
      | false =>
        refine (Bool.eq_false_iff.mpr (fun hany => ?_)).symm
        obtain ⟨t, ht, hat⟩ := AdmAny_iff.mp hany
        have htl : t ∈ os.filter (fun t => admitOptV (specOf t, Adm t) v) :=
          List.mem_filter.mpr ⟨ht, hbridge t ht hat⟩
        rw [hL, List.mem_singleton] at htl
        rw [htl] at hat
        exact absurd hat (by rw [hao]; simp)
/-! ### The same equation on the read side

The value side needs only `AdmRest`, which is `none` at `drop` and at `refuse` alike. The read
side needs the certificate's third conjunct twice over, and the two lemmas below are where it is
spent: `mem_fields_of_admA` at the undeclared name, `mem_keys_of_isReqA` at the declared and
absent one. -/

/-- `AdmABody` at a map, unfolded. -/
theorem AdmABody_map {b : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Attr} :
    AdmABody b (.m keys g)
      = (reqPresentT b.fields b.at keys &&
         objAdmA ⟨b.fields, fun k => AdmAField (b.at k)⟩ (AdmARest b.rest)
           (keepT b.rest b.fields) keys g) := by
  cases b; rfl

/-- A field's row carries its literal alternatives on the read side, where it has any —
    `altsOkV_of_AdmField`'s twin, through `ExactA` because `altsOkA` asks the codec. -/
theorem altsOkA_of_AdmAField {f : Field} {a : Attr} (h : AdmAField f a = true) :
    altsOkA (altsOfField f) a = true := by
  cases f with
  | req t => cases t <;> first | rfl | exact (AdmA_exact _ a).mp h
  | optional t => cases t <;> first | rfl | exact (AdmA_exact _ a).mp h
  | fallback t d => cases t <;> first | rfl | exact (AdmA_exact _ a).mp h

/-- Every present name is declared, where the rest REFUSES an undeclared one. `drop` skips it,
    and a name that is skipped is read, which is why the certificate excludes a `drop` option. -/
theorem mem_fields_of_admA {b : Body} (hr : b.rest = .refuse)
    {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (h : AdmABody b (.m keys g) = true) : ∀ k ∈ keys, k ∈ b.fields := by
  rw [AdmABody_map, Bool.and_eq_true] at h
  have h2 := h.2
  unfold objAdmA at h2
  intro k hk
  refine Decidable.byContradiction (fun hnb => ?_)
  have hh := of_decide_eq_true h2 ⟨k, hk⟩ (by rw [hr]; rfl)
  rw [entryPA, MapOf.at, dif_neg hnb, hr] at hh
  exact absurd hh (by simp [AdmARest])

/-- A declared name that must be present on both halves is present. `fallback` is where the two
    halves part, and the certificate excludes it for that. -/
theorem mem_keys_of_isReqA {b : Body} {keys : Finset Name}
    (hnf : ∀ k : {k // k ∈ b.fields}, Field.presenceAgrees (b.at k) = true)
    (hv : reqPresentT b.fields b.at keys = true) {k : Name} (hc : k ∈ b.fields)
    (hreq : Field.isReq (b.at ⟨k, hc⟩) = true) : k ∈ keys := by
  have hh := of_decide_eq_true hv ⟨k, hc⟩
  cases hf : b.at ⟨k, hc⟩ with
  | req t => rw [hf] at hh; exact of_decide_eq_true hh
  | optional t => rw [hf] at hreq; exact absurd hreq (by simp [Field.isReq])
  | fallback t d =>
      have := hnf ⟨k, hc⟩
      rw [hf] at this
      exact absurd this (by simp [Field.presenceAgrees])

/-- One kept entry of the read-side object row — `objAdmV_row`'s twin, with the keep filter as a
    hypothesis because `keepT` is the half the two sides do not share. -/
theorem objAdmA_row {c : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hB : objAdmA ⟨c.fields, fun k => AdmAField (c.at k)⟩ (AdmARest c.rest)
            (keepT c.rest c.fields) keys g = true)
    {k : Name} (hk : k ∈ keys) (hc : k ∈ c.fields)
    (hkeep : keepT c.rest c.fields k = true) :
    AdmAField (c.at ⟨k, hc⟩) (g ⟨k, hk⟩) = true := by
  unfold objAdmA at hB
  have hh := of_decide_eq_true hB ⟨k, hk⟩ hkeep
  rwa [entryPA, MapOf.at, dif_pos hc] at hh

/-- **An object option whose halves agree about names has its structural test for a read row.**
    `structural_of_AdmBody`'s twin, and it needs both halves of `objectNamesAgree` where the
    value side needs neither. -/
theorem structural_of_AdmABody {b : Body} (hr : b.rest = .refuse)
    (hnf : ∀ k : {k // k ∈ b.fields}, Field.presenceAgrees (b.at k) = true)
    {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (h : AdmABody b (.m keys g) = true) :
    (keysOk b.spec keys && literalsOkA b.spec keys g) = true := by
  have hsub := mem_fields_of_admA hr h
  have h' := h
  rw [AdmABody_map, Bool.and_eq_true] at h'
  have hkeepall : ∀ k, keepT b.rest b.fields k = true := fun _ => by rw [hr]; rfl
  cases hb : b with
  | mk fields fld rest =>
    subst hb
    refine Bool.and_eq_true _ _ |>.mpr ⟨?_, ?_⟩
    · exact keysOk_of_names hsub (fun k hreq => mem_keys_of_isReqA hnf h'.1 k.2 hreq)
    · refine decide_eq_true (fun k => ?_)
      have hkf : k.1 ∈ fields := hsub k.1 k.2
      show litOkA _ k.1 (g k) = true
      rw [litOkA, show (Body.spec (.mk fields fld rest)).at k.1
            = some ⟨_, altsOfField (fld ⟨k.1, hkf⟩)⟩ from by
          rw [Body.spec, MapOf.at, dif_pos hkf]]
      exact altsOkA_of_AdmAField (objAdmA_row h'.2 k.2 hkf (hkeepall k.1))

/-- A list reads an attribute exactly when one of its terms does. -/
theorem AdmAAny_iff : ∀ {os : List Term} {a : Attr},
    AdmAAny os a = true ↔ ∃ t ∈ os, AdmA t a = true
  | [], a => by simp
  | t :: ts, a => by
      rw [AdmAAny_cons, Bool.or_eq_true, AdmAAny_iff]
      constructor
      · rintro (h | ⟨u, hu, h⟩)
        · exact ⟨t, by simp, h⟩
        · exact ⟨u, by simp [hu], h⟩
      · rintro ⟨u, hu, h⟩
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact Or.inl h
        · exact Or.inr ⟨u, hu', h⟩

/-- The certificate's third conjunct, in the two forms the bridge takes. -/
theorem namesAgree_parts {b : Body} (h : objectNamesAgree (.object b) = true) :
    b.rest = .refuse ∧ ∀ k : {k // k ∈ b.fields}, Field.presenceAgrees (b.at k) = true := by
  rw [objectNamesAgree, Bool.and_eq_true] at h
  refine ⟨?_, of_decide_eq_true h.2⟩
  cases hr : b.rest with
  | refuse => rfl
  | drop => rw [hr] at h; exact absurd h.1 (by simp)
  | codec t => rw [hr] at h; exact absurd h.1 (by simp)

/-- **A certified union reads the join of its options'.** `selOptV_eq_AdmAny`'s twin. `selOptA`
    answers where exactly one option admits structurally; the certificate makes that at most one,
    and makes each option's structural test its read row. -/
theorem selOptA_eq_AdmAAny {os : List Term} (hc : unionOk os = true) (a : Attr) :
    selOptA (AdmASpecs os) a = AdmAAny os a := by
  simp only [unionOk, Bool.and_eq_true, List.all_eq_true] at hc
  have hbridge : ∀ t ∈ os, AdmA t a = true → admitOptA (specOf t, AdmA t) a = true := by
    intro t ht h
    cases t with
    | object b =>
      obtain ⟨hr, hnf⟩ := namesAgree_parts (hc.2 _ ht)
      cases a with
      | m keys g => simpa only [admitOptA, specOf] using structural_of_AdmABody hr hnf h
      | _ => exact absurd h (by cases b; simp [AdmA, AdmABody])
    | _ => exact h
  have hlen : (os.filter (fun t => admitOptA (specOf t, AdmA t) a)).length ≤ 1 := by
    have hone := (admitsAtMostOne_of_orth (pairwise_of_orthAll hc.1.1)).2 a
    rwa [semsOf, ← optionSems_eq, filter_AdmASpecs (fun t _ => AdmA_exact t) a,
      List.length_map] at hone
  rw [selOptA, AdmASpecs_eq, filter_map_AdmASpecs]
  cases hL : os.filter (fun t => admitOptA (specOf t, AdmA t) a) with
  | nil =>
    refine (Bool.eq_false_iff.mpr (fun hany => ?_)).symm |>.symm ▸ rfl
    obtain ⟨t, ht, hat⟩ := AdmAAny_iff.mp hany
    have : t ∈ os.filter (fun t => admitOptA (specOf t, AdmA t) a) :=
      List.mem_filter.mpr ⟨ht, hbridge t ht hat⟩
    rw [hL] at this
    exact absurd this (by simp)
  | cons o rest =>
    cases rest with
    | cons _ _ => rw [hL] at hlen; simp at hlen
    | nil =>
      have ho : o ∈ os ∧ admitOptA (specOf o, AdmA o) a = true := by
        have : o ∈ os.filter (fun t => admitOptA (specOf t, AdmA t) a) := by rw [hL]; simp
        exact ⟨List.mem_of_mem_filter this, (List.mem_filter.mp this).2⟩
      simp only [List.map_cons, List.map_nil]
      cases hao : AdmA o a with
      | true => exact (AdmAAny_iff.mpr ⟨o, ho.1, hao⟩).symm
      | false =>
        refine (Bool.eq_false_iff.mpr (fun hany => ?_)).symm
        obtain ⟨t, ht, hat⟩ := AdmAAny_iff.mp hany
        have htl : t ∈ os.filter (fun t => admitOptA (specOf t, AdmA t) a) :=
          List.mem_filter.mpr ⟨ht, hbridge t ht hat⟩
        rw [hL, List.mem_singleton] at htl
        rw [htl] at hat
        exact absurd hat (by rw [hao]; simp)

/-- The options that survive are the ones that admit; the bottoms admit nothing. -/
theorem AdmAny_filter_never : ∀ (ts : List Term) (v : Value),
    AdmAny (ts.filter (fun z => !z.isNever)) v = AdmAny ts v
  | [], _ => rfl
  | t :: ts, v => by
      cases ht : t.isNever with
      | true =>
        have htn : t = Term.never := eq_never_of_isNever ht
        subst htn
        rw [List.filter_cons, if_neg (by simp [Term.isNever]), AdmAny_cons,
          AdmAny_filter_never ts v]
        rfl
      | false =>
        rw [List.filter_cons, if_pos (by simp [ht]), AdmAny_cons, AdmAny_cons,
          AdmAny_filter_never ts v]

/-- A certified list of survivors admits what its options admit. -/
theorem Adm_ofOptions {ts : List Term} (hc : unionOk ts = true) (v : Value) :
    Adm (Term.ofOptions ts) v = AdmAny ts v := by
  match ts with
  | [] => rfl
  | [t] => simp only [Term.ofOptions, AdmAny_cons, AdmAny_nil, Bool.or_false]
  | _ :: _ :: _ => exact selOptV_eq_AdmAny hc v

/-- The join over the met options is the join over the options, met with the partner. -/
theorem AdmAny_meet {y : Term} (v : Value) : ∀ {os zs : List Term},
    List.Forall₂ (fun t w => ∀ u, Adm w u = (Adm t u && Adm y u)) os zs →
    AdmAny zs v = (AdmAny os v && Adm y v) := by
  intro os zs h
  induction h with
  | nil => simp
  | cons hh _ ihx =>
    rw [AdmAny_cons, AdmAny_cons, hh v, ihx]
    cases Adm _ v <;> cases Adm y v <;> simp

/-- A union's options, lifted from the meet of the terms to the meet of the rows. -/
theorem forall₂_lift {y : Term} {n : Nat}
    (ih : ∀ x y, Term.depth x + Term.depth y ≤ n → ∀ z, Term.meet x y = some z →
          ∀ w, Adm z w = (Adm x w && Adm y w)) :
    ∀ {os zs : List Term}, Term.depthL os + Term.depth y ≤ n →
      List.Forall₂ (fun t w => Term.meet t y = some w) os zs →
      List.Forall₂ (fun t w => ∀ u, Adm w u = (Adm t u && Adm y u)) os zs := by
  intro os
  induction os with
  | nil => intro zs _ h; cases h; exact .nil
  | cons t os' ihx =>
    intro zs hd h
    cases h with
    | cons hh hrest =>
      have h1 : Term.depth t ≤ Term.depthL (t :: os') := by simp [Term.depthL]
      have h2 : Term.depthL os' ≤ Term.depthL (t :: os') := by simp [Term.depthL]
      exact .cons (ih t y (by omega) _ hh) (ihx (by omega) hrest)



/-- What a union answers on the left: the options met one by one, the bottoms dropped, and
    both the options and the survivors certified. -/
theorem meet_union_left {os : List Term} {y z : Term}
    (h1 : y = .never → False)
    (h2 : ∀ (t : Term) (f g : Value → Value), y = .held t f g → False)
    (h3 : ∀ (t : Term) (r : Attr → Option Value), y = .legacy t r → False)
    (h4 : ∀ (ce : Value → Option Attr) (cp : Attr → Option Value), y = .custom ce cp → False)
    (h5 : ∀ (t : Term), y = .lazy t → False)
    (h : Term.meet (.union os) y = some z) :
    ∃ zs, List.Forall₂ (fun t w => Term.meet t y = some w) os zs ∧
      unionOk os = true ∧ unionOk (zs.filter (fun w => !w.isNever)) = true ∧
      z = Term.ofOptions (zs.filter (fun w => !w.isNever)) := by
  rw [Term.meet] at h
  · obtain ⟨zs, hzs, hg⟩ := Option.bind_eq_some_iff.mp h
    unfold Term.ofOptionsGuarded at hg
    split at hg
    next hok =>
      rw [Bool.and_eq_true] at hok
      refine ⟨zs, allSome_map_forall₂ _ ?_, hok.1, hok.2, (Option.some.inj hg).symm⟩
      rw [← attach_map_fun os (fun t => Term.meet t y)]
      exact hzs
    next => exact absurd hg (by simp)
  all_goals (intros; simp_all)

/-- …and on the right, where the left rows fire first so the partner's exclusions are six. -/
theorem meet_union_right {os : List Term} {x z : Term}
    (h1 : x = .never → False)
    (h2 : ∀ (t : Term) (f g : Value → Value), x = .held t f g → False)
    (h3 : ∀ (t : Term) (r : Attr → Option Value), x = .legacy t r → False)
    (h4 : ∀ (ce : Value → Option Attr) (cp : Attr → Option Value), x = .custom ce cp → False)
    (h5 : ∀ (t : Term), x = .lazy t → False)
    (h6 : ∀ (ts : List Term), x = .union ts → False)
    (h : Term.meet x (.union os) = some z) :
    ∃ zs, List.Forall₂ (fun t w => Term.meet t x = some w) os zs ∧
      unionOk os = true ∧ unionOk (zs.filter (fun w => !w.isNever)) = true ∧
      z = Term.ofOptions (zs.filter (fun w => !w.isNever)) := by
  rw [Term.meet] at h
  · obtain ⟨zs, hzs, hg⟩ := Option.bind_eq_some_iff.mp h
    unfold Term.ofOptionsGuarded at hg
    split at hg
    next hok =>
      rw [Bool.and_eq_true] at hok
      refine ⟨zs, allSome_map_forall₂ _ ?_, hok.1, hok.2, (Option.some.inj hg).symm⟩
      rw [← attach_map_fun os (fun t => Term.meet t x)]
      exact hzs
    next => exact absurd hg (by simp)
  all_goals (intros; simp_all)

set_option maxHeartbeats 4000000 in
/-- **The meet admits the intersection, by strong induction on the summed depth.** The measure
    is what a two-argument recursion needs: `Adm`'s structural trick is unavailable because the
    meet shrinks neither argument alone. -/
theorem Adm_meet_le : ∀ (n : Nat) (x y : Term), Term.depth x + Term.depth y ≤ n →
    ∀ z, Term.meet x y = some z → ∀ v : Value, Adm z v = (Adm x v && Adm y v) := by
  intro n
  induction n with
  | zero =>
      intro x y hle
      have h1 := Term.depth_pos x; have h2 := Term.depth_pos y; omega
  | succ n ih =>
      intro x y hle z h v
      cases x, y using Term.meet.fun_cases
      -- the four function-carrying terms, on the left
      case case3 => rename_i t f g hne; rw [meet_held_none t f g hne] at h; exact absurd h (by simp)
      case case4 => rename_i t r hne; rw [meet_legacy_none t r hne] at h; exact absurd h (by simp)
      case case5 => rename_i ce cp hne; rw [meet_custom_none ce cp hne] at h; exact absurd h (by simp)
      case case6 => rename_i t hne; rw [meet_lazy_none t hne] at h; exact absurd h (by simp)
      -- …and on the right, where the left rows fire first so only the bottom needs naming
      case case7 => rename_i t f g hne _ _ _ _; rw [meet_heldR_none hne t f g] at h; exact absurd h (by simp)
      case case8 => rename_i t r hne _ _ _ _; rw [meet_legacyR_none hne t r] at h; exact absurd h (by simp)
      case case9 => rename_i ce cp hne _ _ _ _; rw [meet_customR_none hne ce cp] at h; exact absurd h (by simp)
      case case10 => rename_i t hne _ _ _ _; rw [meet_lazyR_none hne t] at h; exact absurd h (by simp)
      -- a refinement whose predicate is a closure, and `opaque` against what it cannot compare:
      -- both refuse, and the partner is a variable, so the row reduces one constructor at a time
      case case14 | case90 => cases y <;> simp_all [Term.meet]
      case case16 | case91 => cases x <;> simp_all [Term.meet]
      -- two literals: the same value at the same base, or nothing
      case case57 =>
        rename_i k a k' a'
        simp only [Term.meet] at h
        cases k <;> cases k' <;> simp only [Term.meetLit, reduceCtorEq] at h <;>
          (try split at h) <;>
          (try (simp only [Option.some.injEq] at h
                subst h
                cases v <;> simp_all [Adm, AdmLit, inL, isStored, inD]))
      -- two set bases that write different wire families: a set is non-empty, so a base that
      -- refuses every element refuses the set
      case case65 =>
        rename_i b b' _ _ _ _ hb
        simp only [Term.meet, if_neg hb, Option.some.injEq] at h
        subst h
        cases b <;> cases b' <;> cases v <;>
          simp_all [Adm, SetBase.adm, isStored, inD, -Classical.not_forall] <;>
          (intros; exact NEFinset.not_forall_notMem _)
      -- the two set bases that share the `strSet` slot
      case case60 | case61 => simp [Term.meet] at h
      -- the same set base is itself
      case case64 =>
        simp only [Term.meet, if_true, ite_true, Option.some.injEq] at h
        subst h
        simp
      -- …and two different ones write different wire families
      -- the bottom absorbs, on either side
      case case1 => simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm]
      case case2 =>
        rw [meet_never_right] at h; simp only [Option.some.injEq] at h; subst h; simp [Adm]
      -- the ground bases: the same base is itself
      case case17 | case18 | case19 | case20 | case21 | case22 =>
        simp only [Term.meet, Option.some.injEq] at h; subst h; simp
      -- the `string`/`decimal` family, which shares values and so refuses
      case case23 | case24 | case26 | case29 | case50 | case54 => simp [Term.meet] at h
      -- a literal against its own base: the literal is the finer term, so the base adds nothing
      -- a literal against its own base: the literal is the finer term, so the base adds nothing.
      -- The `string` and `decimal` rows are explicit matches and reduce on their own; the other
      -- four bases still decide by `if`, and the condition is closed.
      case case25 | case28 | case43 | case46 | case49 | case53 =>
        simp only [Term.meet, Option.some.injEq] at h
        subst h
        cases v <;> simp [Adm, AdmLit, inL, isStored, inD] <;> (intro hs _; exact hs)
      case case31 | case33 | case35 | case37 | case39 | case41 =>
        simp only [Term.meet, if_true, ite_true, Option.some.injEq] at h
        subst h
        cases v <;> simp [Adm, AdmLit, inL, inD] <;> (intro hs _; exact hs)
      -- …and against any other base, nothing: the two write different value constructors
      -- …and against any other base, nothing: the two write different value constructors
      case case52 | case56 =>
        rename_i k _ _ _ _
        simp only [Term.meet, Option.some.injEq] at h
        subst h
        cases k <;> cases v <;> simp_all [Adm, AdmLit, inL, inD, isStored]
      case case27 | case30 | case45 | case48 =>
        rename_i k _ _ _
        simp only [Term.meet, Option.some.injEq] at h
        subst h
        cases k <;> cases v <;> simp_all [Adm, AdmLit, inL, inD, isStored]
      case case32 | case34 | case36 | case38 | case40 | case42 =>
        rename_i k _ hk
        simp only [Term.meet, if_neg hk, Option.some.injEq] at h
        subst h
        cases k <;> cases v <;> simp_all [Adm, AdmLit, inL, inD, isStored]
      -- `opaque` against a self-identifying base: the base is the finer term
      case case78 | case79 | case80 | case81 | case82 | case83 | case84 | case85 =>
        simp only [Term.meet, Option.some.injEq] at h
        subst h
        cases v <;>
          (try simp only [Adm_opaq_str, Adm_opaq_bool, Adm_opaq_bin, Adm_opaq_null]) <;>
          simp [Adm]
      -- …and against `number`, by the policy: the lossy one holds every stored double
      case case86 | case88 =>
        simp only [Term.meet, if_true, Option.some.injEq] at h
        subst h
        cases v <;> (try simp only [Adm_opaq_num]) <;> simp [Adm, inD]
      -- …and the refusing one none, so the pair is the bottom
      case case87 | case89 =>
        rename_i l hl
        simp only [Bool.not_eq_true] at hl
        subst hl
        simp only [Term.meet, Bool.false_eq_true, if_false, Option.some.injEq] at h
        subst h
        cases v <;> (try simp only [Adm_opaq_num]) <;> simp [Adm, inD]
      -- **the `number` family against the `decimal` family.** One member, different slots: the
      -- pair stores nothing together and reads a stored numeral together, so it has no meet.
      case case44 | case47 | case51 | case55 | case62 | case63 | case92 | case93 =>
        simp [Term.meet, Term.meetLit] at h
      -- **the catch-all: two constructors with no row of their own.** They occupy different
      -- value slots, so `Adm_and_false` answers the pair; `number` against `decimal` is the one
      -- pair that shares a member and needs the value split instead.
      case case94 =>
        clear ih hle
        cases x <;> (try (exfalso; solve_by_elim (maxDepth := 2) [rfl])) <;>
          cases y <;> (try (exfalso; solve_by_elim (maxDepth := 8) [rfl])) <;>
          (simp only [Term.meet, Option.some.injEq] at h; subst h)
        all_goals (first
          | (refine Eq.trans ?g1 (Adm_and_false ?g2 v).symm
             case g2 =>
               first
                 | rfl
                 | (cases ‹GroundKind› <;> rfl)
                 | (cases ‹SetBase› <;> rfl)
                 | (cases ‹GroundKind› <;> cases ‹SetBase› <;> rfl)
             case g1 => simp [Adm])
          | (cases v <;> simp [Adm, inD, isStored]))
      case case13 | case15 =>
        simp only [Term.meet] at h
        rw [if_pos (by assumption)] at h
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        have ihw := ih _ _ (by simp only [Term.depth] at hle; omega) w hw v
        simp only [Adm, ihw]
        simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
      -- the containers: the element rows meet, and the payload carries the conjunction
      case case58 =>
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [Term.meet] using h)
        have ihw := ih _ _ (by simp only [Term.depth] at hle; omega) w hw
        cases v <;> simp only [Adm, Bool.and_self, allP_and ihw]
      case case59 =>
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [Term.meet] using h)
        have ihw := ih _ _ (by simp only [Term.depth] at hle; omega) w hw
        cases v <;> simp only [Adm, Bool.and_self, decide_forall_and (fun k => ihw _)]
      case case67 | case68 =>
        obtain ⟨vs, tl, rfl, hts, htl⟩ := meet_array_tuple h
        obtain ⟨hb1, hb2⟩ := tuple_bounds_l hle
        cases v <;>
          simp only [Adm, Bool.and_self,
            alignP_meet_all (AdmList_forall₂ ih hb1 hts) (tailMeet_lift ih hb2 htl)]
      case case69 | case70 =>
        obtain ⟨vs, tl, rfl, hts, htl⟩ := meet_tuple_array h
        obtain ⟨hb1, hb2⟩ := tuple_bounds_r hle
        cases v <;> simp only [Adm, Bool.and_self] <;>
          rw [Bool.and_comm,
            alignP_meet_all (AdmList_forall₂ ih hb1 hts) (tailMeet_lift ih hb2 htl)]
      -- two tuples: one arity meets positionwise, and two arities with no tail admit no
      -- common array
      case case71 | case72 | case73 | case74 =>
        obtain ⟨hb1, hb2⟩ := tuple_bounds_tt hle
        rcases meet_tuple_tuple h with ⟨vs, tl, rfl, hlen, hF, htl⟩ | ⟨rfl, hne, rfl, rfl⟩
        · cases v <;> simp only [Adm, Bool.and_self,
            alignP_meet_zip (AdmList_forall₂_zip ih hb1 hF)
              (by rw [AdmList_length, AdmList_length]; exact hlen)
              (tailMeet_lift2 ih hb2 htl)]
        · cases v with
          | arr ws =>
            simp only [Adm, AdmOptT]
            cases hA : alignP (AdmList _) none ws with
            | false => simp
            | true =>
              cases hB : alignP (AdmList _) none ws with
              | false => simp
              | true =>
                exact absurd
                  (((alignP_none_length hA).trans (AdmList_length _)).symm.trans
                    ((alignP_none_length hB).trans (AdmList_length _))) hne
          | _ => simp [Adm]
      -- two `opaque`s: the policies conjoin, the refusing one being below the lossy one
      case case66 =>
        simp only [Term.meet, Option.some.injEq] at h
        subst h
        exact Adm_opaq_and _ _ v
      -- two objects: the declared names intersect, the required names unite, and the rests
      -- decide first
      case case77 =>
        rename_i a b
        obtain ⟨r, hr, hcase⟩ := meet_object_object h
        obtain ⟨hra, hrb, hrr⟩ := Rest.merge_admRest hr
        have ihf : Body.meetOk a b = true →
            ∀ (k : {k // k ∈ Body.shared a b}) (w : Value),
              AdmField (Body.meetField a b k) w
                = (AdmField (a.at ⟨k.1, Body.mem_shared_left k.2⟩) w
                    && AdmField (b.at ⟨k.1, Body.mem_shared_right k.2⟩) w) := by
          intro hok k w
          unfold Body.meetOk at hok
          obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (of_decide_eq_true hok k)
          obtain ⟨tx, ty, tz, hz, hx, hy, hfz, hdx, hdy⟩ := AdmField_meet hfm
          have hlt := Body.depth_lt_shared a b k
          simp only [Term.depth] at hle
          unfold Body.meetField
          rw [hfm, Option.getD_some, hfz, hx, hy]
          exact ih tx ty (by omega) tz hz w
        have hnm : ∀ w : Value, (∀ keys g, w ≠ .map keys g) →
            Adm z w = (Adm (.object a) w && Adm (.object b) w) := by
          intro w hw
          rw [show Adm (.object a) w = AdmBody a w from rfl,
              show Adm (.object b) w = AdmBody b w from rfl,
              AdmBody_of_not_map hw, AdmBody_of_not_map hw, Bool.and_self]
          rcases hcase with ⟨rfl, _⟩ | ⟨_, _, _, ⟨rfl, _⟩ | rfl⟩
          · rfl
          · rfl
          · exact AdmBody_of_not_map hw
        cases v
        case map keys g =>
          rw [show Adm (.object a) (.map keys g) = AdmBody a (.map keys g) from rfl,
              show Adm (.object b) (.map keys g) = AdmBody b (.map keys g) from rfl]
          rcases hcase with ⟨rfl, hne⟩ | ⟨hab, hba, hok, ⟨rfl, hnb⟩ | rfl⟩
          · show (false : Bool) = _
            cases hA : AdmBody a (.map keys g) with
            | false => rfl
            | true =>
              cases hB : AdmBody b (.map keys g) with
              | false => rfl
              | true => exact absurd ⟨reqShared_of_adm hrb hA hB, reqShared_of_adm hra hB hA⟩ hne
          · show (false : Bool) = _
            cases hA : AdmBody a (.map keys g) with
            | false => rfl
            | true =>
              cases hB : AdmBody b (.map keys g) with
              | false => rfl
              | true => exact absurd (isBottom_false_of_adm (ihf hok) hok hA hB) hnb
          · show AdmBody (.mk (Body.shared a b) (fun k => Body.meetField a b k) r)
                (.map keys g) = _
            rw [AdmBody_map, AdmBody_map, AdmBody_map]
            simp only [Body.fields_mk, Body.at_mk, Body.rest_mk, hra, hrb, hrr]
            rw [valPresentT_meet hab hba hok, objAdmV_meet (ihf hok)]
            simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
        all_goals exact hnm _ (fun _ _ hc => Value.noConfusion hc)
      -- an object against a record: only a `codec` rest reads an undeclared name the way a
      -- record does, and the record's term meets every field and the rest's codec
      case case75 =>
        rename_i b x
        have hmr : Body.meetRec b x = some z := by rw [Term.meet.eq_def] at h; simpa using h
        obtain ⟨t, r, hrest, hmt, hok, hcase⟩ := meet_object_record hmr
        simp only [Term.depth] at hle
        have hdt := Body.depth_lt_rest b hrest
        have iht : ∀ w, Adm r w = (Adm t w && Adm x w) := ih t x (by omega) r hmt
        have ihf : ∀ (k : {k // k ∈ b.fields}) (w : Value),
            AdmField (Body.meetRecField b x k) w = (AdmField (b.at k) w && Adm x w) := by
          intro k w
          unfold Body.meetRecOk at hok
          obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (of_decide_eq_true hok k)
          obtain ⟨tx, tz, hz, hx, hfz, hdx⟩ := AdmField_meetT hfm
          have hlt := Body.depth_lt_field b k
          unfold Body.meetRecField
          rw [hfm, Option.getD_some, hfz, hx]
          exact ih tx x (by omega) tz hz w
        have hnm : ∀ w : Value, (∀ keys g, w ≠ .map keys g) →
            Adm z w = (Adm (.object b) w && Adm (.record x) w) := by
          intro w hw
          have hrx : Adm (.record x) w = false := by
            cases w with
            | map keys g => exact absurd rfl (hw keys g)
            | _ => rfl
          rw [show Adm (.object b) w = AdmBody b w from rfl, AdmBody_of_not_map hw, hrx,
            Bool.and_self]
          rcases hcase with ⟨rfl, _⟩ | rfl
          · rfl
          · exact AdmBody_of_not_map hw
        cases v
        case map keys g =>
          rw [show Adm (.object b) (.map keys g) = AdmBody b (.map keys g) from rfl,
              show Adm (.record x) (.map keys g)
                = decide (∀ k : {k // k ∈ keys}, Adm x (g k) = true) from rfl]
          rcases hcase with ⟨rfl, hnb⟩ | rfl
          · show (false : Bool) = _
            cases hA : AdmBody b (.map keys g) with
            | false => rfl
            | true =>
              cases hR : decide (∀ k : {k // k ∈ keys}, Adm x (g k) = true) with
              | false => rfl
              | true => exact absurd (isBottom_false_of_admRec hok ihf hA hR) hnb
          · show AdmBody (.mk b.fields (fun k => Body.meetRecField b x k) (.codec r))
                  (.map keys g) = _
            rw [AdmBody_map, AdmBody_map]
            simp only [Body.fields_mk, Body.at_mk, Body.rest_mk, hrest]
            rw [valPresentT_meetRec hok, show AdmRest (.codec r) = some (Adm r) from rfl,
                show AdmRest (.codec t) = some (Adm t) from rfl, objAdmV_meetRec ihf iht]
            simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
        all_goals exact hnm _ (fun _ _ hc => Value.noConfusion hc)
      case case76 =>
        rename_i x b
        have hmr : Body.meetRec b x = some z := by rw [Term.meet.eq_def] at h; simpa using h
        obtain ⟨t, r, hrest, hmt, hok, hcase⟩ := meet_object_record hmr
        simp only [Term.depth] at hle
        have hdt := Body.depth_lt_rest b hrest
        have iht : ∀ w, Adm r w = (Adm t w && Adm x w) := ih t x (by omega) r hmt
        have ihf : ∀ (k : {k // k ∈ b.fields}) (w : Value),
            AdmField (Body.meetRecField b x k) w = (AdmField (b.at k) w && Adm x w) := by
          intro k w
          unfold Body.meetRecOk at hok
          obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (of_decide_eq_true hok k)
          obtain ⟨tx, tz, hz, hx, hfz, hdx⟩ := AdmField_meetT hfm
          have hlt := Body.depth_lt_field b k
          unfold Body.meetRecField
          rw [hfm, Option.getD_some, hfz, hx]
          exact ih tx x (by omega) tz hz w
        have hnm : ∀ w : Value, (∀ keys g, w ≠ .map keys g) →
            Adm z w = (Adm (.record x) w && Adm (.object b) w) := by
          intro w hw
          have hrx : Adm (.record x) w = false := by
            cases w with
            | map keys g => exact absurd rfl (hw keys g)
            | _ => rfl
          rw [show Adm (.object b) w = AdmBody b w from rfl, AdmBody_of_not_map hw, hrx,
            Bool.and_self]
          rcases hcase with ⟨rfl, _⟩ | rfl
          · rfl
          · exact AdmBody_of_not_map hw
        cases v
        case map keys g =>
          rw [show Adm (.object b) (.map keys g) = AdmBody b (.map keys g) from rfl,
              show Adm (.record x) (.map keys g)
                = decide (∀ k : {k // k ∈ keys}, Adm x (g k) = true) from rfl,
              Bool.and_comm]
          rcases hcase with ⟨rfl, hnb⟩ | rfl
          · show (false : Bool) = _
            cases hA : AdmBody b (.map keys g) with
            | false => rfl
            | true =>
              cases hR : decide (∀ k : {k // k ∈ keys}, Adm x (g k) = true) with
              | false => rfl
              | true => exact absurd (isBottom_false_of_admRec hok ihf hA hR) hnb
          · show AdmBody (.mk b.fields (fun k => Body.meetRecField b x k) (.codec r))
                  (.map keys g) = _
            rw [AdmBody_map, AdmBody_map]
            simp only [Body.fields_mk, Body.at_mk, Body.rest_mk, hrest]
            rw [valPresentT_meetRec hok, show AdmRest (.codec r) = some (Adm r) from rfl,
                show AdmRest (.codec t) = some (Adm t) from rfl, objAdmV_meetRec ihf iht]
            simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
        all_goals exact hnm _ (fun _ _ hc => Value.noConfusion hc)
      -- **a certified union distributes.** Its admission is the join of its options', the meet
      -- is optionwise, and the bottoms that drop out admit nothing.
      case case11 =>
        obtain ⟨zs, hF, hco, hcz, rfl⟩ :=
          meet_union_left (by assumption) (by assumption) (by assumption) (by assumption)
            (by assumption) h
        simp only [Term.depth] at hle
        rw [Adm_ofOptions hcz, AdmAny_filter_never,
          show Adm (.union _) v = selOptV (AdmSpecs _) v from rfl, selOptV_eq_AdmAny hco]
        exact AdmAny_meet v (forall₂_lift ih (by omega) hF)
      case case12 =>
        obtain ⟨zs, hF, hco, hcz, rfl⟩ :=
          meet_union_right (by assumption) (by assumption) (by assumption) (by assumption)
            (by assumption) (by assumption) h
        simp only [Term.depth] at hle
        rw [Adm_ofOptions hcz, AdmAny_filter_never,
          show Adm (.union _) v = selOptV (AdmSpecs _) v from rfl, selOptV_eq_AdmAny hco,
          Bool.and_comm]
        exact AdmAny_meet v (forall₂_lift ih (by omega) hF)

#print axioms opaq_e_mono

/-- **`Adm` is a homomorphism from the meet to conjunction.** Where two terms have a meet, the
    values it admits are exactly the values both admit. -/
theorem Adm_meet {x y z : Term} (h : Term.meet x y = some z) (v : Value) :
    Adm z v = (Adm x v && Adm y v) :=
  Adm_meet_le (Term.depth x + Term.depth y) x y (Nat.le_refl _) z h v

/-- A unanimous list names one member, so every entry is that member. -/
theorem unanimous_all : ∀ {μs : List (Option Member)} {m : Member},
    unanimous μs = some m → ∀ u ∈ μs, u = some m
  | [], _, h => by simp [unanimous] at h
  | μ :: μs, m, h => by
      simp only [unanimous] at h
      split at h
      next hall =>
        subst h
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · rfl
        · exact of_decide_eq_true (by simpa using (List.all_eq_true.mp hall) u hu')
      next => exact absurd h (by simp)

/-- An option's member is one of the list's. -/
theorem mem_μSynList : ∀ {os : List Term} {o : Term}, o ∈ os → μSyn o ∈ μSynList os
  | [], _, h => by simp at h
  | t :: ts, o, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_μSynList h')

/-- Every option of a union that names a member names that one. -/
theorem μSyn_union_mem {os : List Term} {m : Member} (h : μSyn (.union os) = some m) :
    ∀ o ∈ os, μSyn o = some m := by
  intro o ho
  exact unanimous_all (by simpa only [μSyn] using h) _ (mem_μSynList ho)

/-- …and a list of survivors that names a member has one that does. -/
theorem μSyn_ofOptions_mem {ts : List Term} {m : Member}
    (h : μSyn (Term.ofOptions ts) = some m) : ∃ t ∈ ts, μSyn t = some m := by
  match ts with
  | [] => exact absurd h (by simp [Term.ofOptions, μSyn])
  | [t] => exact ⟨t, by simp, h⟩
  | a :: b :: rest =>
      exact ⟨a, by simp, μSyn_union_mem (os := a :: b :: rest) h a (by simp)⟩



/-- A `Forall₂` relates every right element to some left one. -/
theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ {b}, b ∈ bs → ∃ a ∈ as, R a b
  | _, _, .nil, _, hb => by simp at hb
  | _, _, .cons hr hrest, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact ⟨_, List.mem_cons_self, hr⟩
      · obtain ⟨a, ha, hra⟩ := forall₂_mem_right hrest hb'
        exact ⟨a, List.mem_cons_of_mem _ ha, hra⟩

set_option maxHeartbeats 2000000 in
/-- `meet_writes`, in the form the strong induction on summed depth takes. -/
theorem meet_writes_le : ∀ (n : Nat) (x y : Term), Term.depth x + Term.depth y ≤ n →
    ∀ z, Term.meet x y = some z → ∀ m : Member, μSyn z = some m →
      (∀ mx, μSyn x = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m) := by
  intro n
  induction n with
  | zero =>
      intro x y hle
      have h1 := Term.depth_pos x; have h2 := Term.depth_pos y; omega
  | succ n ih =>
      intro x y hle z h m hz
      cases x, y using Term.meet.fun_cases
      -- a refinement carries the cell, and `μSyn` reads through it on both sides
      case case13 | case15 =>
        simp only [Term.meet] at h
        rw [if_pos (by assumption)] at h
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ih _ _ (by simp only [Term.depth] at hle; omega) w hw m hz
      -- a certified union distributes, and a survivor that names the member is the witness
      case case11 =>
        obtain ⟨zs, hF, _, _, rfl⟩ :=
          meet_union_left (by assumption) (by assumption) (by assumption) (by assumption)
            (by assumption) h
        obtain ⟨w, hw, hwm⟩ := μSyn_ofOptions_mem hz
        obtain ⟨o, ho, hom⟩ := forall₂_mem_right hF (List.mem_of_mem_filter hw)
        simp only [Term.depth] at hle
        have ihw := ih o _ (by have := Term.depth_le_depthL ho; omega) w hom m hwm
        exact ⟨fun mx hmx => ihw.1 mx (μSyn_union_mem hmx o ho), ihw.2⟩
      case case12 =>
        obtain ⟨zs, hF, _, _, rfl⟩ :=
          meet_union_right (by assumption) (by assumption) (by assumption) (by assumption)
            (by assumption) (by assumption) h
        obtain ⟨w, hw, hwm⟩ := μSyn_ofOptions_mem hz
        obtain ⟨o, ho, hom⟩ := forall₂_mem_right hF (List.mem_of_mem_filter hw)
        simp only [Term.depth] at hle
        have ihw := ih o _ (by have := Term.depth_le_depthL ho; omega) w hom m hwm
        exact ⟨ihw.2, fun my hmy => ihw.1 my (μSyn_union_mem hmy o ho)⟩
      -- the ground rows, the literal rows, the set rows and the bottom rows. `μSyn` is a
      -- function of the constructor at each, so no row here can disagree with its factors about
      -- the member; the bottom names none, which is what makes `hz` a hypothesis rather than a
      -- conclusion
      all_goals (try (simp only [Term.meet, Option.some.injEq] at h))
      all_goals (try subst h)
      all_goals (try (simp_all [μSyn, Term.meetLit, Term.meet]))
      all_goals (try (split at h))
      all_goals (try (simp only [Option.some.injEq] at h))
      all_goals (try subst h)
      all_goals (try (simp_all [μSyn]))
      all_goals (try (split at h))
      all_goals (try (simp only [Option.some.injEq] at h))
      all_goals (try subst h)
      all_goals (try (simp_all [μSyn]))
      -- the containers and the objects answer a constructor whose member is fixed, so these
      -- rows never read the recursion: `μSyn` of an `array`, a `tuple`, a `record` and an
      -- `object` is `L`, `L`, `M` and `M` whatever the payload meets to
      case case58 | case59 =>
        obtain ⟨w, _, rfl⟩ := h
        simpa [μSyn] using hz
      case case67 | case68 =>
        obtain ⟨vs, tl, rfl, _, _⟩ := meet_array_tuple h
        simpa [μSyn] using hz
      case case69 | case70 =>
        obtain ⟨vs, tl, rfl, _, _⟩ := meet_tuple_array h
        simpa [μSyn] using hz
      case case71 | case72 | case74 =>
        rcases meet_tuple_tuple h with ⟨vs, tl, rfl, _, _, _⟩ | ⟨rfl, _, _, _⟩
        · simpa [μSyn] using hz
        · exact absurd hz (by simp [μSyn])
      case case75 | case76 =>
        obtain ⟨t, r, _, _, _, hc⟩ := meet_object_record h
        rcases hc with ⟨rfl, _⟩ | rfl
        · exact absurd hz (by simp [μSyn])
        · simpa [μSyn] using hz
      case case77 =>
        obtain ⟨r, _, hc⟩ :=
          meet_object_object (show Term.meet (.object _) (.object _) = some z by
            rw [Term.meet.eq_def]; simpa using h)
        rcases hc with ⟨rfl, _⟩ | ⟨_, _, _, ⟨rfl, _⟩ | rfl⟩
        · exact absurd hz (by simp [μSyn])
        · exact absurd hz (by simp [μSyn])
        · simpa [μSyn] using hz


/-- **Where the meet names a member, any member a factor names is that one.** `μSyn z` is a
    hypothesis and not a conclusion, because the converse fails twice: a bottom names no member,
    so two factors naming different members meet at a term that names none, and a refinement over
    the bottom is not the bottom, so excluding `never` does not repair it. -/
theorem meet_writes {x y z : Term} (h : Term.meet x y = some z) {m : Member}
    (hz : μSyn z = some m) :
    (∀ mx, μSyn x = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m) :=
  meet_writes_le (Term.depth x + Term.depth y) x y (Nat.le_refl _) z h m hz

/-- **The converse is false, and a bottom is why.** Two factors naming different members meet at
    the bottom, which names none, so a theorem concluding `mx = my` from the factors alone fails
    here. -/
example : Term.meet (.literal .boolean true) Term.string = some .never := by simp [Term.meet]

example : μSyn Term.never = none := rfl

/-- …and excluding the bottom does not repair it: a refinement over the bottom is not the bottom,
    and it names no member either. -/
example : Term.meet (.refine .string (.members .string ⟨{"1"}, Finset.singleton_nonempty _⟩))
    .boolean = some (.refine .never (.members .string ⟨{"1"}, Finset.singleton_nonempty _⟩)) := by
  simp [Term.meet, Pred.isData]

example : μSyn (.refine .never (.members .string ⟨{"1"}, Finset.singleton_nonempty _⟩)) = none :=
  rfl


/-! ## The bottom, and what a sub-selection keeps -/

/-- The bottom admits no value. -/
theorem Adm_never (v : Value) : Adm .never v = false := rfl

/-- …and reads no attribute. -/
theorem AdmA_never (a : Attr) : AdmA .never a = false := rfl

/-- `orthAll` from the pairwise form, which is what a sublist preserves. -/
theorem orthAll_of_pairwise : ∀ {ts : List Term},
    List.Pairwise (fun x y => Orth x y = true) ts → orthAll ts = true
  | [], _ => rfl
  | t :: ts, h => by
      cases h with
      | cons hh hrest =>
        simp only [orthAll, Bool.and_eq_true, List.all_eq_true]
        exact ⟨fun u hu => hh u hu, orthAll_of_pairwise hrest⟩

/-- **The certificate survives a sub-selection.** All three conjuncts are pairwise or pointwise,
    so keeping fewer options proves nothing new. (U) is the property that does not survive, and
    it is not one of the three. -/
theorem unionOk_sublist {opts sub : List Term} (hs : sub.Sublist opts)
    (h : unionOk opts = true) : unionOk sub = true := by
  simp only [unionOk, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨⟨orthAll_of_pairwise ((pairwise_of_orthAll h.1.1).sublist hs),
          fun t ht => h.1.2 t (hs.mem ht)⟩, fun t ht => h.2 t (hs.mem ht)⟩

/-- **A value an option admits, the option admits structurally**, where the option is closed.
    The bridge `selOptV_eq_AdmAny` builds inline; an open object is the case it fails at. -/
theorem admitOptV_of_Adm {t : Term} (hcl : t.isOpenObject = false) {v : Value}
    (h : Adm t v = true) : admitOptV (specOf t, Adm t) v = true := by
  cases t with
  | object b =>
    have hr : AdmRest b.rest = none := by
      cases hrest : b.rest with
      | drop => rfl
      | refuse => rfl
      | codec _ => exact absurd hcl (by simp [Term.isOpenObject, hrest, Rest.isOpen])
    cases b with
    | mk fields fld rest =>
      cases v with
      | map keys g => simpa only [admitOptV, specOf] using structural_of_AdmBody hr h
      | _ => exact absurd h (by simp [Adm, AdmBody])
  | _ => exact h



/-! ## The laws, on admission

`Adm_meet` is the homomorphism from the meet to conjunction, so each law below is the
corresponding law of `Bool` read through it. Each is stated on both sides ANSWERING: whether the
meet answers in one order when it answers in the other is a question about the rows, and the
lattice does not need it.
-/

/-- **The meet is commutative on admission.** Stated on both orders answering, because whether
    the meet answers in one order when it answers in the other is a question about the rows and
    not about the lattice. -/
theorem Adm_meet_comm {x y z z' : Term} (h : Term.meet x y = some z)
    (h' : Term.meet y x = some z') (v : Value) : Adm z v = Adm z' v := by
  rw [Adm_meet h, Adm_meet h', Bool.and_comm]

/-- **…and associative on admission**, both bracketings answering. -/
theorem Adm_meet_assoc {x y z xy yz l r : Term}
    (hxy : Term.meet x y = some xy) (hl : Term.meet xy z = some l)
    (hyz : Term.meet y z = some yz) (hr : Term.meet x yz = some r) (v : Value) :
    Adm l v = Adm r v := by
  rw [Adm_meet hl, Adm_meet hxy, Adm_meet hr, Adm_meet hyz, Bool.and_assoc]

/-- **…and idempotent.** -/
theorem Adm_meet_self {x z : Term} (h : Term.meet x x = some z) (v : Value) :
    Adm z v = Adm x v := by
  rw [Adm_meet h, Bool.and_self]

/-- **The bottom absorbs.** -/
theorem Adm_meet_never {x z : Term} (h : Term.meet x .never = some z) (v : Value) :
    Adm z v = false := by
  rw [Adm_meet h, Adm_never, Bool.and_false]

/-- **The meet distributes over a certified union.** `AdmAny` is the join of the options'
    admissions, and `&&` distributes over `||`, so this is the distributive law with the join
    written the way the certificate makes it available. -/
theorem Adm_meet_union {x z : Term} {os : List Term} (hok : unionOk os = true)
    (h : Term.meet x (.union os) = some z) (v : Value) :
    Adm z v = (Adm x v && AdmAny os v) := by
  rw [Adm_meet h, show Adm (.union os) v = selOptV (AdmSpecs os) v from rfl,
    selOptV_eq_AdmAny hok]

/-- …and the distribution, written so a reader sees it: the meet of a term with a join is the
    join of the meets, one option at a time. -/
theorem Adm_meet_union_distrib {x z o : Term} {os : List Term} (hok : unionOk (o :: os) = true)
    (h : Term.meet x (.union (o :: os)) = some z) (v : Value) :
    Adm z v = ((Adm x v && Adm o v) || (Adm x v && AdmAny os v)) := by
  rw [Adm_meet_union hok h, AdmAny_cons]
  cases Adm x v <;> cases Adm o v <;> cases AdmAny os v <;> rfl

end Calculus
