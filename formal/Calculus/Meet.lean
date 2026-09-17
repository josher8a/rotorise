import Calculus.HeldSet
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
bottom, and `BOOL` and `S` never have to agree. The bottom is the whole of the reason, and it is
enough: a bottom names no member, so no pair whose meet is one can conclude anything about the
factors. The meet normalises a refinement over the bottom to the bottom, so that shape no longer
gives a second witness.

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

**A shared name's two fields meet at the stronger mark where the two marks read alike, and an
unshared one parts the halves.** A mark says whether the name must be present when the object is
written and when it is read, and those two bits are not the same bit: `fallback` forces the write
and not the read, because its stand-in answers a read that finds no name. Intersecting conjoins
each bit, so where the marks read alike a shared name meets at the stronger of the two,
`optional < fallback < req`, which is `Field.meet`. **`optional` against a `fallback` reads an
absent name two ways and so refuses**: both admit a map that omits the name, and there one reads a
map without the name and the other a map carrying the stand-in, so the pair shares attributes no
term states. A name one body declares and the other does not has no second mark to join: under a
closed rest a `req` name makes the object the bottom, because it must be written and the partner
refuses it, and a `fallback` name refuses outright, because the write side is empty there and the
read side is not.

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

/-- A held set of the option judgements is some option's own. -/
theorem mem_typed_of_mem : ∀ {os : List Term} {Ts μs}, TypedListμ os Ts μs →
    ∀ T ∈ Ts, ∃ t ∈ os, ∃ μ, Typed t T μ
  | _, _, _, .nil, _, hT => nomatch hT
  | _, _, _, .cons hty hs, T, hT => by
    rcases List.mem_cons.mp hT with rfl | hT'
    · exact ⟨_, List.mem_cons_self, _, hty⟩
    · obtain ⟨t', ht', μ', hty'⟩ := mem_typed_of_mem hs T hT'
      exact ⟨t', List.mem_cons_of_mem _ ht', μ', hty'⟩

/-- The certificate's pairwise `Orth`, carried to the held sets option by option. -/
theorem unionOk_pairwise_held : ∀ {os : List Term} {Ts μs}, TypedListμ os Ts μs →
    List.Pairwise (fun x y => Orth x y = true) os →
    (∀ t ∈ os, t.isOpenObject = false) → Ts.Pairwise HDisj
  | _, _, _, .nil, _, _ => .nil
  | _, _, _, .cons hty hs, ho, hc => by
    obtain ⟨hohead, hotail⟩ := List.pairwise_cons.mp ho
    refine .cons ?_
      (unionOk_pairwise_held hs hotail (fun t ht => hc t (List.mem_cons_of_mem _ ht)))
    intro T hT
    obtain ⟨t', ht', μ', hty'⟩ := mem_typed_of_mem hs T hT
    exact separates_held_of_orth (hc _ List.mem_cons_self)
      (hc _ (List.mem_cons_of_mem _ ht')) (hohead t' ht') hty hty'

/-- **A certified union satisfies (D).** The certificate is what the judgement's side
    condition needs, and it needs no `denote`: the held sets are the judgement's own, and
    disjointness is the second disjunct. This is the form the meet's union row takes. -/
theorem dincomp_of_unionOk {os : List Term} {Ts μs} (hc : unionOk os = true)
    (h : TypedListμ os Ts μs) : DIncomp Ts := by
  obtain ⟨hc1, _⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨horth, hopen⟩ := Bool.and_eq_true_iff.mp hc1
  refine dincomp_of_disjoint (unionOk_pairwise_held h (pairwise_of_orthAll horth) ?_)
  intro t ht
  have := List.all_eq_true.mp hopen t ht
  simpa using this

/-- A union of what survived a distribution: nothing is the bottom, one survivor is itself, and
    the rest are a union again. -/
def Term.ofOptions : List Term → Term
  | [] => .never
  | [t] => t
  | ts => .union ts

/-- …and the answer the meet gives at a union: the survivors, where both the options met and
    the survivors carry the certificate. The meet is the lattice's meet, and an uncertified
    union is not in the lattice, so the pair has no meet to state. Both sides are tested and
    not one: `objRec` answers an OPEN object, so a certified list of options can meet to an
    uncertified one. -/
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
    `drop` rest refuses it on the write side and skips it on the read side. So `objObj` reads the
    rests first, and puts the pair to `Body.dropFits` before it consults this test. -/
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

/-- A list of answers, as one answer: `none` where any cell refused. Outside the recursion, so
    the rows below reach a list through `List.attach` and a `map` rather than through a mutual
    companion — which is what makes every recursive call strictly shallower in one measure. -/
def allSome {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some x :: rest => (allSome rest).map (x :: ·)

/-- **A refinement over the bottom is the bottom.** The bottom bubbles up through a slot that
    must hold a value, and a refinement's inner term is one: `refine` narrows what the inner term
    holds, so it holds nothing where the inner term does. Called from the right-hand side of the
    meet's refinement rows, so every refinement the meet builds is normal. -/
def Term.refineOf (z : Term) (p : Pred) : Term :=
  if z.isNever then .never else .refine z p

/-- **A list with a declared position at the bottom is the bottom.** Every value the list
    admits fills each declared position, so one position holding nothing empties the list.
    The SPREAD is not such a slot: a value of exactly the declared length omits every spread
    position, so a spread at the bottom reads "exactly the declared positions" rather than
    "nothing". The prefix and the suffix are both declared; the spread is not. -/
def Term.listOf (pre : List Term) (sp : Option Term) (suf : List Term) : Term :=
  if pre.any Term.isNever || suf.any Term.isNever then .never else .list pre sp suf

/-- The suffix-free case, under the name the tuple rows use. -/
def Term.tupleOf (ts : List Term) (tail : Option Term) : Term :=
  Term.listOf ts tail []

/-! ## The meet -/

mutual

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


end

/-! ## The meet, structurally

Every row keeps the left operand on the left. -/

def mapF (f : Term → Option Term) : List Term → List (Option Term)
  | [] => [] | t :: ts => f t :: mapF f ts

def zipF : List (Term → Option Term) → List Term → List (Option Term)
  | [], _ => [] | _, [] => []
  | f :: fs, u :: us => f u :: zipF fs us

mutual
/-- **Every row that reads the right operand alone, written once.** The bottom, the four whose
    admission is a function, a refinement and a certified union answer the same way whatever the
    left operand is, so they are stated here rather than restated per left constructor. `fam`
    carries the left operand, already applied. -/
def meetSRight (fam : Term → Option Term) : Term → Option Term
  | .never => some .never
  | .held _ _ _ | .legacy _ _ | .custom _ _ | .lazy _ => none
  | .refine y p => if p.isData then (meetSRight fam y).map (fun z => Term.refineOf z p) else none
  | .union os => (allSome (meetSRightL fam os)).bind
      (fun zs => Term.ofOptionsGuarded os (zs.filter (fun z => !z.isNever)))
  | y => fam y
def meetSRightL (fam : Term → Option Term) : List Term → List (Option Term)
  | [] => [] | y :: ys => meetSRight fam y :: meetSRightL fam ys
end

/-! ### The families: one per left constructor, flat and non-recursive. -/
def famString : Term → Option Term
  | .string => some .string
  | .decimal => none
  | .literal k v => match k, v with
      | .string, v => some (.literal .string v) | .decimal, _ => none | _, _ => some .never
  | .opaq _ => some .string
  | _ => some .never

def famNumber : Term → Option Term
  | .number => some .number
  | .decimal => none
  | .literal k v => match k, v with
      | .number, v => some (.literal .number v) | .decimal, _ => none | _, _ => some .never
  | .opaq l => if l then some .number else some .never
  | _ => some .never

def famDecimal : Term → Option Term
  | .decimal => some .decimal
  | .string => none
  | .number => none
  | .literal k v => match k, v with
      | .decimal, v => some (.literal .decimal v) | .string, _ => none | .number, _ => none
      | _, _ => some .never
  | .opaq _ => none
  | _ => some .never

def famBoolean : Term → Option Term
  | .boolean => some .boolean
  | .literal k v => if k = .boolean then some (.literal k v) else some .never
  | .opaq _ => some .boolean
  | _ => some .never

def famBinary : Term → Option Term
  | .binary => some .binary
  | .literal k v => if k = .binary then some (.literal k v) else some .never
  | .opaq _ => some .binary
  | _ => some .never

def famNull : Term → Option Term
  | .null => some .null
  | .literal k v => if k = .null then some (.literal k v) else some .never
  | .opaq _ => some .null
  | _ => some .never

def famLit (k : GroundKind) (v : k.Carrier) : Term → Option Term
  | .string => match k, v with
      | .string, v => some (.literal .string v) | .decimal, _ => none | _, _ => some .never
  | .number => match k, v with
      | .number, v => some (.literal .number v) | .decimal, _ => none | _, _ => some .never
  | .decimal => match k, v with
      | .decimal, v => some (.literal .decimal v) | .string, _ => none | .number, _ => none
      | _, _ => some .never
  | .boolean => if k = .boolean then some (.literal k v) else some .never
  | .binary => if k = .binary then some (.literal k v) else some .never
  | .null => if k = .null then some (.literal k v) else some .never
  | .literal k' v' => Term.meetLit k v k' v'
  | .opaq _ => none
  | _ => some .never

def famSet (b : SetBase) : Term → Option Term
  | .set b' => match b, b' with
      | .string, .decimal | .decimal, .string | .number, .decimal | .decimal, .number => none
      | _, _ => if b = b' then some (.set b) else some .never
  | .opaq _ => none
  | _ => some .never

def famOpaq (l : Bool) : Term → Option Term
  | .string => some .string
  | .boolean => some .boolean
  | .binary => some .binary
  | .null => some .null
  | .number => if l then some .number else some .never
  | .opaq l' => some (.opaq (l && l'))
  | _ => none

def applyAt : List (Term → Option Term) → Term → List (Option Term)
  | [], _ => [] | f :: fs, y => f y :: applyAt fs y

/-- **The row a `list` shape assigns to `n` positions**: the prefix, the spread as often as
    the middle needs, then the suffix. `none` is the length the shape refuses. One
    definition serves both operands, because the left operand's positions are partially
    applied meets and the right operand's are terms, and the shape does not care which.
    Mirrors `slotsL` one level up. -/
def rowOfG {α : Type} (pre : List α) (sp : Option α) (suf : List α) (n : Nat) :
    Option (List α) :=
  match sp with
  | some c =>
      if n < pre.length + suf.length then none
      else some (pre ++ List.replicate (n - pre.length - suf.length) c ++ suf)
  | none => if n = pre.length + suf.length then some (pre ++ suf) else none

/-- The spread row, split at the suffix. Stated over an explicit split so no rewrite has to
    reach inside a length. -/
theorem zipP_row_split (pre suf : List VP) (c : VP) (A B : List Value)
    (hB : B.length = suf.length) (hA : pre.length ≤ A.length) :
    (zipP (pre ++ List.replicate (A.length - pre.length) c) A && zipP suf B)
      = zipP (pre ++ List.replicate ((A ++ B).length - pre.length - suf.length) c ++ suf)
          (A ++ B) := by
  have hcount : (A ++ B).length - pre.length - suf.length = A.length - pre.length := by
    simp only [List.length_append, hB]; omega
  rw [hcount, zipP_append _ _ _ _
      (by simp only [List.length_append, List.length_replicate]; omega)]

/-- **`alignPL` is its row, applied position for position.** This is `align_eq_zip` one level
    down, and it is what lets the meet reason about two shapes by reasoning about their rows
    at one length: the admission of a `list` at a value of length `n` is the admission of the
    row `rowOfG` assigns to `n`, position by position. -/
theorem alignPL_eq_rowOfG (pre : List VP) (sp : Option VP) (suf : List VP) (ws : List Value) :
    alignPL pre sp suf ws
      = match rowOfG pre sp suf ws.length with
        | none => false
        | some row => zipP row ws := by
  have htl : (ws.take (ws.length - suf.length)).length = ws.length - suf.length := by
    simp only [List.length_take]; omega
  unfold alignPL
  rcases Nat.lt_or_ge ws.length (pre.length + suf.length) with hlt | hge
  · have hrow : rowOfG pre sp suf ws.length = none := by
      cases sp with
      | none => simp only [rowOfG]; rw [if_neg (by omega)]
      | some c => simp only [rowOfG]; rw [if_pos (by omega)]
    rw [hrow]
    rcases Nat.lt_or_ge ws.length suf.length with hs | hs
    · rw [zipP_false_of_length_ne _ _ (by simp only [List.length_drop]; omega), Bool.and_false]
    · rw [alignP_short _ _ _ (by omega), Bool.false_and]
  · have hdl : (ws.drop (ws.length - suf.length)).length = suf.length := by
      simp only [List.length_drop]; omega
    have hAB : ws.take (ws.length - suf.length) ++ ws.drop (ws.length - suf.length) = ws :=
      List.take_append_drop _ _
    cases sp with
    | none =>
        rw [alignP_none_eq_zipP]
        simp only [rowOfG]
        rcases Nat.eq_or_lt_of_le hge with heq | hlt2
        · rw [if_pos heq.symm]
          show _ = zipP (pre ++ suf) ws
          have hz := (zipP_append pre suf (ws.take (ws.length - suf.length))
            (ws.drop (ws.length - suf.length)) (by omega)).symm
          rw [hAB] at hz
          exact hz
        · rw [if_neg (by omega)]
          show _ = false
          rw [zipP_false_of_length_ne _ _ (by omega), Bool.false_and]
    | some c =>
        rw [alignP_some_eq_zipP _ _ _ (by omega)]
        simp only [rowOfG]
        rw [if_neg (by omega)]
        show _ = zipP (pre ++ List.replicate (ws.length - pre.length - suf.length) c ++ suf) ws
        have hz := zipP_row_split pre suf c (ws.take (ws.length - suf.length))
          (ws.drop (ws.length - suf.length)) hdl (by omega)
        rw [hAB] at hz
        exact hz

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
def listMeetRow (fpre : List (Term → Option Term)) (fsp : Option (Term → Option Term))
    (fsuf : List (Term → Option Term)) (pre₂ : List Term) (sp₂ : Option Term)
    (suf₂ : List Term) : Option Term :=
  match fsp, sp₂ with
  | some f, some c =>
      if dominates fpre.length fsuf.length pre₂.length suf₂.length then
        match f c with
        | none => none
        | some sp =>
          let P := max fpre.length pre₂.length
          let S := max fsuf.length suf₂.length
          match rowOfG fpre (some f) fsuf (P + S), rowOfG pre₂ (some c) suf₂ (P + S) with
          | some fs, some us =>
              (allSome (zipF fs us)).map fun row =>
                Term.listOf (row.take P) (some sp) (row.drop P)
          | _, _ => some .never
      else none
  | _, _ =>
      let n := match fsp with
        | none => fpre.length + fsuf.length
        | some _ => pre₂.length + suf₂.length
      match rowOfG fpre fsp fsuf n, rowOfG pre₂ sp₂ suf₂ n with
      | some fs, some us =>
          (allSome (zipF fs us)).map fun row => Term.listOf row none []
      | _, _ => some .never

/-- The family of the one positional container. Replaces `famArr` and `famTup`, which
    answered on shapes that are now one term. -/
def famList (fpre : List (Term → Option Term)) (fsp : Option (Term → Option Term))
    (fsuf : List (Term → Option Term)) : Term → Option Term
  | .list pre₂ sp₂ suf₂ => listMeetRow fpre fsp fsuf pre₂ sp₂ suf₂
  | .opaq _ => none
  | _ => some .never

def famTup (fs : List (Term → Option Term)) (ftail : Option (Term → Option Term)) :
    Term → Option Term
  | .array y =>
      match allSome (applyAt fs y),
            (match ftail with | none => some none | some ft => (ft y).map some) with
      | some vs, some tl => some (Term.tupleOf vs tl)
      | _, _ => none
  | .tuple us tail' =>
      if fs.length = us.length then
        match allSome (zipF fs us),
              (match ftail, tail' with
               | none, none => some none
               | some ft, some u => (ft u).map some
               | _, _ => none) with
        | some vs, some tl => some (Term.tupleOf vs tl)
        | _, _ => none
      else if ftail.isNone && tail'.isNone then some .never
      else none
  | .opaq _ => none
  | _ => some .never

/-- A field met with one term, the field's mark kept, with the TERM on the left. `Field.meetT`
    is the same cell with the field on the left; the record∧object row needs this one. -/
def fieldMeetT (f : Term → Option Term) : Field → Option Field
  | .req t => (f t).map .req
  | .optional t => (f t).map .optional
  | .fallback _ _ => none

/-- **A record against an object, with the RECORD as the left operand.** `f` is the meet at the
    record's value term, so each declared field answers `meet x t` and not `meet t x`. -/
def recObj (f : Term → Option Term) (b : Body) : Option Term :=
  match b.rest with
  | .codec t =>
      if decide (∀ k : {k // k ∈ b.fields}, (fieldMeetT f (b.at k)).isSome = true) then
        match f t with
        | some r =>
            if decide (∀ k : {k // k ∈ b.fields},
                Field.isBottom ((fieldMeetT f (b.at k)).getD (.optional .never)) = false) then
              some (.object (.mk b.fields
                (fun k => (fieldMeetT f (b.at k)).getD (.optional .never)) (.codec r)))
            else some .never
        | none => none
      else none
  | _ => none

def famRec (f : Term → Option Term) : Term → Option Term
  | .record y => (f y).map .record
  | .object b => recObj f b
  | .opaq _ => none
  | _ => some .never

/-- **An object against a record, with the OBJECT as the left operand.** `gt k` is the meet at
    the left body's field `k`, and `frest` the meet at its rest codec. -/
def objRec (fs : Finset Name) (gt : {k // k ∈ fs} → Term → Option Field)
    (frest : Option (Term → Option Term)) (x : Term) : Option Term :=
  match frest with
  | some fr =>
      if decide (∀ k : {k // k ∈ fs}, (gt k x).isSome = true) then
        match fr x with
        | some r =>
            if decide (∀ k : {k // k ∈ fs},
                Field.isBottom ((gt k x).getD (.optional .never)) = false) then
              some (.object (.mk fs (fun k => (gt k x).getD (.optional .never)) (.codec r)))
            else some .never
        | none => none
      else none
  | none => none

/-- **Two objects.** The guards read the two bodies whole; only the shared names recurse, through
    `g` at the left body's field. -/
def objObj (a : Body) (g : {k // k ∈ a.fields} → Field → Option Field) (b : Body) : Option Term :=
  match Rest.merge a.rest b.rest with
  | some r =>
      if Body.fbShared a b && Body.fbShared b a then
        if Body.dropFits a b && Body.dropFits b a then
          if Body.reqShared a b && Body.reqShared b a then
            if decide (∀ k : {k // k ∈ Body.shared a b},
                (g ⟨k.1, Body.mem_shared_left k.2⟩
                   (b.at ⟨k.1, Body.mem_shared_right k.2⟩)).isSome = true) then
              if decide (∀ k : {k // k ∈ Body.shared a b},
                  Field.isBottom ((g ⟨k.1, Body.mem_shared_left k.2⟩
                    (b.at ⟨k.1, Body.mem_shared_right k.2⟩)).getD (.optional .never)) = false) then
                some (.object (.mk (Body.shared a b)
                  (fun k => (g ⟨k.1, Body.mem_shared_left k.2⟩
                    (b.at ⟨k.1, Body.mem_shared_right k.2⟩)).getD (.optional .never)) r))
              else some .never
            else none
          else some .never
        else none
      else none
  | none => none

def famObj (a : Body) (g : {k // k ∈ a.fields} → Field → Option Field)
    (gt : {k // k ∈ a.fields} → Term → Option Field)
    (frest : Option (Term → Option Term)) : Term → Option Term
  | .object b => objObj a g b
  | .record x => objRec a.fields gt frest x
  | .opaq _ => none
  | _ => some .never

mutual
/-- **The intersection of two admissions, as a term**, by structural recursion on the left
    operand. Every row keeps the left operand on the left. -/
def Term.meet : Term → Term → Option Term
  | .never, _ => some .never
  | .held _ _ _, .never | .legacy _ _, .never | .custom _ _, .never | .lazy _, .never =>
      some .never
  | .held _ _ _, _ | .legacy _ _, _ | .custom _ _, _ | .lazy _, _ => none
  | .refine _ _, .never => some .never
  | .refine x p, y => if p.isData then (Term.meet x y).map (fun z => Term.refineOf z p) else none
  | .union _, .never => some .never
  | .union os, y => (allSome (Term.meetSL os y)).bind
      (fun zs => Term.ofOptionsGuarded os (zs.filter (fun z => !z.isNever)))
  | .string, y => meetSRight famString y
  | .number, y => meetSRight famNumber y
  | .decimal, y => meetSRight famDecimal y
  | .boolean, y => meetSRight famBoolean y
  | .binary, y => meetSRight famBinary y
  | .null, y => meetSRight famNull y
  | .literal k v, y => meetSRight (famLit k v) y
  | .set b, y => meetSRight (famSet b) y
  | .opaq l, y => meetSRight (famOpaq l) y
  | .record x, y => meetSRight (famRec (Term.meet x)) y
  | .list pre sp suf, y =>
      meetSRight (famList (Term.meetSTs pre)
        (match sp with | none => none | some t => some (Term.meet t))
        (Term.meetSTs suf)) y
  | .object (.mk fs f r), y =>
      meetSRight (famObj (.mk fs f r) (fun k => Field.meet (f k)) (fun k => Field.meetT (f k))
        (match r with | .codec t => some (Term.meet t) | _ => none)) y
termination_by structural x _ => x
def Term.meetSL : List Term → Term → List (Option Term)
  | [], _ => [] | x :: xs, y => Term.meet x y :: Term.meetSL xs y
termination_by structural xs _ => xs
def Term.meetSTs : List Term → List (Term → Option Term)
  | [] => [] | t :: ts => Term.meet t :: Term.meetSTs ts
termination_by structural ts => ts
def Field.meet : Field → Field → Option Field
  | .req x, .req y => (Term.meet x y).map .req
  | .req x, .optional y => (Term.meet x y).map .req
  | .optional x, .req y => (Term.meet x y).map .req
  | .req x, .fallback y _ => (Term.meet x y).map .req
  | .fallback x _, .req y => (Term.meet x y).map .req
  | .optional x, .optional y => (Term.meet x y).map .optional
  | .optional _, .fallback _ _ => none
  | .fallback _ _, .optional _ => none
  | .fallback _ _, .fallback _ _ => none
termination_by structural f _ => f
def Field.meetT : Field → Term → Option Field
  | .req x, y => (Term.meet x y).map .req
  | .optional x, y => (Term.meet x y).map .optional
  | .fallback _ _, _ => none
termination_by structural f _ => f
end

/-- **`optional` against a `fallback` refuses, in both orientations.** They agree on presence and
    part on what they read at a map omitting the name, so the pair shares attributes it reads two
    ways and no mark states that. `docs/defects.md` carries the pair. -/
example : Field.meet (.optional .string) (.fallback .string (.str "d")) = none := by rfl

example : Field.meet (.fallback .string (.str "d")) (.optional .string) = none := by rfl

/-- **Two `fallback` fields refuse, and that is a defect and not a rule.** They meet at the same
    mark whenever their stand-ins agree, and `Value` has no `DecidableEq` in this tree. -/
example : Field.meet (.fallback .string (.str "d")) (.fallback .string (.str "d")) = none := by rfl

/-! ## What the rows answer

Worked pairs, one per class, checked by the equation compiler rather than described. The first is
the example the meet exists for: an array admits every length and a tuple pins one, so the meet is
the tuple. -/

example : Term.meet (.array .string) (.tuple [.literal .string "a"] none)
    = some (.tuple [.literal .string "a"] none) := by rfl

/-- Two value kinds that never meet. -/
example : Term.meet .string .number = some .never := by rfl

/-- A literal against its own base is the literal: the finer of the two. -/
example : Term.meet (.literal .string "a") .string = some (.literal .string "a") := by rfl

/-- …and against another value of the same base, nothing. -/
example : Term.meet (.literal .string "a") (.literal .string "b") = some .never := by rfl

/-- `string` and `decimal` admit the same text and store it at different members, so the pair has
    no meet rather than an empty one. -/
example : Term.meet .string .decimal = none := by rfl

/-- **The same refusal reaches a literal at either base**, because a `decimal` literal's values
    are `.str`. These four rows answered the bottom, which claims the pair shares no value while
    it shares one, and the two literals below are the same mistake one level further in. -/
example : Term.meet (.literal .decimal ⟨"1", by decide⟩) .string = none := by rfl

example : Term.meet (.literal .string "1") .decimal = none := by rfl

example : Term.meet (.literal .string "1") (.literal .decimal ⟨"1", by decide⟩) = none := by rfl

/-- The value the refusal is about: both terms admit it, and they store it at `S` and at `N`. -/
example : Adm (.literal .decimal ⟨"1", by decide⟩) (.str "1") = true := by
  simp [Adm, AdmLit, inL]
  decide

example : Adm Term.string (.str "1") = true := by simp [Adm]

/-- A literal at a base that shares nothing with the partner is still the bottom. -/
example : Term.meet (.literal .string "1") .boolean = some .never := by rfl

/-- A refinement carries the cell, and so does a container: `none` survives `.map`. -/
example : Term.meet (.refine .string (.members .string ⟨{"1"}, Finset.singleton_nonempty _⟩))
    .decimal = none := by rfl

example : Term.meet (.array .string) (.array .decimal) = none := by rfl

/-- **`number` and `decimal` refuse too, and for the other half of the rule.** They write
    different value kinds, so the bottom is right about what they store together — nothing. They
    read the same member `N`, so the bottom is wrong about what they read together: a stored
    numeral the host re-reads is an attribute both admit. A pair that shares an attribute has no
    meet, for the reason a pair that shares a value has none. -/
example : Term.meet .number .decimal = none := by rfl

example : Term.meet (.set .number) (.set .decimal) = none := by rfl

/-- The attribute the refusal is about: both terms read it, and the bottom reads nothing. -/
example (x : WFNumeral) (h : Numeral.Stored x.1 = true) : AdmA Term.decimal (.n x) = true := h

/-- **The null point needs no row of its own.** A null point is the null term joined by a union,
    so the union rows distribute over it and the ground rows answer each cell. This is the pair
    that had a row and got it wrong: the wrapper this replaced dropped the point at every
    partner but another wrapper and a `null`, and `opaq` holds the point. -/
example : Term.meet (.union [.string, .null]) (.opaq true) = some (.union [.string, .null]) := by rfl

/-- …and against the null term alone the string cell is the bottom, so one option survives. -/
example : Term.meet (.union [.string, .null]) .null = some .null := by rfl

/-- …and the same refusal one container out. A set of stored numerals satisfies both bases, so
    the pair shares values and has no meet. -/
example : Term.meet (.set .string) (.set .decimal) = none := by rfl

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
      = none := by rfl

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
example : Field.meet (.req .string) (.req .string) = some (.req .string) := by rfl

example : Field.meet (.req .string) (.optional .string) = some (.req .string) := by rfl

example : Field.meet (.optional .string) (.req .string) = some (.req .string) := by rfl

example : Field.meet (.req .string) (.fallback .string (.str "d")) = some (.req .string) := by rfl

example : Field.meet (.fallback .string (.str "d")) (.req .string) = some (.req .string) := by rfl

/-- `optional` against `optional` forces neither half… -/
example : Field.meet (.optional .string) (.optional .string) = some (.optional .string) := by rfl

/-- …and against a `fallback` it refuses, at every pair of terms, because the two read an absent
    name apart. -/
example : Field.meet (.optional .string) (.fallback .string (.str "d")) = none := by
  simp [Field.meet]

example : Field.meet (.fallback .string (.str "d")) (.optional .string) = none := by
  simp [Field.meet]

/-- A `req` field over the bottom is still the bottom and not a refusal: both halves force the
    name present, so both agree that nothing satisfies the object. -/
example : Field.meet (.req .string) (.req .boolean) = some (.req .never) := by rfl

/-- Two stand-ins refuse, even these two, which are equal. `Value` has no `DecidableEq` here, so
    the row cannot ask; `docs/defects.md` carries it. -/
example : Field.meet (.fallback .string (.str "d")) (.fallback .string (.str "d")) = none := by
  simp [Field.meet]

/-- An unshared `req` name under a closed rest is the bottom: it must be written and the partner
    refuses it, and on the read side the partner refuses it too. -/
example : Term.meet
    (.object (.mk {"x"} (fun _ => .req .string) .refuse))
    (.object (.mk ∅ (fun _ => .optional .never) .refuse)) = some .never := by rfl

/-- **…and an unshared `fallback` name refuses**, because the two halves part there. The write
    side must write the name and the partner refuses it, so nothing is written; the read side
    needs no name at all and both factors read the map that omits it. -/
example : Term.meet
    (.object (.mk {"x"} (fun _ => .fallback .string (.str "d")) .refuse))
    (.object (.mk ∅ (fun _ => .optional .never) .refuse)) = none := by rfl

/-- **`drop` skips an undeclared name on the read side, so the declared set bounds the read from
    below.** These two bodies declare one name each, and the intersection declares neither. On the
    write side each factor refuses a map carrying the other's name and the intersection refuses it
    too, so the write side is right. On the read side each factor skips the name it does not
    declare, so each reads `{x := true}` — and the intersection, declaring nothing, reads every
    map, where the left factor refuses that one. No object states both halves and the pair
    refuses. -/
example : Term.meet
    (.object (.mk {"x"} (fun _ => .optional .string) .drop))
    (.object (.mk {"y"} (fun _ => .optional .string) .drop)) = none := by rfl

/-- The same pair at `req`, where the answer was the bottom: the required-name test reads a name
    the other body does not declare as a refusal, and under `drop` the other body skips it. -/
example : Term.meet
    (.object (.mk {"x"} (fun _ => .req .string) .drop))
    (.object (.mk {"y"} (fun _ => .req .string) .drop)) = none := by rfl

/-- …and the mirror, where the meet refuses what both factors read. The `drop` factor skips `y`
    and the `refuse` factor reads it through its own field, so both admit `{y := "1"}`; the
    intersection declares nothing and the merged `refuse` refuses it. -/
example : Term.meet
    (.object (.mk ∅ (fun _ => .optional .never) .drop))
    (.object (.mk {"y"} (fun _ => .optional .string) .refuse)) = none := by rfl

/-- Two `refuse` factors keep the intersection. `refuse` reads an undeclared name the way it
    writes one, so the declared set is an upper bound on both halves and the two agree. -/
example : Term.meet
    (.object (.mk {"x"} (fun _ => .optional .string) .refuse))
    (.object (.mk {"y"} (fun _ => .optional .string) .refuse))
    = some (.object (.mk (Body.shared (.mk {"x"} (fun _ => .optional .string) .refuse)
                                      (.mk {"y"} (fun _ => .optional .string) .refuse))
        (fun k => (Field.meet
            ((Body.mk {"x"} (fun _ => .optional .string) .refuse).at
              ⟨k.1, Body.mem_shared_left k.2⟩)
            ((Body.mk {"y"} (fun _ => .optional .string) .refuse).at
              ⟨k.1, Body.mem_shared_right k.2⟩)).getD (.optional .never))
        .refuse)) := by rfl

/-- **An uncertified union has no meet, and there are two ways to be uncertified.** These two
    options declare the same name with the same mark and no literal, so nothing tells them
    apart: both admit a map carrying `a` *structurally*, `selOptV` finds two admitters and
    refuses, and the union admits less than the join of its options. -/
example : unionOk [.object (.mk {"a"} (fun _ => .req .string) .refuse),
    .object (.mk {"a"} (fun _ => .req .boolean) .refuse)] = false := by
  simp [unionOk, orthAll, Orth, Orth1, OrthM, OrthS, OrthL, occV, occA, occOnly, Slot.all,
    Member.all, reqNotDeclared, Body.spec, altsOfField, specOf, litDisjAt, altsDisj, MapOf.at,
    Finset.mem_singleton]

/-! ### The bottom bubbles up through a required slot

A slot that must hold a value passes the bottom up; a slot that may be empty stops it. So the
meet's output is normal, and `Term.isNever` is the whole of the union guard's filter again. -/

/-- A tuple's declared position is such a slot… -/
example : Term.meet (.tuple [.string] none) (.tuple [.boolean] none) = some .never := by rfl

/-- …an `array`'s element is not, because an array over the bottom holds the empty list. -/
example : Term.meet (.array .string) (.array .boolean) = some (.array .never) := by rfl

/-- A refinement's inner term is such a slot, and this is the pair that made a union of empty
    options: each option met the partner at a refinement over the bottom, which the filter could
    not see. Both options now answer the bottom and the filter drops them. -/
example : Term.meet
    (.refine .string (.members .string ⟨{"1"}, Finset.singleton_nonempty _⟩)) .null
      = some .never := by rfl

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

example : Term.meet (.opaq true) .string = some .string := by rfl

example : ¬ (μSyn Term.string = μSyn (Term.opaq true)) := by simp [μSyn]

/-! ## The homomorphism

`Adm` carries the meet to conjunction. The proof mirrors the definition's three layers. One
shared lemma covers `meetSRight`, parametric in the family. One flat lemma covers each family.
The outer statement recurses structurally on the left operand. The lemmas each class needs are
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


/-- The rows of a term list are as many as the terms. -/
theorem AdmList_length (ts : List Term) : (AdmList ts).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ihx => simp only [AdmList, List.length_cons, ihx]

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

/-- A name is shared exactly when both bodies declare it. -/
theorem mem_shared_iff {a b : Body} {k : Name} :
    k ∈ Body.shared a b ↔ k ∈ a.fields ∧ k ∈ b.fields := Finset.mem_filter

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


/-- A declared name that must be present is present, read off the admission. -/
theorem mem_keys_of_isReq {c : Body} {keys : Finset Name}
    (hv : valPresentT c.fields c.at keys = true) {k : Name} (hc : k ∈ c.fields)
    (hreq : Field.isReq (c.at ⟨k, hc⟩) = true) : k ∈ keys := by
  rw [valPresentT_req] at hv
  exact of_decide_eq_true hv ⟨k, hc⟩ hreq

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

/-- Normalising a refinement keeps the member it stores, because the bottom stores none and so
    does the refinement over it. -/
theorem μSyn_refineOf (z : Term) (p : Pred) : μSyn (Term.refineOf z p) = μSyn z := by
  unfold Term.refineOf
  split
  next hz => rw [show z = Term.never from eq_never_of_isNever hz]
  next => rfl

/-- …and a normalised list is a list or the bottom. -/
theorem listOf_cases (pre : List Term) (sp : Option Term) (suf : List Term) :
    Term.listOf pre sp suf = .never ∨ Term.listOf pre sp suf = .list pre sp suf := by
  unfold Term.listOf; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The suffix-free case, under the name the tuple rows use. -/
theorem tupleOf_cases (ts : List Term) (tail : Option Term) :
    Term.tupleOf ts tail = .never ∨ Term.tupleOf ts tail = .tuple ts tail :=
  listOf_cases ts tail []

/-- A declared position that holds nothing empties the tuple: every list the tuple admits fills
    each declared position. -/
theorem alignP_never_false : ∀ {ts : List Term} {tail : Option Term} {ws : List Value},
    ts.any Term.isNever = true → alignP (AdmList ts) (AdmOptT tail) ws = false := by
  intro ts
  induction ts with
  | nil => intro _ _ h; simp at h
  | cons t ts' ih =>
    intro tail ws h
    cases ws with
    | nil => rfl
    | cons w ws' =>
      simp only [List.any_cons, Bool.or_eq_true] at h
      simp only [AdmList, alignP]
      rcases h with ht | hrest
      · rw [show t = Term.never from eq_never_of_isNever ht, show Adm .never _ = false from rfl, Bool.false_and]
      · rw [ih (tail := tail) (ws := ws') hrest, Bool.and_false]

/-- A declared SUFFIX position that holds nothing empties the list, for the same reason:
    every value the list admits fills each suffix position too. -/
theorem zipP_never_false : ∀ {suf : List Term} {ws : List Value},
    suf.any Term.isNever = true → zipP (AdmList suf) ws = false := by
  intro suf
  induction suf with
  | nil => intro _ h; simp at h
  | cons t ts' ih =>
    intro ws h
    cases ws with
    | nil => rfl
    | cons w ws' =>
      simp only [List.any_cons, Bool.or_eq_true] at h
      simp only [AdmList, zipP]
      rcases h with ht | hrest
      · rw [show t = Term.never from eq_never_of_isNever ht,
          show Adm .never w = false from rfl, Bool.false_and]
      · rw [ih (ws := ws') hrest, Bool.and_false]

/-- Normalising a list keeps what it admits. -/
theorem Adm_listOf (pre : List Term) (sp : Option Term) (suf : List Term) (v : Value) :
    Adm (Term.listOf pre sp suf) v = Adm (.list pre sp suf) v := by
  unfold Term.listOf
  split
  next hany =>
    cases v <;> simp only [Adm] <;> try rfl
    rename_i ws
    refine Eq.symm ?_
    simp only [alignPL]
    rcases Bool.or_eq_true .. |>.mp hany with hp | hs
    · rw [alignP_never_false hp, Bool.false_and]
    · rw [zipP_never_false hs, Bool.and_false]
  next => rfl

/-- Normalising a tuple keeps what it admits. -/
theorem Adm_tupleOf (ts : List Term) (tail : Option Term) (v : Value) :
    Adm (Term.tupleOf ts tail) v = Adm (.tuple ts tail) v :=
  Adm_listOf ts tail [] v

/-- …and normalising a refinement keeps what it admits. -/
theorem Adm_refineOf (z : Term) (p : Pred) (v : Value) :
    Adm (Term.refineOf z p) v = Adm (.refine z p) v := by
  unfold Term.refineOf
  split
  next hz => rw [show z = Term.never from eq_never_of_isNever hz]; simp [Adm]
  next => rfl

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

section StructuralAdm
-- the object rows put the whole field table to `decide` under a binder, which is where the
-- default budget goes
set_option maxHeartbeats 1000000

/-! ## `Adm` is a homomorphism from the meet to conjunction, structurally

The definition recurses on the left operand, so the theorem does too: one shared lemma for every
row that reads the right operand alone, one flat lemma per left constructor, and an outer
recursion that feeds the induction hypothesis at the subterm into the two. No measure appears,
and the depth bounds the well-founded proof carries are gone with it. -/

/-- The right operands `meetSRight` hands to the family: everything its own rows do not answer.
    A family's catch-all row answers the bottom, which is right for these and wrong for the
    seven above, so the predicate below carries the same split the definition makes. -/
def Delegated : Term → Prop
  | .never | .held _ _ _ | .legacy _ _ | .custom _ _ | .lazy _ | .refine _ _ | .union _ => False
  | _ => True

/-- `f` answers the meet with one term fixed on the left, at EVERY right operand. The container
    families need this of the call they carry, because they apply it to a subterm of any shape. -/
def AdmSound (x : Term) (f : Term → Option Term) : Prop :=
  ∀ y z, f y = some z → ∀ v, Adm z v = (Adm x v && Adm y v)

/-- `fam` answers the meet with one term fixed on the left, over the operands it is handed. -/
def AdmFam (x : Term) (fam : Term → Option Term) : Prop :=
  ∀ y z, Delegated y → fam y = some z → ∀ v, Adm z v = (Adm x v && Adm y v)

/-- The list companion is the plain map, so the union row reuses the `Forall₂` machinery. -/
theorem meetSRightL_eq (fam : Term → Option Term) :
    ∀ os, meetSRightL fam os = os.map (meetSRight fam)
  | [] => rfl
  | _ :: os => congrArg _ (meetSRightL_eq fam os)

/-- …and the union row's extraction, with no exclusions: the row is reached by the pattern. -/
theorem meetSRight_union {fam : Term → Option Term} {os : List Term} {z : Term}
    (h : meetSRight fam (.union os) = some z) :
    ∃ zs, List.Forall₂ (fun t w => meetSRight fam t = some w) os zs ∧
      unionOk os = true ∧ unionOk (zs.filter (fun w => !w.isNever)) = true ∧
      z = Term.ofOptions (zs.filter (fun w => !w.isNever)) := by
  rw [meetSRight] at h
  obtain ⟨zs, hzs, hg⟩ := Option.bind_eq_some_iff.mp h
  unfold Term.ofOptionsGuarded at hg
  split at hg
  next hok =>
    rw [Bool.and_eq_true] at hok
    refine ⟨zs, allSome_map_forall₂ _ ?_, hok.1, hok.2, (Option.some.inj hg).symm⟩
    rw [← meetSRightL_eq]
    exact hzs
  next => exact absurd hg (by simp)

mutual
/-- Every row that reads the right operand alone is sound wherever the family is. -/
theorem Adm_meetSRight {x : Term} {fam : Term → Option Term} (hf : AdmFam x fam) :
    ∀ y z, meetSRight fam y = some z → ∀ v, Adm z v = (Adm x v && Adm y v)
  | .never, _, h, _ => by
      simp only [meetSRight, Option.some.injEq] at h; subst h; simp [Adm]
  | .held _ _ _, _, h, _ => by simp [meetSRight] at h
  | .legacy _ _, _, h, _ => by simp [meetSRight] at h
  | .custom _ _, _, h, _ => by simp [meetSRight] at h
  | .lazy _, _, h, _ => by simp [meetSRight] at h
  | .refine y p, _, h, v => by
      simp only [meetSRight] at h
      split at h
      · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        have ihw := Adm_meetSRight hf y w hw v
        rw [Adm_refineOf]
        simp only [Adm, ihw]
        simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
      · exact absurd h (by simp)
  | .union os, _, h, v => by
      obtain ⟨zs, hF, hco, hcz, rfl⟩ := meetSRight_union h
      rw [Adm_ofOptions hcz, AdmAny_filter_never,
        show Adm (.union _) v = selOptV (AdmSpecs _) v from rfl, selOptV_eq_AdmAny hco,
        Bool.and_comm]
      exact AdmAny_meet v (Adm_meetSRightL hf os _ hF)
  | .string, _, h, v => hf .string _ trivial h v
  | .number, _, h, v => hf .number _ trivial h v
  | .decimal, _, h, v => hf .decimal _ trivial h v
  | .boolean, _, h, v => hf .boolean _ trivial h v
  | .binary, _, h, v => hf .binary _ trivial h v
  | .null, _, h, v => hf .null _ trivial h v
  | .literal k lv, _, h, v => hf (.literal k lv) _ trivial h v
  | .set b, _, h, v => hf (.set b) _ trivial h v
  | .opaq l, _, h, v => hf (.opaq l) _ trivial h v
  | .array e, _, h, v => hf (.array e) _ trivial h v
  | .record c, _, h, v => hf (.record c) _ trivial h v
  | .tuple ts tl, _, h, v => hf (.tuple ts tl) _ trivial h v
  | .object b, _, h, v => hf (.object b) _ trivial h v
termination_by structural y => y

/-- The list companion: the union row's options, lifted pointwise. It recurses on the list and
    `Adm_meetSRight` on the term, as the definition's own pair does. -/
theorem Adm_meetSRightL {x : Term} {fam : Term → Option Term} (hf : AdmFam x fam) :
    ∀ os zs, List.Forall₂ (fun t w => meetSRight fam t = some w) os zs →
      List.Forall₂ (fun t w => ∀ u, Adm w u = (Adm t u && Adm x u)) os zs
  | [], _, h => by cases h; exact .nil
  | t :: ts, _, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun u => by rw [Adm_meetSRight hf t _ hh u, Bool.and_comm])
            (Adm_meetSRightL hf ts _ ht)
termination_by structural os => os
end

/-- The catch-all of every family: two constructors in different value slots meet at the bottom. -/
theorem Adm_never_orth {x y : Term} (ho : Orth1 x y = true) (v : Value) :
    Adm Term.never v = (Adm x v && Adm y v) := by
  rw [Adm_and_false ho v]; simp [Adm]

/-- The tactic every family's catch-all row uses. -/
local macro "fam_never" fam:ident : tactic => `(tactic|
  (simp only [$fam:ident, Option.some.injEq] at *
   subst_vars
   refine Adm_never_orth ?_ _
   first
     | rfl
     | decide
     | (cases ‹GroundKind› <;> first | rfl | decide)
     | (cases ‹SetBase› <;> first | rfl | decide)
     | (cases ‹GroundKind› <;> cases ‹SetBase› <;> first | rfl | decide)))

/-- `boolean` meets the boolean literal, `opaque`, and nothing else. -/
theorem Adm_famBoolean : AdmFam Term.boolean famBoolean := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case boolean => simp only [famBoolean, Option.some.injEq] at h; subst h; simp
  case literal k v' =>
      simp only [famBoolean] at h
      split at h
      next hk =>
        subst hk
        simp only [Option.some.injEq] at h; subst h
        cases v <;> simp [Adm, AdmLit, inL, inD, isStored]
      next hk =>
        simp only [Option.some.injEq] at h; subst h
        cases k <;> cases v <;> simp_all [Adm, AdmLit, inL, inD, isStored]
  case opaq l =>
      simp only [famBoolean, Option.some.injEq] at h; subst h
      cases v <;> (try simp only [Adm_opaq_bool]) <;> simp [Adm]
  all_goals fam_never famBoolean

/-- `binary` meets the binary literal, `opaque`, and nothing else. -/
theorem Adm_famBinary : AdmFam Term.binary famBinary := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case binary => simp only [famBinary, Option.some.injEq] at h; subst h; simp
  case literal k v' =>
      simp only [famBinary] at h
      split at h
      next hk =>
        subst hk
        simp only [Option.some.injEq] at h; subst h
        cases v <;> simp [Adm, AdmLit, inL, inD, isStored]
      next hk =>
        simp only [Option.some.injEq] at h; subst h
        cases k <;> cases v <;> simp_all [Adm, AdmLit, inL, inD, isStored]
  case opaq l =>
      simp only [famBinary, Option.some.injEq] at h; subst h
      cases v <;> (try simp only [Adm_opaq_bin]) <;> simp [Adm]
  all_goals fam_never famBinary

/-- `null` meets the null literal, `opaque`, and nothing else. -/
theorem Adm_famNull : AdmFam Term.null famNull := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case null => simp only [famNull, Option.some.injEq] at h; subst h; simp
  case literal k v' =>
      simp only [famNull] at h
      split at h
      next hk =>
        subst hk
        simp only [Option.some.injEq] at h; subst h
        cases v <;> simp [Adm, AdmLit, inL, inD, isStored]
      next hk =>
        simp only [Option.some.injEq] at h; subst h
        cases k <;> cases v <;> simp_all [Adm, AdmLit, inL, inD, isStored]
  case opaq l =>
      simp only [famNull, Option.some.injEq] at h; subst h
      cases v <;> (try simp only [Adm_opaq_null]) <;> simp [Adm]
  all_goals fam_never famNull

/-- `string` meets its own literals and `opaque`, and refuses the `decimal` family. -/
theorem Adm_famString : AdmFam Term.string famString := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case string => simp only [famString, Option.some.injEq] at h; subst h; simp
  case decimal => simp [famString] at h
  case literal k v' =>
      cases k <;> simp only [famString, Option.some.injEq, reduceCtorEq] at h <;>
        (try subst h) <;>
        first
          | (cases v <;> simp [Adm, AdmLit, inL, inD, isStored] <;>
              (try (intro hs _; exact hs)))
          | exact Adm_never_orth (by rfl) v
  case opaq l =>
      simp only [famString, Option.some.injEq] at h; subst h
      cases v <;> (try simp only [Adm_opaq_str]) <;> simp [Adm]
  all_goals fam_never famString

/-- `number` meets its own literals and a lossy `opaque`, and refuses `decimal`. -/
theorem Adm_famNumber : AdmFam Term.number famNumber := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case number => simp only [famNumber, Option.some.injEq] at h; subst h; simp
  case decimal => simp [famNumber] at h
  case literal k v' =>
      cases k <;> simp only [famNumber, Option.some.injEq, reduceCtorEq] at h <;>
        (try subst h) <;>
        first
          | (cases v <;> simp [Adm, AdmLit, inL, inD, isStored] <;>
              (try (intro hs _; exact hs)))
          | exact Adm_never_orth (by rfl) v
  case opaq l =>
      simp only [famNumber] at h
      split at h
      next hl =>
        subst hl
        simp only [Option.some.injEq] at h; subst h
        cases v <;> (try simp only [Adm_opaq_num]) <;> simp [Adm, inD]
      next hl =>
        simp only [Bool.not_eq_true] at hl; subst hl
        simp only [Option.some.injEq] at h; subst h
        cases v <;> (try simp only [Adm_opaq_num]) <;> simp [Adm, inD]
  all_goals fam_never famNumber

/-- `decimal` meets its own literals alone: it shares values with `string` and the
    member `N` with `number`, so both refuse. -/
theorem Adm_famDecimal : AdmFam Term.decimal famDecimal := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case decimal => simp only [famDecimal, Option.some.injEq] at h; subst h; simp
  case string => simp [famDecimal] at h
  case number => simp [famDecimal] at h
  case opaq l => simp [famDecimal] at h
  case literal k v' =>
      cases k <;> simp only [famDecimal, Option.some.injEq, reduceCtorEq] at h <;>
        (try subst h) <;>
        first
          | (cases v <;> simp [Adm, AdmLit, inL, inD, isStored] <;>
              (try (intro hs _; exact hs)))
          | exact Adm_never_orth (by rfl) v
  all_goals fam_never famDecimal

/-- A literal meets its own base and an equal literal, and is the bottom elsewhere. -/
theorem Adm_famLit (k : GroundKind) (lv : k.Carrier) : AdmFam (.literal k lv) (famLit k lv) := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case string | number | decimal =>
      cases k <;> simp only [famLit, Option.some.injEq, reduceCtorEq] at h <;>
        (try subst h) <;>
        first
          | (cases v <;> simp [Adm, AdmLit, inL, inD, isStored] <;>
              (try (intro hs _; exact hs)))
          | exact Adm_never_orth (by rfl) v
  case boolean | binary | null =>
      simp only [famLit] at h
      split at h
      next hk =>
        subst hk
        simp only [Option.some.injEq] at h; subst h
        cases v <;> simp [Adm, AdmLit, inL, inD, isStored]
      next hk =>
        simp only [Option.some.injEq] at h; subst h
        cases k <;> cases v <;> simp_all [Adm, AdmLit, inL, inD, isStored]
  case literal k' v' =>
      simp only [famLit] at h
      cases k <;> cases k' <;> simp only [Term.meetLit, reduceCtorEq] at h <;>
        (try split at h) <;>
        (try (simp only [Option.some.injEq] at h
              subst h
              cases v <;> simp_all [Adm, AdmLit, inL, isStored, inD]))
  case opaq l => simp [famLit] at h
  all_goals fam_never famLit

/-- Two set bases meet where they are equal, refusing the three that share a wire slot. -/
theorem Adm_famSet (b : SetBase) : AdmFam (.set b) (famSet b) := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case set b' =>
      cases b <;> cases b' <;>
        simp only [famSet, reduceCtorEq, reduceIte, Option.some.injEq] at h <;>
        (try subst h) <;>
        first
          | simp
          | (cases v <;>
              simp_all [Adm, SetBase.adm, isStored, inD, -Classical.not_forall] <;>
              (intros; exact NEFinset.not_forall_notMem _))
  case opaq l => simp [famSet] at h
  all_goals fam_never famSet

/-- `opaque` meets each self-identifying base, and another `opaque` at the conjoined policy. -/
theorem Adm_famOpaq (l : Bool) : AdmFam (.opaq l) (famOpaq l) := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case string | boolean | binary | null =>
      simp only [famOpaq, Option.some.injEq] at h; subst h
      cases v <;>
        (try simp only [Adm_opaq_str, Adm_opaq_bool, Adm_opaq_bin, Adm_opaq_null]) <;>
        simp [Adm]
  case number =>
      simp only [famOpaq] at h
      split at h
      next hl =>
        subst hl
        simp only [Option.some.injEq] at h; subst h
        cases v <;> (try simp only [Adm_opaq_num]) <;> simp [Adm, inD]
      next hl =>
        simp only [Bool.not_eq_true] at hl; subst hl
        simp only [Option.some.injEq] at h; subst h
        cases v <;> (try simp only [Adm_opaq_num]) <;> simp [Adm, inD]
  case opaq l' =>
      simp only [famOpaq, Option.some.injEq] at h; subst h
      exact Adm_opaq_and l l' v
  all_goals simp [famOpaq] at h

/-! ### The container families. The depth bounds go: the lifts are measure-free. -/

/-- The element companion is the plain map. -/
theorem mapF_eq (f : Term → Option Term) : ∀ ts, mapF f ts = ts.map f
  | [] => rfl
  | _ :: ts => congrArg _ (mapF_eq f ts)

/-- The element list of an array against a tuple, lifted pointwise. -/
theorem AdmList_lift {x' : Term} {f : Term → Option Term} (hf : AdmSound x' f) :
    ∀ {ts vs : List Term}, List.Forall₂ (fun t v => f t = some v) ts vs →
      List.Forall₂ (fun p q => ∀ w, q w = (p w && Adm x' w)) (AdmList ts) (AdmList vs) := by
  intro ts
  induction ts with
  | nil => intro vs h; cases h; exact .nil
  | cons t ts ihs =>
      intro vs h
      cases h with
      | cons hh ht =>
          exact .cons (fun w => by rw [hf t _ hh w, Bool.and_comm]) (ihs ht)

/-- …and the tail. -/
theorem AdmOptT_lift {x' : Term} {f : Term → Option Term} (hf : AdmSound x' f)
    {tail tl : Option Term}
    (htl : (tail = none ∧ tl = none) ∨
      ∃ t u, tail = some t ∧ tl = some u ∧ f t = some u) :
    (AdmOptT tail = none ∧ AdmOptT tl = none) ∨
      (∃ p q, AdmOptT tail = some p ∧ AdmOptT tl = some q ∧
        ∀ w, q w = (p w && Adm x' w)) := by
  rcases htl with ⟨rfl, rfl⟩ | ⟨t, u, rfl, rfl, hm⟩
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨Adm t, Adm u, rfl, rfl, fun w => by rw [hf t _ hm w, Bool.and_comm]⟩

/-- The array-against-tuple row's extraction, with no measure. -/
theorem famArr_tuple {f : Term → Option Term} {ts : List Term} {tail : Option Term} {z : Term}
    (h : famArr f (.tuple ts tail) = some z) :
    ∃ vs tl, z = Term.tupleOf vs tl ∧
      List.Forall₂ (fun t v => f t = some v) ts vs ∧
      ((tail = none ∧ tl = none) ∨
        ∃ t u, tail = some t ∧ tl = some u ∧ f t = some u) := by
  simp only [famArr] at h
  split at h
  next vs tl hvs htl =>
    simp only [Option.some.injEq] at h
    refine ⟨vs, tl, h.symm, ?_, ?_⟩
    · exact allSome_map_forall₂ _ (by rw [← mapF_eq]; exact hvs)
    · cases tail with
      | none =>
          replace htl : some (none : Option Term) = some tl := htl
          exact .inl ⟨rfl, by simpa using htl.symm⟩
      | some t =>
          replace htl : Option.map some (f t) = some tl := htl
          obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp htl
          exact .inr ⟨t, u, rfl, rfl, hu⟩
  next => exact absurd h (by simp)

/-- An array meets an array at the element, and a tuple at every declared position. -/
theorem Adm_famArr {x' : Term} {f : Term → Option Term} (hf : AdmSound x' f) :
    AdmFam (.array x') (famArr f) := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case array e =>
      simp only [famArr] at h
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      have ihw := hf e w hw
      cases v <;> simp only [Adm, Bool.and_self, allP_and ihw]
  case tuple ts tail =>
      obtain ⟨vs, tl, rfl, hts, htl⟩ := famArr_tuple h
      rw [Adm_tupleOf]
      cases v <;>
        simp only [Adm, Bool.and_self,
          alignP_meet_all (AdmList_lift hf hts) (AdmOptT_lift hf htl)]
  case opaq l => simp [famArr] at h
  all_goals fam_never famArr

/-- A tuple's position functions, applied at one term and lifted pointwise. -/
theorem applyAt_lift {y : Term} :
    ∀ {ts : List Term} {fs : List (Term → Option Term)} {vs : List Term},
      List.Forall₂ AdmSound ts fs →
      List.Forall₂ (fun f v => f y = some v) fs vs →
      List.Forall₂ (fun p q => ∀ w, q w = (p w && Adm y w)) (AdmList ts) (AdmList vs) := by
  intro ts
  induction ts with
  | nil => intro fs vs hfs hv; cases hfs; cases hv; exact .nil
  | cons t ts ihs =>
      intro fs vs hfs hv
      cases hfs with
      | cons hf hfs' =>
          cases hv with
          | cons hh ht => exact .cons (fun w => by rw [hf y _ hh w, Bool.and_comm]) (ihs hfs' ht)

/-- …and the same two tuples' positions zipped. -/
theorem zipF_lift :
    ∀ {ts us : List Term} {fs : List (Term → Option Term)} {vs : List Term},
      List.Forall₂ AdmSound ts fs →
      List.Forall₂ (fun (p : (Term → Option Term) × Term) v => p.1 p.2 = some v) (fs.zip us) vs →
      List.Forall₂ (fun (pq : VP × VP) r => ∀ w, r w = (pq.1 w && pq.2 w))
        ((AdmList ts).zip (AdmList us)) (AdmList vs) := by
  intro ts
  induction ts with
  | nil => intro us fs vs hfs hv; cases hfs; cases hv; exact .nil
  | cons t ts ihs =>
      intro us fs vs hfs hv
      cases hfs with
      | cons hf hfs' =>
          cases us with
          | nil => cases hv; exact .nil
          | cons u us =>
              cases hv with
              | cons hh ht => exact .cons (fun w => hf u _ hh w) (ihs hfs' ht)

/-- A record meets a record at the value term. -/
theorem Adm_famRecTerm {x' : Term} {f : Term → Option Term} (hf : AdmSound x' f)
    {y w : Term} (hw : f y = some w) (v : Value) :
    Adm (.record w) v = (Adm (.record x') v && Adm (.record y) v) := by
  have ihw := hf y w hw
  cases v <;> simp only [Adm, Bool.and_self, decide_forall_and (fun k => ihw _)]

/-- The position companion is the plain map at one term. -/
theorem applyAt_eq (y : Term) : ∀ fs, applyAt fs y = fs.map (fun f => f y)
  | [] => rfl
  | _ :: fs => congrArg _ (applyAt_eq y fs)

/-- …and the zip companion is the plain map over the zip. -/
theorem zipF_eq : ∀ (fs : List (Term → Option Term)) (us : List Term),
    zipF fs us = (fs.zip us).map (fun p => p.1 p.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: fs, _ :: us => congrArg _ (zipF_eq fs us)

/-- A tuple meets an array at every position, and another tuple by arity. -/
theorem Adm_famTup {ts : List Term} {tail : Option Term}
    {fs : List (Term → Option Term)} {ftail : Option (Term → Option Term)}
    (hfs : List.Forall₂ AdmSound ts fs)
    (hft : (tail = none ∧ ftail = none) ∨
      ∃ t ft, tail = some t ∧ ftail = some ft ∧ AdmSound t ft) :
    AdmFam (.tuple ts tail) (famTup fs ftail) := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case array e =>
      simp only [famTup] at h
      split at h
      next vs tl hvs htl =>
        simp only [Option.some.injEq] at h; subst h
        have hF : List.Forall₂ (fun f w => f e = some w) fs vs :=
          allSome_map_forall₂ _ (by rw [← applyAt_eq]; exact hvs)
        have hT : (AdmOptT tail = none ∧ AdmOptT tl = none) ∨
            (∃ p q, AdmOptT tail = some p ∧ AdmOptT tl = some q ∧
              ∀ w, q w = (p w && Adm e w)) := by
          rcases hft with ⟨rfl, rfl⟩ | ⟨t, ft, rfl, rfl, hsound⟩
          · replace htl : some (none : Option Term) = some tl := htl
            simp only [Option.some.injEq] at htl; subst htl; exact .inl ⟨rfl, rfl⟩
          · replace htl : Option.map some (ft e) = some tl := htl
            obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp htl
            exact .inr ⟨Adm t, Adm u, rfl, rfl, fun w => by rw [hsound e _ hu w, Bool.and_comm]⟩
        rw [Adm_tupleOf]
        cases v <;> simp only [Adm, Bool.and_self] <;>
          rw [Bool.and_comm, alignP_meet_all (applyAt_lift hfs hF) hT]
      next => exact absurd h (by simp)
  case tuple us tail' =>
      simp only [famTup] at h
      split at h
      next hlen =>
        split at h
        next vs tl hvs htl =>
          simp only [Option.some.injEq] at h; subst h
          have hF : List.Forall₂
              (fun (p : (Term → Option Term) × Term) w => p.1 p.2 = some w) (fs.zip us) vs :=
            allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hvs)
          have hT : (AdmOptT tail = none ∧ AdmOptT tail' = none ∧ AdmOptT tl = none) ∨
              ∃ p q r, AdmOptT tail = some p ∧ AdmOptT tail' = some q ∧ AdmOptT tl = some r ∧
                ∀ w, r w = (p w && q w) := by
            rcases hft with ⟨rfl, rfl⟩ | ⟨t, ft, rfl, rfl, hsound⟩
            · cases tail' with
              | none =>
                  replace htl : some (none : Option Term) = some tl := htl
                  simp only [Option.some.injEq] at htl; subst htl
                  exact .inl ⟨rfl, rfl, rfl⟩
              | some u => exact absurd htl (by simp)
            · cases tail' with
              | none => exact absurd htl (by simp)
              | some u =>
                  replace htl : Option.map some (ft u) = some tl := htl
                  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp htl
                  exact .inr ⟨Adm t, Adm u, Adm w, rfl, rfl, rfl, fun q => hsound u _ hw q⟩
          rw [Adm_tupleOf]
          cases v <;> simp only [Adm, Bool.and_self,
            alignP_meet_zip (zipF_lift hfs hF)
              (by rw [AdmList_length, AdmList_length]
                  exact hfs.length_eq.trans hlen) hT]
        next => exact absurd h (by simp)
      next hlen =>
        split at h
        next hb =>
          simp only [Option.some.injEq] at h; subst h
          simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hb
          obtain ⟨hb1, hb2⟩ := hb
          have htn : tail = none := by
            rcases hft with ⟨rfl, _⟩ | ⟨t, ft, rfl, rfl, _⟩
            · rfl
            · exact absurd hb1 (by simp)
          subst htn; subst hb2
          have hne : ts.length ≠ us.length := fun hc =>
            hlen (((hfs.length_eq).symm.trans hc))
          cases v with
          | arr ws =>
            simp only [Adm, AdmOptT]
            cases hA : alignP (AdmList ts) none ws with
            | false => simp
            | true =>
              cases hB : alignP (AdmList us) none ws with
              | false => simp
              | true =>
                exact absurd
                  (((alignP_none_length hA).trans (AdmList_length _)).symm.trans
                    ((alignP_none_length hB).trans (AdmList_length _))) hne
          | _ => simp [Adm]
        next => exact absurd h (by simp)
  case opaq l => simp [famTup] at h
  all_goals fam_never famTup

/-! ### The object families. The three body helpers are stated over an abstract field function,
     so the flipped cell and the object cell share them. -/

/-- The presence test reads the marks alone, so a field table with the body's marks has the
    body's test. -/
theorem valPresentT_of_isReq {b : Body} {F : {k // k ∈ b.fields} → Field}
    (hreq : ∀ k, Field.isReq (F k) = Field.isReq (b.at k)) (keys : Finset Name) :
    valPresentT b.fields F keys = valPresentT b.fields b.at keys := by
  rw [valPresentT_req, valPresentT_req]
  exact decide_eq_decide.mpr (forall_congr' fun k => by rw [hreq k])

/-- Every present name goes through its field and the left operand's term alike. -/
theorem objAdmV_of_left {b : Body} {x t r : Term} {F : {k // k ∈ b.fields} → Field}
    (ihf : ∀ (k : {k // k ∈ b.fields}) (w : Value),
      AdmField (F k) w = (Adm x w && AdmField (b.at k) w))
    (iht : ∀ w, Adm r w = (Adm x w && Adm t w))
    (keys : Finset Name) (g : {k // k ∈ keys} → Value) :
    objAdmV ⟨b.fields, fun k => AdmField (F k)⟩ (some (Adm r)) keys g
      = (decide (∀ k : {k // k ∈ keys}, Adm x (g k) = true)
         && objAdmV ⟨b.fields, fun k => AdmField (b.at k)⟩ (some (Adm t)) keys g) := by
  simp only [objAdmV, entryP, MapOf.at]
  refine decide_forall_and (fun k => ?_)
  by_cases hk : k.1 ∈ b.fields
  · simp only [dif_pos hk]; exact ihf ⟨k.1, hk⟩ (g k)
  · simp only [dif_neg hk]; exact iht (g k)

/-- No declared field meets the left operand's term to the bottom at a value both admit. -/
theorem isBottom_false_of_left {b : Body} {x : Term} {F : {k // k ∈ b.fields} → Field}
    (hreq : ∀ k, Field.isReq (F k) = Field.isReq (b.at k))
    (ihf : ∀ (k : {k // k ∈ b.fields}) (w : Value),
      AdmField (F k) w = (Adm x w && AdmField (b.at k) w))
    {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (hA : AdmBody b (.map keys g) = true)
    (hR : decide (∀ k : {k // k ∈ keys}, Adm x (g k) = true) = true) :
    ∀ k, Field.isBottom (F k) = false := by
  rw [AdmBody_map, Bool.and_eq_true] at hA
  intro k
  refine Bool.eq_false_iff.mpr (fun hbot => ?_)
  have hreqk : Field.isReq (b.at k) = true := (hreq k) ▸ isReq_of_isBottom hbot
  have hk : k.1 ∈ keys := mem_keys_of_isReq hA.1 k.2 hreqk
  have hrow := objAdmV_row hA.2 hk k.2
  have hrec := of_decide_eq_true hR ⟨k.1, hk⟩
  have hi := ihf k (g ⟨k.1, hk⟩)
  rw [AdmField_of_isBottom hbot, hrow, hrec] at hi
  exact absurd hi (by simp)

/-- A field met with one term carries two terms that meet. -/
theorem AdmField_fieldMeetT {f : Term → Option Term} {fl fm : Field}
    (h : fieldMeetT f fl = some fm) :
    ∃ tx tz, f tx = some tz ∧ AdmField fl = Adm tx ∧ AdmField fm = Adm tz := by
  cases fl <;> simp only [fieldMeetT, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨tz, hz, rfl⟩ := h <;> exact ⟨_, tz, hz, rfl, rfl⟩

/-- …and keeps the field's mark, because a term says nothing about presence. -/
theorem isReq_fieldMeetT {f : Term → Option Term} {fl fm : Field}
    (h : fieldMeetT f fl = some fm) : Field.isReq fm = Field.isReq fl := by
  cases fl <;> simp only [fieldMeetT, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨tz, hz, rfl⟩ := h <;> rfl

/-- What a record against an object answers: the refusal at a rest that is not a codec, the
    bottom where a declared field empties, and otherwise the object. -/
theorem recObj_extract {f : Term → Option Term} {b : Body} {z : Term}
    (h : recObj f b = some z) :
    ∃ t r, b.rest = .codec t ∧ f t = some r ∧
      (∀ k : {k // k ∈ b.fields}, (fieldMeetT f (b.at k)).isSome = true) ∧
      ((z = .never ∧ ¬ (∀ k, Field.isBottom
            ((fieldMeetT f (b.at k)).getD (.optional .never)) = false))
       ∨ z = .object (.mk b.fields
            (fun k => (fieldMeetT f (b.at k)).getD (.optional .never)) (.codec r))) := by
  unfold recObj at h
  split at h
  next t ht =>
    split at h
    next hok =>
      split at h
      next r hmr =>
        refine ⟨t, r, ht, hmr, of_decide_eq_true hok, ?_⟩
        split at h
        next _ => exact Or.inr (Option.some.inj h).symm
        next hnb =>
          exact Or.inl ⟨(Option.some.inj h).symm, fun hall => hnb (decide_eq_true hall)⟩
      next => exact absurd h (by simp)
    next => exact absurd h (by simp)
  next => exact absurd h (by simp)

/-- A record meets a record at the value term, and an object through every declared field. -/
theorem Adm_famRec {x' : Term} {f : Term → Option Term} (hf : AdmSound x' f) :
    AdmFam (.record x') (famRec f) := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case record c =>
      simp only [famRec] at h
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_famRecTerm hf hw v
  case object b =>
      simp only [famRec] at h
      obtain ⟨t, r, hrest, hmt, hok, hcase⟩ := recObj_extract h
      have hreq : ∀ k : {k // k ∈ b.fields},
          Field.isReq ((fieldMeetT f (b.at k)).getD (.optional .never))
            = Field.isReq (b.at k) := by
        intro k
        obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfm, Option.getD_some]
        exact isReq_fieldMeetT hfm
      have ihf : ∀ (k : {k // k ∈ b.fields}) (w : Value),
          AdmField ((fieldMeetT f (b.at k)).getD (.optional .never)) w
            = (Adm x' w && AdmField (b.at k) w) := by
        intro k w
        obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        obtain ⟨tx, tz, hz, hx, hfz⟩ := AdmField_fieldMeetT hfm
        rw [hfm, Option.getD_some, hfz, hx]
        exact hf tx tz hz w
      have iht : ∀ w, Adm r w = (Adm x' w && Adm t w) := hf t r hmt
      have hnm : ∀ w : Value, (∀ keys g, w ≠ .map keys g) →
          Adm z w = (Adm (.record x') w && Adm (.object b) w) := by
        intro w hw
        have hrx : Adm (.record x') w = false := by
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
            show Adm (.record x') (.map keys g)
              = decide (∀ k : {k // k ∈ keys}, Adm x' (g k) = true) from rfl]
        rcases hcase with ⟨rfl, hnb⟩ | rfl
        · show (false : Bool) = _
          cases hR : decide (∀ k : {k // k ∈ keys}, Adm x' (g k) = true) with
          | false => rfl
          | true =>
            cases hA : AdmBody b (.map keys g) with
            | false => simp
            | true => exact absurd (isBottom_false_of_left hreq ihf hA hR) hnb
        · show AdmBody (.mk b.fields
              (fun k => (fieldMeetT f (b.at k)).getD (.optional .never)) (.codec r))
                (.map keys g) = _
          rw [AdmBody_map, AdmBody_map]
          simp only [Body.fields_mk, Body.at_mk, Body.rest_mk, hrest]
          rw [valPresentT_of_isReq hreq, show AdmRest (.codec r) = some (Adm r) from rfl,
              show AdmRest (.codec t) = some (Adm t) from rfl, objAdmV_of_left ihf iht]
          simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
      all_goals exact hnm _ (fun _ _ hc => Value.noConfusion hc)
  case opaq l => simp [famRec] at h
  all_goals fam_never famRec

/-! ### …and the same three over the right operand, and over two bodies. -/

/-- Every present name goes through its field and the right operand's term alike. -/
theorem objAdmV_of_right {b : Body} {x t r : Term} {F : {k // k ∈ b.fields} → Field}
    (ihf : ∀ (k : {k // k ∈ b.fields}) (w : Value),
      AdmField (F k) w = (AdmField (b.at k) w && Adm x w))
    (iht : ∀ w, Adm r w = (Adm t w && Adm x w))
    (keys : Finset Name) (g : {k // k ∈ keys} → Value) :
    objAdmV ⟨b.fields, fun k => AdmField (F k)⟩ (some (Adm r)) keys g
      = (objAdmV ⟨b.fields, fun k => AdmField (b.at k)⟩ (some (Adm t)) keys g
         && decide (∀ k : {k // k ∈ keys}, Adm x (g k) = true)) := by
  simp only [objAdmV, entryP, MapOf.at]
  refine decide_forall_and (fun k => ?_)
  by_cases hk : k.1 ∈ b.fields
  · simp only [dif_pos hk]; exact ihf ⟨k.1, hk⟩ (g k)
  · simp only [dif_neg hk]; exact iht (g k)

/-- No declared field meets the right operand's term to the bottom at a value both admit. -/
theorem isBottom_false_of_right {b : Body} {x : Term} {F : {k // k ∈ b.fields} → Field}
    (hreq : ∀ k, Field.isReq (F k) = Field.isReq (b.at k))
    (ihf : ∀ (k : {k // k ∈ b.fields}) (w : Value),
      AdmField (F k) w = (AdmField (b.at k) w && Adm x w))
    {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (hA : AdmBody b (.map keys g) = true)
    (hR : decide (∀ k : {k // k ∈ keys}, Adm x (g k) = true) = true) :
    ∀ k, Field.isBottom (F k) = false := by
  rw [AdmBody_map, Bool.and_eq_true] at hA
  intro k
  refine Bool.eq_false_iff.mpr (fun hbot => ?_)
  have hreqk : Field.isReq (b.at k) = true := (hreq k) ▸ isReq_of_isBottom hbot
  have hk : k.1 ∈ keys := mem_keys_of_isReq hA.1 k.2 hreqk
  have hrow := objAdmV_row hA.2 hk k.2
  have hrec := of_decide_eq_true hR ⟨k.1, hk⟩
  have hi := ihf k (g ⟨k.1, hk⟩)
  rw [AdmField_of_isBottom hbot, hrow, hrec] at hi
  exact absurd hi (by simp)

/-- Every present name goes through both bodies' fields, a shared name through the meet. -/
theorem objAdmV_of_bodies {a b : Body} {F : {k // k ∈ Body.shared a b} → Field}
    (ihf : ∀ (k : {k // k ∈ Body.shared a b}) (w : Value),
      AdmField (F k) w = (AdmField (a.at ⟨k.1, Body.mem_shared_left k.2⟩) w
        && AdmField (b.at ⟨k.1, Body.mem_shared_right k.2⟩) w))
    (keys : Finset Name) (g : {k // k ∈ keys} → Value) :
    objAdmV ⟨Body.shared a b, fun k => AdmField (F k)⟩ none keys g
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

/-- The declared set is the intersection and the required set the union, which is what the
    two presence tests conjoin to. -/
theorem valPresentT_of_bodies {a b : Body} {F : {k // k ∈ Body.shared a b} → Field}
    (hab : Body.reqShared a b = true) (hba : Body.reqShared b a = true)
    (hisreq : ∀ k, Field.isReq (F k)
      = (Field.isReq (a.at ⟨k.1, Body.mem_shared_left k.2⟩)
         || Field.isReq (b.at ⟨k.1, Body.mem_shared_right k.2⟩)))
    (keys : Finset Name) :
    valPresentT (Body.shared a b) F keys
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
      exact hs ⟨k.1, hk⟩ (by rw [hisreq ⟨k.1, hk⟩, hreq, Bool.true_or])
    · have hk : k.1 ∈ Body.shared a b := mem_shared_iff.mpr ⟨hB k hreq, k.2⟩
      exact hs ⟨k.1, hk⟩ (by rw [hisreq ⟨k.1, hk⟩, hreq, Bool.or_true])
  · rintro ⟨hA', hB'⟩ k hreq
    rw [hisreq k, Bool.or_eq_true] at hreq
    rcases hreq with hr | hr
    · exact hA' ⟨k.1, Body.mem_shared_left k.2⟩ hr
    · exact hB' ⟨k.1, Body.mem_shared_right k.2⟩ hr

/-- No shared field meets to the bottom at a value both bodies admit. -/
theorem isBottom_false_of_bodies {a b : Body} {F : {k // k ∈ Body.shared a b} → Field}
    (hisreq : ∀ k, Field.isReq (F k)
      = (Field.isReq (a.at ⟨k.1, Body.mem_shared_left k.2⟩)
         || Field.isReq (b.at ⟨k.1, Body.mem_shared_right k.2⟩)))
    (ihf : ∀ (k : {k // k ∈ Body.shared a b}) (w : Value),
      AdmField (F k) w = (AdmField (a.at ⟨k.1, Body.mem_shared_left k.2⟩) w
        && AdmField (b.at ⟨k.1, Body.mem_shared_right k.2⟩) w))
    {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (hA : AdmBody a (.map keys g) = true) (hB : AdmBody b (.map keys g) = true) :
    ∀ k, Field.isBottom (F k) = false := by
  rw [AdmBody_map, Bool.and_eq_true] at hA hB
  intro k
  refine Bool.eq_false_iff.mpr (fun hbot => ?_)
  have ha := Body.mem_shared_left k.2
  have hb := Body.mem_shared_right k.2
  have hreq : Field.isReq (F k) = true := isReq_of_isBottom hbot
  rw [hisreq k, Bool.or_eq_true] at hreq
  have hk : k.1 ∈ keys := by
    rcases hreq with hr | hr
    · exact mem_keys_of_isReq hA.1 ha hr
    · exact mem_keys_of_isReq hB.1 hb hr
  have hrowA := objAdmV_row hA.2 hk ha
  have hrowB := objAdmV_row hB.2 hk hb
  have hi := ihf k (g ⟨k.1, hk⟩)
  rw [AdmField_of_isBottom hbot, hrowA, hrowB] at hi
  exact absurd hi (by simp)

/-- What an object against a record answers, with the object on the left. -/
theorem objRec_extract {fs : Finset Name} {gt : {k // k ∈ fs} → Term → Option Field}
    {frest : Option (Term → Option Term)} {x z : Term}
    (h : objRec fs gt frest x = some z) :
    ∃ fr r, frest = some fr ∧ fr x = some r ∧
      (∀ k, (gt k x).isSome = true) ∧
      ((z = .never ∧ ¬ (∀ k, Field.isBottom ((gt k x).getD (.optional .never)) = false))
       ∨ z = .object (.mk fs (fun k => (gt k x).getD (.optional .never)) (.codec r))) := by
  unfold objRec at h
  cases hfr : frest with
  | none => rw [hfr] at h; exact absurd h (by simp)
  | some fr =>
    rw [hfr] at h
    simp only at h
    split at h
    next hok =>
      split at h
      next r hr =>
        refine ⟨fr, r, rfl, hr, of_decide_eq_true hok, ?_⟩
        split at h
        next _ => exact Or.inr (Option.some.inj h).symm
        next hnb =>
          exact Or.inl ⟨(Option.some.inj h).symm, fun hall => hnb (decide_eq_true hall)⟩
      next => exact absurd h (by simp)
    next => exact absurd h (by simp)

/-- What two objects answer: the bottom where the required names do not fit the
    intersection or a shared field empties, and otherwise the object over the shared names. -/
theorem objObj_extract {a b : Body} {g : {k // k ∈ a.fields} → Field → Option Field} {z : Term}
    (h : objObj a g b = some z) :
    ∃ r, Rest.merge a.rest b.rest = some r ∧
      ((z = .never ∧ ¬ (Body.reqShared a b = true ∧ Body.reqShared b a = true))
       ∨ (Body.reqShared a b = true ∧ Body.reqShared b a = true ∧
          (∀ k : {k // k ∈ Body.shared a b},
            (g ⟨k.1, Body.mem_shared_left k.2⟩
              (b.at ⟨k.1, Body.mem_shared_right k.2⟩)).isSome = true) ∧
          ((z = .never ∧ ¬ (∀ k : {k // k ∈ Body.shared a b}, Field.isBottom
              ((g ⟨k.1, Body.mem_shared_left k.2⟩
                (b.at ⟨k.1, Body.mem_shared_right k.2⟩)).getD (.optional .never)) = false))
           ∨ z = .object (.mk (Body.shared a b)
              (fun k => (g ⟨k.1, Body.mem_shared_left k.2⟩
                (b.at ⟨k.1, Body.mem_shared_right k.2⟩)).getD (.optional .never)) r)))) := by
  unfold objObj at h
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
          refine Or.inr ⟨hreq.1, hreq.2, ?_⟩
          split at h
          next hok =>
            refine ⟨of_decide_eq_true hok, ?_⟩
            split at h
            next _ => exact Or.inr (Option.some.inj h).symm
            next hnb =>
              exact Or.inl ⟨(Option.some.inj h).symm, fun hall => hnb (decide_eq_true hall)⟩
          next => exact absurd h (by simp)
        next hreq =>
          refine Or.inl ⟨(Option.some.inj h).symm, ?_⟩
          rw [Bool.and_eq_true] at hreq
          exact hreq
      next => exact absurd h (by simp)
    next => exact absurd h (by simp)
  next => exact absurd h (by simp)

/-- An object meets an object over the shared names, and a record through every field. -/
theorem Adm_famObj {a : Body} {g : {k // k ∈ a.fields} → Field → Option Field}
    {gt : {k // k ∈ a.fields} → Term → Option Field}
    {frest : Option (Term → Option Term)}
    (hg : ∀ (k : {k // k ∈ a.fields}) (fl fm : Field), g k fl = some fm →
      ∀ w, AdmField fm w = (AdmField (a.at k) w && AdmField fl w))
    (hgreq : ∀ (k : {k // k ∈ a.fields}) (fl fm : Field), g k fl = some fm →
      Field.isReq fm = (Field.isReq (a.at k) || Field.isReq fl))
    (hgt : ∀ (k : {k // k ∈ a.fields}) (y : Term) (fm : Field), gt k y = some fm →
      ∀ w, AdmField fm w = (AdmField (a.at k) w && Adm y w))
    (hgtreq : ∀ (k : {k // k ∈ a.fields}) (y : Term) (fm : Field), gt k y = some fm →
      Field.isReq fm = Field.isReq (a.at k))
    (hfr : ∀ fr, frest = some fr → ∃ t, a.rest = .codec t ∧ AdmSound t fr) :
    AdmFam (.object a) (famObj a g gt frest) := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case object b =>
      simp only [famObj] at h
      obtain ⟨r, hr, hcase⟩ := objObj_extract h
      obtain ⟨hra, hrb, hrr⟩ := Rest.merge_admRest hr
      have hnm : ∀ w : Value, (∀ keys gv, w ≠ .map keys gv) →
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
      case map keys gv =>
        rw [show Adm (.object a) (.map keys gv) = AdmBody a (.map keys gv) from rfl,
            show Adm (.object b) (.map keys gv) = AdmBody b (.map keys gv) from rfl]
        rcases hcase with ⟨rfl, hne⟩ | ⟨hab, hba, hok, hrest⟩
        · show (false : Bool) = _
          cases hA : AdmBody a (.map keys gv) with
          | false => rfl
          | true =>
            cases hB : AdmBody b (.map keys gv) with
            | false => rfl
            | true => exact absurd ⟨reqShared_of_adm hrb hA hB, reqShared_of_adm hra hB hA⟩ hne
        · have hisreq : ∀ k : {k // k ∈ Body.shared a b},
              Field.isReq ((g ⟨k.1, Body.mem_shared_left k.2⟩
                (b.at ⟨k.1, Body.mem_shared_right k.2⟩)).getD (.optional .never))
                = (Field.isReq (a.at ⟨k.1, Body.mem_shared_left k.2⟩)
                   || Field.isReq (b.at ⟨k.1, Body.mem_shared_right k.2⟩)) := by
            intro k
            obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
            rw [hfm, Option.getD_some]
            exact hgreq _ _ _ hfm
          have ihf : ∀ (k : {k // k ∈ Body.shared a b}) (w : Value),
              AdmField ((g ⟨k.1, Body.mem_shared_left k.2⟩
                (b.at ⟨k.1, Body.mem_shared_right k.2⟩)).getD (.optional .never)) w
                = (AdmField (a.at ⟨k.1, Body.mem_shared_left k.2⟩) w
                   && AdmField (b.at ⟨k.1, Body.mem_shared_right k.2⟩) w) := by
            intro k w
            obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
            rw [hfm, Option.getD_some]
            exact hg _ _ _ hfm w
          rcases hrest with ⟨rfl, hnb⟩ | rfl
          · show (false : Bool) = _
            cases hA : AdmBody a (.map keys gv) with
            | false => rfl
            | true =>
              cases hB : AdmBody b (.map keys gv) with
              | false => rfl
              | true => exact absurd (isBottom_false_of_bodies hisreq ihf hA hB) hnb
          · show AdmBody (.mk (Body.shared a b) _ r) (.map keys gv) = _
            rw [AdmBody_map, AdmBody_map, AdmBody_map]
            simp only [Body.fields_mk, Body.at_mk, Body.rest_mk, hra, hrb, hrr]
            rw [valPresentT_of_bodies hab hba hisreq, objAdmV_of_bodies ihf]
            simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
      all_goals exact hnm _ (fun _ _ hc => Value.noConfusion hc)
  case record x =>
      simp only [famObj] at h
      obtain ⟨fr, r, hfrest, hrx, hok, hcase⟩ := objRec_extract h
      obtain ⟨t, hrest, hsound⟩ := hfr fr hfrest
      have hreq : ∀ k : {k // k ∈ a.fields},
          Field.isReq ((gt k x).getD (.optional .never)) = Field.isReq (a.at k) := by
        intro k
        obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfm, Option.getD_some]
        exact hgtreq _ _ _ hfm
      have ihf : ∀ (k : {k // k ∈ a.fields}) (w : Value),
          AdmField ((gt k x).getD (.optional .never)) w
            = (AdmField (a.at k) w && Adm x w) := by
        intro k w
        obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfm, Option.getD_some]
        exact hgt _ _ _ hfm w
      have iht : ∀ w, Adm r w = (Adm t w && Adm x w) := hsound x r hrx
      have hnm : ∀ w : Value, (∀ keys gv, w ≠ .map keys gv) →
          Adm z w = (Adm (.object a) w && Adm (.record x) w) := by
        intro w hw
        have hrxv : Adm (.record x) w = false := by
          cases w with
          | map keys gv => exact absurd rfl (hw keys gv)
          | _ => rfl
        rw [show Adm (.object a) w = AdmBody a w from rfl, AdmBody_of_not_map hw, hrxv,
          Bool.and_self]
        rcases hcase with ⟨rfl, _⟩ | rfl
        · rfl
        · exact AdmBody_of_not_map hw
      cases v
      case map keys gv =>
        rw [show Adm (.object a) (.map keys gv) = AdmBody a (.map keys gv) from rfl,
            show Adm (.record x) (.map keys gv)
              = decide (∀ k : {k // k ∈ keys}, Adm x (gv k) = true) from rfl]
        rcases hcase with ⟨rfl, hnb⟩ | rfl
        · show (false : Bool) = _
          cases hA : AdmBody a (.map keys gv) with
          | false => rfl
          | true =>
            cases hR : decide (∀ k : {k // k ∈ keys}, Adm x (gv k) = true) with
            | false => rfl
            | true => exact absurd (isBottom_false_of_right hreq ihf hA hR) hnb
        · show AdmBody (.mk a.fields _ (.codec r)) (.map keys gv) = _
          rw [AdmBody_map, AdmBody_map]
          simp only [Body.fields_mk, Body.at_mk, Body.rest_mk, hrest]
          rw [valPresentT_of_isReq hreq, show AdmRest (.codec r) = some (Adm r) from rfl,
              show AdmRest (.codec t) = some (Adm t) from rfl, objAdmV_of_right ihf iht]
          simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
      all_goals exact hnm _ (fun _ _ hc => Value.noConfusion hc)
  case opaq l => simp [famObj] at h
  all_goals fam_never famObj

/-! ### The outer theorem. -/

/-- Two fields meet at the stronger mark, so the write bit is the join. -/
theorem isReq_Field_meet : ∀ {f fl fm : Field}, Field.meet f fl = some fm →
    Field.isReq fm = (Field.isReq f || Field.isReq fl) := by
  intro f fl fm h
  cases f <;> cases fl <;>
    simp only [Field.meet, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨tz, _, rfl⟩ := h <;> rfl

/-- …and a field met with a term keeps its own mark. -/
theorem isReq_Field_meetT : ∀ {f : Field} {y : Term} {fm : Field}, Field.meetT f y = some fm →
    Field.isReq fm = Field.isReq f := by
  intro f y fm h
  cases f <;> simp only [Field.meetT, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨tz, _, rfl⟩ := h <;> rfl

/-- The option companion is the plain map at the fixed partner. -/
theorem meetSL_eq (y : Term) : ∀ os, Term.meetSL os y = os.map (fun t => Term.meet t y)
  | [] => rfl
  | _ :: os => congrArg _ (meetSL_eq y os)

/-- A certified union distributes: every option meets, the bottoms drop, and the survivors
    carry the certificate. -/
theorem meet_union_of {os : List Term} {y z : Term}
    (h : Term.meet (.union os) y = some z) (hy : y ≠ .never) :
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
      rw [← meetSL_eq]
      exact hzs
    next => exact absurd hg (by simp)
  all_goals (intros; simp_all)

mutual
/-- **`Adm` is a homomorphism from the meet to conjunction.** Where two terms have a meet,
    the values it admits are exactly the values both admit. -/
theorem Adm_meet : ∀ x y z, Term.meet x y = some z → ∀ v, Adm z v = (Adm x v && Adm y v)
  | .never, _, _, h, _ => by
      simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm]
  | .held _ _ _, y, _, h, v => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm])
          | exact absurd h (by simp [Term.meet])
  | .legacy _ _, y, _, h, v => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm])
          | exact absurd h (by simp [Term.meet])
  | .custom _ _, y, _, h, v => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm])
          | exact absurd h (by simp [Term.meet])
  | .lazy _, y, _, h, v => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm])
          | exact absurd h (by simp [Term.meet])
  | .refine x p, y, _, h, v => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm]
      | _ =>
        simp only [Term.meet] at h
        split at h
        · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
          have ihw := Adm_meet x _ w hw v
          rw [Adm_refineOf]
          simp only [Adm, ihw]
          simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
        · exact absurd h (by simp)
  | .union os, y, _, h, v => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm]
      | _ =>
        obtain ⟨zs, hF, hco, hcz, rfl⟩ := meet_union_of h (by simp)
        rw [Adm_ofOptions hcz, AdmAny_filter_never,
          show Adm (.union _) v = selOptV (AdmSpecs _) v from rfl, selOptV_eq_AdmAny hco]
        exact AdmAny_meet v (Adm_meetL os _ _ hF)
  | .string, y, z, h, v => Adm_meetSRight Adm_famString y z h v
  | .number, y, z, h, v => Adm_meetSRight Adm_famNumber y z h v
  | .decimal, y, z, h, v => Adm_meetSRight Adm_famDecimal y z h v
  | .boolean, y, z, h, v => Adm_meetSRight Adm_famBoolean y z h v
  | .binary, y, z, h, v => Adm_meetSRight Adm_famBinary y z h v
  | .null, y, z, h, v => Adm_meetSRight Adm_famNull y z h v
  | .literal k lv, y, z, h, v => Adm_meetSRight (Adm_famLit k lv) y z h v
  | .set b, y, z, h, v => Adm_meetSRight (Adm_famSet b) y z h v
  | .opaq l, y, z, h, v => Adm_meetSRight (Adm_famOpaq l) y z h v
  | .array e, y, z, h, v =>
      Adm_meetSRight (Adm_famArr (fun t w hw => Adm_meet e t w hw)) y z h v
  | .record c, y, z, h, v =>
      Adm_meetSRight (Adm_famRec (fun t w hw => Adm_meet c t w hw)) y z h v
  | .tuple ts tl, y, z, h, v => by
      cases tl with
      | none =>
          exact Adm_meetSRight (Adm_famTup (Adm_meetSTs ts) (Or.inl ⟨rfl, rfl⟩)) y z h v
      | some t =>
          exact Adm_meetSRight (Adm_famTup (Adm_meetSTs ts)
            (Or.inr ⟨t, Term.meet t, rfl, rfl, fun u w hw => Adm_meet t u w hw⟩)) y z h v
  | .object (.mk fs f r), y, z, h, v => by
      cases r with
      | codec t =>
          exact Adm_meetSRight (Adm_famObj (a := .mk fs f (.codec t))
            (fun k fl fm hm w => Adm_Field_meet (f k) fl fm hm w)
            (fun _ _ _ hm => isReq_Field_meet hm)
            (fun k u fm hm w => Adm_Field_meetT (f k) u fm hm w)
            (fun _ _ _ hm => isReq_Field_meetT hm)
            (fun fr hfr => ⟨t, rfl, by
              simp only [Option.some.injEq] at hfr
              subst hfr
              exact fun u w hw => Adm_meet t u w hw⟩)) y z h v
      | drop =>
          exact Adm_meetSRight (Adm_famObj (a := .mk fs f .drop)
            (fun k fl fm hm w => Adm_Field_meet (f k) fl fm hm w)
            (fun _ _ _ hm => isReq_Field_meet hm)
            (fun k u fm hm w => Adm_Field_meetT (f k) u fm hm w)
            (fun _ _ _ hm => isReq_Field_meetT hm)
            (fun _ hfr => absurd hfr (by simp))) y z h v
      | refuse =>
          exact Adm_meetSRight (Adm_famObj (a := .mk fs f .refuse)
            (fun k fl fm hm w => Adm_Field_meet (f k) fl fm hm w)
            (fun _ _ _ hm => isReq_Field_meet hm)
            (fun k u fm hm w => Adm_Field_meetT (f k) u fm hm w)
            (fun _ _ _ hm => isReq_Field_meetT hm)
            (fun _ hfr => absurd hfr (by simp))) y z h v
termination_by structural x => x

/-- The union row's options, lifted pointwise at the fixed partner. -/
theorem Adm_meetL : ∀ (os : List Term) (y : Term) (zs : List Term),
    List.Forall₂ (fun t w => Term.meet t y = some w) os zs →
    List.Forall₂ (fun t w => ∀ u, Adm w u = (Adm t u && Adm y u)) os zs
  | [], _, _, h => by cases h; exact .nil
  | t :: ts, y, _, h => by
      cases h with
      | cons hh ht => exact .cons (fun u => Adm_meet t y _ hh u) (Adm_meetL ts y _ ht)
termination_by structural os => os

/-- Every position of a tuple carries the meet at that position. -/
theorem Adm_meetSTs : ∀ ts : List Term, List.Forall₂ AdmSound ts (Term.meetSTs ts)
  | [] => .nil
  | t :: ts => .cons (fun u w hw => Adm_meet t u w hw) (Adm_meetSTs ts)
termination_by structural ts => ts

/-- Two fields at one name admit what both admit, at the stronger mark. -/
theorem Adm_Field_meet : ∀ (f fl : Field) (fm : Field), Field.meet f fl = some fm →
    ∀ w, AdmField fm w = (AdmField f w && AdmField fl w)
  | .req x, .req y, _, h, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet x y tz hz w
  | .req x, .optional y, _, h, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet x y tz hz w
  | .optional x, .req y, _, h, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet x y tz hz w
  | .req x, .fallback y _, _, h, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet x y tz hz w
  | .fallback x _, .req y, _, h, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet x y tz hz w
  | .optional x, .optional y, _, h, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet x y tz hz w
  | .optional _, .fallback _ _, _, h, _ => by simp [Field.meet] at h
  | .fallback _ _, .optional _, _, h, _ => by simp [Field.meet] at h
  | .fallback _ _, .fallback _ _, _, h, _ => by simp [Field.meet] at h
termination_by structural f => f

/-- …and a field met with a record's term admits what both admit. -/
theorem Adm_Field_meetT : ∀ (f : Field) (y : Term) (fm : Field), Field.meetT f y = some fm →
    ∀ w, AdmField fm w = (AdmField f w && Adm y w)
  | .req x, y, _, h, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet x y tz hz w
  | .optional x, y, _, h, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet x y tz hz w
  | .fallback _ _, _, _, h, _ => by simp [Field.meetT] at h
termination_by structural f => f
end

end StructuralAdm

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

section StructuralWrites
set_option maxHeartbeats 1000000

/-! ## The member the meet names, structurally

The same three layers the homomorphism uses. The containers never read the recursion here:
`μSyn` of an `array`, a `tuple`, a `record` and an `object` is fixed by the constructor whatever
the payload meets to, so only the refinement and the union rows recurse. -/

/-- `fam` carries the member with one term fixed on the left, over the operands it is handed. -/
def WritesFam (x : Term) (fam : Term → Option Term) : Prop :=
  ∀ y z, Delegated y → fam y = some z → ∀ m : Member, μSyn z = some m →
    (∀ mx, μSyn x = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m)

mutual
/-- Every row that reads the right operand alone names the family's member. -/
theorem writes_meetSRight {x : Term} {fam : Term → Option Term} (hf : WritesFam x fam) :
    ∀ y z, meetSRight fam y = some z → ∀ m : Member, μSyn z = some m →
      (∀ mx, μSyn x = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m)
  | .never, _, h, _, hz => by
      simp only [meetSRight, Option.some.injEq] at h; subst h
      exact absurd hz (by simp [μSyn])
  | .held _ _ _, _, h, _, _ => by simp [meetSRight] at h
  | .legacy _ _, _, h, _, _ => by simp [meetSRight] at h
  | .custom _ _, _, h, _, _ => by simp [meetSRight] at h
  | .lazy _, _, h, _, _ => by simp [meetSRight] at h
  | .refine y p, _, h, m, hz => by
      simp only [meetSRight] at h
      split at h
      · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [μSyn_refineOf] at hz
        have ih := writes_meetSRight hf y w hw m hz
        exact ⟨ih.1, fun my hmy => ih.2 my (by simpa [μSyn] using hmy)⟩
      · exact absurd h (by simp)
  | .union os, _, h, m, hz => by
      obtain ⟨zs, hF, _, _, rfl⟩ := meetSRight_union h
      obtain ⟨w, hw, hwm⟩ := μSyn_ofOptions_mem hz
      obtain ⟨o, ho, hP⟩ :=
        forall₂_mem_right (writes_meetSRightL hf os zs hF) (List.mem_of_mem_filter hw)
      have ih := hP m hwm
      exact ⟨ih.1, fun my hmy => ih.2 my (μSyn_union_mem hmy o ho)⟩
  | .string, _, h, m, hz => hf .string _ trivial h m hz
  | .number, _, h, m, hz => hf .number _ trivial h m hz
  | .decimal, _, h, m, hz => hf .decimal _ trivial h m hz
  | .boolean, _, h, m, hz => hf .boolean _ trivial h m hz
  | .binary, _, h, m, hz => hf .binary _ trivial h m hz
  | .null, _, h, m, hz => hf .null _ trivial h m hz
  | .literal k lv, _, h, m, hz => hf (.literal k lv) _ trivial h m hz
  | .set b, _, h, m, hz => hf (.set b) _ trivial h m hz
  | .opaq l, _, h, m, hz => hf (.opaq l) _ trivial h m hz
  | .array e, _, h, m, hz => hf (.array e) _ trivial h m hz
  | .record c, _, h, m, hz => hf (.record c) _ trivial h m hz
  | .tuple ts tl, _, h, m, hz => hf (.tuple ts tl) _ trivial h m hz
  | .object b, _, h, m, hz => hf (.object b) _ trivial h m hz
termination_by structural y => y

/-- The union row's options, lifted pointwise. -/
theorem writes_meetSRightL {x : Term} {fam : Term → Option Term} (hf : WritesFam x fam) :
    ∀ os zs, List.Forall₂ (fun t w => meetSRight fam t = some w) os zs →
      List.Forall₂ (fun t w => ∀ m : Member, μSyn w = some m →
        (∀ mx, μSyn x = some mx → mx = m) ∧ (∀ my, μSyn t = some my → my = m)) os zs
  | [], _, h => by cases h; exact .nil
  | t :: ts, _, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun m hm => writes_meetSRight hf t _ hh m hm)
            (writes_meetSRightL hf ts _ ht)
termination_by structural os => os
end

/-- `string` names `S`, and so does every term it meets. -/
theorem writes_famString : WritesFam Term.string famString := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case literal k lv =>
      cases k <;> (try simp_all [famString, μSyn, Term.meetLit]) <;>
        (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (split at h))
      all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))
  all_goals (try simp_all [famString, μSyn, Term.meetLit])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- `number` names `N`, and so does every term it meets. -/
theorem writes_famNumber : WritesFam Term.number famNumber := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case literal k lv =>
      cases k <;> (try simp_all [famNumber, μSyn, Term.meetLit]) <;>
        (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (split at h))
      all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))
  all_goals (try simp_all [famNumber, μSyn, Term.meetLit])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- `decimal` names `N`, and so does every term it meets. -/
theorem writes_famDecimal : WritesFam Term.decimal famDecimal := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case literal k lv =>
      cases k <;> (try simp_all [famDecimal, μSyn, Term.meetLit]) <;>
        (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (split at h))
      all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))
  all_goals (try simp_all [famDecimal, μSyn, Term.meetLit])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- `boolean` names `BOOL`, and so does every term it meets. -/
theorem writes_famBoolean : WritesFam Term.boolean famBoolean := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case literal k lv =>
      cases k <;> (try simp_all [famBoolean, μSyn, Term.meetLit]) <;>
        (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (split at h))
      all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))
  all_goals (try simp_all [famBoolean, μSyn, Term.meetLit])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- `binary` names `B`, and so does every term it meets. -/
theorem writes_famBinary : WritesFam Term.binary famBinary := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case literal k lv =>
      cases k <;> (try simp_all [famBinary, μSyn, Term.meetLit]) <;>
        (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (split at h))
      all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))
  all_goals (try simp_all [famBinary, μSyn, Term.meetLit])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- `null` names `NULL`, and so does every term it meets. -/
theorem writes_famNull : WritesFam Term.null famNull := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case literal k lv =>
      cases k <;> (try simp_all [famNull, μSyn, Term.meetLit]) <;>
        (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (split at h))
      all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))
  all_goals (try simp_all [famNull, μSyn, Term.meetLit])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- A literal names its base's member, and so does every term it meets. -/
theorem writes_famLit (k : GroundKind) (lv : k.Carrier) :
    WritesFam (.literal k lv) (famLit k lv) := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case literal k' lv' =>
      cases k <;> cases k' <;> (try simp_all [famLit, μSyn, Term.meetLit, GroundKind.member])
      all_goals (try (split at h))
      all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))
  all_goals (cases k <;> (try simp_all [famLit, μSyn, Term.meetLit, GroundKind.member]))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- A set names its base's member, and so does every term it meets. -/
theorem writes_famSet (b : SetBase) : WritesFam (.set b) (famSet b) := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  all_goals (cases b <;> (try simp_all [famSet, μSyn, SetBase.member]))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- `opaque` names no member, so the pair agrees vacuously on the left. -/
theorem writes_famOpaq (l : Bool) : WritesFam (.opaq l) (famOpaq l) := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  all_goals (try simp_all [famOpaq, μSyn])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- An array names `L` whatever the element meets to. -/
theorem writes_famArr {f : Term → Option Term} {x' : Term} :
    WritesFam (.array x') (famArr f) := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case array e =>
      obtain ⟨w, _, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa [μSyn] using hz
  case tuple ts tl =>
      obtain ⟨vs, tll, rfl, _, _⟩ := famArr_tuple h
      rcases tupleOf_cases vs tll with hc | hc <;> rw [hc] at hz
      · exact absurd hz (by simp [μSyn])
      · simpa [μSyn] using hz
  all_goals (try simp_all [famArr, μSyn])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- A record names `M`, and an object it meets names `M` too. -/
theorem writes_famRec {f : Term → Option Term} {x' : Term} :
    WritesFam (.record x') (famRec f) := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case record c =>
      obtain ⟨w, _, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa [μSyn] using hz
  case object b =>
      obtain ⟨t, r, _, _, _, hc⟩ := recObj_extract (by simpa [famRec] using h)
      rcases hc with ⟨rfl, _⟩ | rfl
      · exact absurd hz (by simp [μSyn])
      · simpa [μSyn] using hz
  all_goals (try simp_all [famRec, μSyn])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- A tuple names `L`, and the bottom it can answer names none. -/
theorem writes_famTup {ts : List Term} {tl : Option Term}
    {fs : List (Term → Option Term)} {ftail : Option (Term → Option Term)} :
    WritesFam (.tuple ts tl) (famTup fs ftail) := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case array e =>
      simp only [famTup] at h
      split at h
      next vs tll _ _ =>
        simp only [Option.some.injEq] at h; subst h
        rcases tupleOf_cases vs tll with hc | hc <;> rw [hc] at hz
        · exact absurd hz (by simp [μSyn])
        · simpa [μSyn] using hz
      next => exact absurd h (by simp)
  case tuple us tail' =>
      simp only [famTup] at h
      split at h
      next =>
        split at h
        next vs tll _ _ =>
          simp only [Option.some.injEq] at h; subst h
          rcases tupleOf_cases vs tll with hc | hc <;> rw [hc] at hz
          · exact absurd hz (by simp [μSyn])
          · simpa [μSyn] using hz
        next => exact absurd h (by simp)
      next =>
        split at h
        next =>
          simp only [Option.some.injEq] at h; subst h
          exact absurd hz (by simp [μSyn])
        next => exact absurd h (by simp)
  case opaq l => simp [famTup] at h
  all_goals (try simp_all [famTup, μSyn])
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))

/-- An object names `M`, and the bottom it can answer names none. -/
theorem writes_famObj {a : Body} {g : {k // k ∈ a.fields} → Field → Option Field}
    {gt : {k // k ∈ a.fields} → Term → Option Field}
    {frest : Option (Term → Option Term)} :
    WritesFam (.object a) (famObj a g gt frest) := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case object b =>
      obtain ⟨r, _, hc⟩ := objObj_extract (by simpa [famObj] using h)
      rcases hc with ⟨rfl, _⟩ | ⟨_, _, _, ⟨rfl, _⟩ | rfl⟩
      · exact absurd hz (by simp [μSyn])
      · exact absurd hz (by simp [μSyn])
      · simpa [μSyn] using hz
  case record x =>
      obtain ⟨fr, r, _, _, _, hc⟩ := objRec_extract (by simpa [famObj] using h)
      rcases hc with ⟨rfl, _⟩ | rfl
      · exact absurd hz (by simp [μSyn])
      · simpa [μSyn] using hz
  all_goals (try simp_all [famObj, μSyn])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))


mutual
/-- **Where the meet names a member, any member a factor names is that one.** `μSyn z` is a
    hypothesis and not a conclusion, because the converse fails twice: a bottom names no member,
    so two factors naming different members meet at a term that names none, and a refinement over
    the bottom is not the bottom, so excluding `never` does not repair it. -/
theorem meet_writes : ∀ x y z, Term.meet x y = some z → ∀ m : Member, μSyn z = some m →
    (∀ mx, μSyn x = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m)
  | .never, _, _, h, _, hz => by
      simp only [Term.meet, Option.some.injEq] at h; subst h
      exact absurd hz (by simp [μSyn])
  | .held _ _ _, y, _, h, _, hz => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h
             exact absurd hz (by simp [μSyn]))
          | exact absurd h (by simp [Term.meet])
  | .legacy _ _, y, _, h, _, hz => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h
             exact absurd hz (by simp [μSyn]))
          | exact absurd h (by simp [Term.meet])
  | .custom _ _, y, _, h, _, hz => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h
             exact absurd hz (by simp [μSyn]))
          | exact absurd h (by simp [Term.meet])
  | .lazy _, y, _, h, _, hz => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h
             exact absurd hz (by simp [μSyn]))
          | exact absurd h (by simp [Term.meet])
  | .refine x p, y, _, h, m, hz => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h
          exact absurd hz (by simp [μSyn])
      | _ =>
        simp only [Term.meet] at h
        split at h
        · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
          rw [μSyn_refineOf] at hz
          have ih := meet_writes x _ w hw m hz
          exact ⟨fun mx hmx => ih.1 mx (by simpa [μSyn] using hmx), ih.2⟩
        · exact absurd h (by simp)
  | .union os, y, _, h, m, hz => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h
          exact absurd hz (by simp [μSyn])
      | _ =>
        obtain ⟨zs, hF, _, _, rfl⟩ := meet_union_of h (by simp)
        obtain ⟨w, hw, hwm⟩ := μSyn_ofOptions_mem hz
        obtain ⟨o, ho, hP⟩ :=
          forall₂_mem_right (writes_meetL os _ zs hF) (List.mem_of_mem_filter hw)
        have ih := hP m hwm
        exact ⟨fun mx hmx => ih.1 mx (μSyn_union_mem hmx o ho), ih.2⟩
  | .string, y, z, h, m, hz => writes_meetSRight writes_famString y z h m hz
  | .number, y, z, h, m, hz => writes_meetSRight writes_famNumber y z h m hz
  | .decimal, y, z, h, m, hz => writes_meetSRight writes_famDecimal y z h m hz
  | .boolean, y, z, h, m, hz => writes_meetSRight writes_famBoolean y z h m hz
  | .binary, y, z, h, m, hz => writes_meetSRight writes_famBinary y z h m hz
  | .null, y, z, h, m, hz => writes_meetSRight writes_famNull y z h m hz
  | .literal k lv, y, z, h, m, hz => writes_meetSRight (writes_famLit k lv) y z h m hz
  | .set b, y, z, h, m, hz => writes_meetSRight (writes_famSet b) y z h m hz
  | .opaq l, y, z, h, m, hz => writes_meetSRight (writes_famOpaq l) y z h m hz
  | .array _, y, z, h, m, hz => writes_meetSRight writes_famArr y z h m hz
  | .record _, y, z, h, m, hz => writes_meetSRight writes_famRec y z h m hz
  | .tuple ts tl, y, z, h, m, hz => by
      cases tl with
      | none =>
          exact writes_meetSRight (writes_famTup (ts := ts) (tl := none)
            (fs := Term.meetSTs ts) (ftail := none)) y z h m hz
      | some t =>
          exact writes_meetSRight (writes_famTup (ts := ts) (tl := some t)
            (fs := Term.meetSTs ts) (ftail := some (Term.meet t))) y z h m hz
  | .object (.mk fs f r), y, z, h, m, hz => by
      cases r with
      | codec t =>
          exact writes_meetSRight (writes_famObj (a := .mk fs f (.codec t))
            (g := fun k => Field.meet (f k)) (gt := fun k => Field.meetT (f k))
            (frest := some (Term.meet t))) y z h m hz
      | drop =>
          exact writes_meetSRight (writes_famObj (a := .mk fs f .drop)
            (g := fun k => Field.meet (f k)) (gt := fun k => Field.meetT (f k))
            (frest := none)) y z h m hz
      | refuse =>
          exact writes_meetSRight (writes_famObj (a := .mk fs f .refuse)
            (g := fun k => Field.meet (f k)) (gt := fun k => Field.meetT (f k))
            (frest := none)) y z h m hz
termination_by structural x => x

/-- The union row's options, lifted pointwise at the fixed partner. -/
theorem writes_meetL : ∀ (os : List Term) (y : Term) (zs : List Term),
    List.Forall₂ (fun t w => Term.meet t y = some w) os zs →
    List.Forall₂ (fun t w => ∀ m : Member, μSyn w = some m →
      (∀ mx, μSyn t = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m)) os zs
  | [], _, _, h => by cases h; exact .nil
  | t :: ts, y, _, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun m hm => meet_writes t y _ hh m hm) (writes_meetL ts y _ ht)
termination_by structural os => os
end

end StructuralWrites

/-- **The converse is false, and a bottom is why.** Two factors naming different members meet at
    the bottom, which names none, so a theorem concluding `mx = my` from the factors alone fails
    here. -/
example : Term.meet (.literal .boolean true) Term.string = some .never := by rfl

example : μSyn Term.never = none := rfl

/-- The refinement that used to be the second witness is now the bottom, because the meet
    normalises: a refinement over the bottom holds nothing, so `Term.refineOf` answers the bottom.
    The hypothesis form is still the right one — the first witness needs no wrapper — and this
    example is kept because it pins the normalisation at the row that motivated it. -/
example : Term.meet (.refine .string (.members .string ⟨{"1"}, Finset.singleton_nonempty _⟩))
    .boolean = some .never := by rfl


/-! ## The homomorphism on the read side

`AdmA_meet` and `denote_meet_p` are proved together, and the pairing is forced.
`AdmA (.refine t p) a` is `AdmA t a && refineReads t p.eval a`, and `refineReads` asks the
predicate of what `t` decodes `a` to, so the refinement rows reduce to the reading agreement.
The agreement is unprovable alone: at a row that answers the bottom the meet reads nothing
where a factor reads something, and what rules that row out is the homomorphism's own content
there. The value side needs no such pairing, because `Adm (.refine t p) v` shows the predicate
the value itself.
-/


/-- A `Bool`-valued filter, compared on the set's own names. Mathlib's `Finset.filter_congr`
    reaches `Classical.choice`; a filter whose predicate is already a `Bool` needs no choice. -/
theorem filter_congr_on {S : Finset Name} {p q : Name → Bool} (h : ∀ k ∈ S, p k = q k) :
    S.filter (p ·) = S.filter (q ·) := by
  ext k
  simp only [Finset.mem_filter]
  exact ⟨fun hk => ⟨hk.1, (h k hk.1) ▸ hk.2⟩, fun hk => ⟨hk.1, (h k hk.1).symm ▸ hk.2⟩⟩

/-- …a filter that keeps nothing is empty… -/
theorem filter_eq_empty_on {S : Finset Name} {p : Name → Bool} (h : ∀ k ∈ S, p k = false) :
    S.filter (p ·) = ∅ := by
  ext k
  refine ⟨fun hk => ?_, fun hk => absurd hk (Finset.notMem_empty k)⟩
  obtain ⟨hs, hp⟩ := Finset.mem_filter.mp hk
  rw [h k hs] at hp
  exact Bool.noConfusion hp

/-- …and one that keeps everything is the set. -/
theorem filter_eq_self_on {S : Finset Name} {p : Name → Bool} (h : ∀ k ∈ S, p k = true) :
    S.filter (p ·) = S := by
  ext k
  simp only [Finset.mem_filter]
  exact ⟨fun hk => hk.1, fun hk => ⟨hk, h k hk⟩⟩

/-- `AdmA` at an object is its body's row. -/
theorem AdmA_object (b : Body) (a : Attr) : AdmA (.object b) a = AdmABody b a := rfl

/-- …and at a record, the row of every entry the map carries. -/
theorem AdmA_record (x : Term) (keys : Finset Name) (g : {k // k ∈ keys} → Attr) :
    AdmA (.record x) (.m keys g) = decide (∀ k : {k // k ∈ keys}, AdmA x (g k) = true) := rfl

/-- A literal table's lookup at a declared name. `MapOf.at_of_mem` says the same for an
    abstract table, and its `m.2 k` does not reduce when the table is written out, which is what
    the rows below need. -/
theorem MapOf.at_mk_pos {α : Type} {S : Finset Name} {f : {k // k ∈ S} → α} {k : Name}
    (h : k ∈ S) : MapOf.at ⟨S, f⟩ k = some (f ⟨k, h⟩) := dif_pos h

/-- …and at an undeclared name it answers nothing. -/
theorem MapOf.at_of_not_mem {α : Type} {m : MapOf α} {k : Name} (h : k ∉ m.1) :
    m.at k = none := dif_neg h

/-- An entry at a declared name goes through that name's field… -/
theorem entryCodec_mk_pos {S : Finset Name} {f : {k // k ∈ S} → FieldSem} {rc? : Option Codec}
    {k : Name} (h : k ∈ S) : entryCodec ⟨S, f⟩ rc? k = some (f ⟨k, h⟩).codec := by
  rw [entryCodec, MapOf.at_mk_pos h]

/-- …and at an undeclared one through the rest policy's. -/
theorem entryCodec_mk_neg {S : Finset Name} {f : {k // k ∈ S} → FieldSem} {rc? : Option Codec}
    {k : Name} (h : k ∉ S) : entryCodec ⟨S, f⟩ rc? k = rc? := by
  rw [entryCodec, MapOf.at_of_not_mem (m := ⟨S, f⟩) h]

/-- The refusing `opaque` reads no stored numeral, which is the row the `number` pair turns
    on. -/
theorem opaq_p_num_false (n : Nat) (x : WFNumeral) : (opaqCodec n false).p (.n x) = none := by
  cases n with
  | zero => rfl
  | succ m => rw [opaqCodec_p_n]; rfl

/-- A set over a base that reads nothing reads nothing. -/
theorem decSet_none_of_refuse {α : Type} (c : Codec) (inj : α → Attr) (S : NEFinset α)
    (h : ∀ x, c.p (inj x) = none) : decSet c inj S = none := by
  obtain ⟨x0, hx0⟩ := S.2
  have key : ∀ {β : Type} [DecidableEq β] (out : Value → Option β),
      neSetImage (fun x => (c.p (inj x)).bind out) S = none := by
    intro β _ out
    cases hs : setImage (fun x => (c.p (inj x)).bind out) S.1 with
    | none => exact neSetImage_none hs
    | some T => exact absurd (setImage_some hs x0 hx0) (by rw [h x0]; exact fun hc => Bool.noConfusion hc)
  unfold decSet
  rw [key, key, key]
  rfl

/-- Two codecs that read a set's members alike give the set one reading. -/
theorem decSet_congr_p {α : Type} (c d : Codec) (inj : α → Attr) (S : NEFinset α)
    (h : ∀ x, c.p (inj x) = d.p (inj x)) : decSet c inj S = decSet d inj S := by
  unfold decSet
  rw [neSetImage_congr (f := fun x => (c.p (inj x)).bind vStr)
        (g := fun x => (d.p (inj x)).bind vStr) (fun x _ => by rw [h x]),
      neSetImage_congr (f := fun x => (c.p (inj x)).bind vNum)
        (g := fun x => (d.p (inj x)).bind vNum) (fun x _ => by rw [h x]),
      neSetImage_congr (f := fun x => (c.p (inj x)).bind vBin)
        (g := fun x => (d.p (inj x)).bind vBin) (fun x _ => by rw [h x])]

/-- The two policies read a stored string alike: only the numeral row separates them. -/
theorem opaq_p_s_lossy (m : Nat) (s : String) :
    (opaqCodec m false).p (.s s) = (opaqCodec m true).p (.s s) := by
  cases m with
  | zero => rfl
  | succ k => rw [opaqCodec_p_s, opaqCodec_p_s]

/-- …and stored bytes alike, for the same reason. -/
theorem opaq_p_b_lossy (m : Nat) (b : Bytes) :
    (opaqCodec m false).p (.b b) = (opaqCodec m true).p (.b b) := by
  cases m with
  | zero => rfl
  | succ k => rw [opaqCodec_p_b, opaqCodec_p_b]

/-- **The refusing policy is below the lossy one on the read side too.** -/
theorem opaq_p_mono : ∀ (n : Nat) (a : Attr) (v : Value),
    (opaqCodec n false).p a = some v → (opaqCodec n true).p a = some v := by
  intro n
  induction n with
  | zero => intro a v hh; exact nomatch hh
  | succ m ihm =>
    intro a v hh
    cases a with
    | s s => rw [opaqCodec_p_s] at hh ⊢; exact hh
    | bool b => rw [opaqCodec_p_bool] at hh ⊢; exact hh
    | b b => rw [opaqCodec_p_b] at hh ⊢; exact hh
    | null => rw [opaqCodec_p_null] at hh ⊢; exact hh
    | n x => rw [opaq_p_num_false] at hh; exact nomatch hh
    | ss S =>
      rw [opaqCodec_p_ss] at hh ⊢
      show (setCodec (opaqCodec m true)).p (.ss S) = some v
      show decSet (opaqCodec m true) Attr.s S = some v
      rw [← decSet_congr_p (opaqCodec m false) (opaqCodec m true) Attr.s S
            (fun x => opaq_p_s_lossy m x)]
      exact hh
    | bs S =>
      rw [opaqCodec_p_bs] at hh ⊢
      show decSet (opaqCodec m true) Attr.b S = some v
      rw [← decSet_congr_p (opaqCodec m false) (opaqCodec m true) Attr.b S
            (fun x => opaq_p_b_lossy m x)]
      exact hh
    | ns S =>
      rw [opaqCodec_p_ns] at hh
      rw [show (setCodec (opaqCodec m false)).p (.ns S)
            = decSet (opaqCodec m false) Attr.n S from rfl,
          decSet_none_of_refuse _ _ _ (opaq_p_num_false m)] at hh
      exact nomatch hh
    | l as =>
      rw [opaqCodec_p_l] at hh ⊢
      show ((traverse (opaqCodec m true).p as).map Value.arr) = some v
      replace hh : ((traverse (opaqCodec m false).p as).map Value.arr) = some v := hh
      obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp hh
      rw [traverse_mono (fun x b hb => ihm x b hb) hvs]
      rfl
    | m keys f =>
      rw [opaqCodec_p_m] at hh ⊢
      show ((funImage (fun k => (opaqCodec m true).p (f k))).map (Value.map keys)) = some v
      replace hh : ((funImage (fun k => (opaqCodec m false).p (f k))).map (Value.map keys))
          = some v := hh
      obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hh
      rw [funImage_mono (fun k b hb => ihm _ b hb) hg]
      rfl

/-- A body reads nothing that is not a map. -/
theorem AdmABody_of_not_m {c : Body} {a : Attr} (h : ∀ keys g, a ≠ .m keys g) :
    AdmABody c a = false := by
  cases c with
  | mk fields fld rest =>
    cases a with
    | m keys g => exact absurd rfl (h keys g)
    | _ => rfl

/-- The rows of a term list are as many as the terms. -/
theorem AdmAList_length (ts : List Term) : (AdmAList ts).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ihx => simp only [AdmAList, List.length_cons, ihx]

/-- A list reads under the meet exactly where it reads under both factors. -/
theorem allPA_and {p q r : AP} (h : ∀ a, r a = (p a && q a)) (xs : List Attr) :
    allPA r xs = (allPA p xs && allPA q xs) := by
  induction xs with
  | nil => simp [allPA]
  | cons a as ihx => simp only [allPA, h, ihx]; cases p a <;> cases q a <;> simp

/-- Two terms whose occupancies are disjoint share no attribute, so their conjunction is
    the bottom. This closes every row that answers `never` because the two read different `Attr`
    constructors. -/
theorem AdmA_and_false {x y : Term} (h : Orth1 x y = true) (a : Attr) :
    (AdmA x a && AdmA y a) = false := by
  cases hx : AdmA x a with
  | false => simp
  | true =>
    cases hy : AdmA y a with
    | false => simp
    | true =>
      have h2 := occA_disjoint_of_Orth1 h (occA_sound x a hx)
      rw [occA_sound y a hy] at h2
      exact absurd h2 (by simp)

/-- `opaque` reads an attribute exactly where its codec at that depth answers. -/
theorem AdmA_opaq_eq (l : Bool) (a : Attr) :
    AdmA (.opaq l) a = ((opaqCodec (Attr.depth a) l).p a).isSome := rfl

/-- It reads every stored string, -/
theorem AdmA_opaq_str (l : Bool) (s : String) : AdmA (.opaq l) (.s s) = true := by
  rw [AdmA_opaq_eq, show Attr.depth (.s s) = 0 + 1 from rfl, opaqCodec_p_s]
  simp [stringCodec]

/-- …every stored boolean, -/
theorem AdmA_opaq_bool (l : Bool) (b : Bool) : AdmA (.opaq l) (.bool b) = true := by
  rw [AdmA_opaq_eq, show Attr.depth (.bool b) = 0 + 1 from rfl, opaqCodec_p_bool]
  simp [booleanCodec]

/-- …every stored byte string, -/
theorem AdmA_opaq_bin (l : Bool) (b : Bytes) : AdmA (.opaq l) (.b b) = true := by
  rw [AdmA_opaq_eq, show Attr.depth (.b b) = 0 + 1 from rfl, opaqCodec_p_b]
  simp [binaryCodec]

/-- …and the stored null, under either policy. -/
theorem AdmA_opaq_null (l : Bool) : AdmA (.opaq l) .null = true := by
  rw [AdmA_opaq_eq, show Attr.depth Attr.null = 0 + 1 from rfl, opaqCodec_p_null]
  simp [nullCodec]

-- the numeric read row, mirror of `Adm_opaq_num`
/-- The numeral is the one row the policy decides: the refusing `opaque` reads none. -/
theorem AdmA_opaq_num (l : Bool) (x : WFNumeral) :
    AdmA (.opaq l) (.n x) = (l && ((numberCodec.p (.n x)).isSome)) := by
  show ((opaqCodec (Attr.depth (.n x)) l).p (.n x)).isSome = _
  rw [show Attr.depth (.n x) = 0 + 1 from rfl, opaqCodec_p_n]
  cases l <;> simp [Codec.empty]

/-- A tuple with no tail pins the length of the wire list it reads. -/
theorem alignPA_none_length : ∀ {Ps : List AP} {as : List Attr},
    alignPA Ps none as = true → as.length = Ps.length := by
  intro Ps
  induction Ps with
  | nil => intro as h; cases as with
    | nil => rfl
    | cons _ _ => simp [alignPA] at h
  | cons p Ps' ihp =>
    intro as h
    cases as with
    | nil => simp [alignPA] at h
    | cons w as' =>
      simp only [alignPA, Bool.and_eq_true] at h
      simp [ihp h.2]

/-- An array against a tuple: every declared position and the tail meet the array's element
    row, so the aligned answer is the conjunction. -/
theorem alignPA_meet_all {P : AP} :
    ∀ {Ps Qs : List AP}, List.Forall₂ (fun p q => ∀ a, q a = (p a && P a)) Ps Qs →
    ∀ {pt qt : Option AP},
      (pt = none ∧ qt = none) ∨
        (∃ p q, pt = some p ∧ qt = some q ∧ ∀ a, q a = (p a && P a)) →
    ∀ as, alignPA Qs qt as = (allPA P as && alignPA Ps pt as) := by
  intro Ps Qs hPQ pt qt htl as
  induction as generalizing Ps Qs with
  | nil =>
    cases hPQ with
    | nil => rcases htl with ⟨rfl, rfl⟩ | ⟨p, q, rfl, rfl, _⟩ <;> simp [alignPA, allPA]
    | cons _ _ => simp [alignPA, allPA]
  | cons w as ihw =>
    cases hPQ with
    | nil =>
      rcases htl with ⟨rfl, rfl⟩ | ⟨p, q, rfl, rfl, hpq⟩
      · simp [alignPA, allPA]
      · simp only [alignPA, allPA, hpq, ihw .nil]
        simp [Bool.and_assoc, Bool.and_left_comm]
    | cons hpq hrest =>
      simp only [alignPA, allPA, hpq, ihw hrest]
      simp [Bool.and_assoc, Bool.and_left_comm]

/-- Two tuples of one arity: the positions meet positionwise and the tails meet. -/
theorem alignPA_meet_zip :
    ∀ {Ps Qs Rs : List AP},
      List.Forall₂ (fun (pq : AP × AP) r => ∀ a, r a = (pq.1 a && pq.2 a)) (Ps.zip Qs) Rs →
      Ps.length = Qs.length →
    ∀ {pt qt rt : Option AP},
      ((pt = none ∧ qt = none ∧ rt = none) ∨
        ∃ p q r, pt = some p ∧ qt = some q ∧ rt = some r ∧ ∀ a, r a = (p a && q a)) →
    ∀ as, alignPA Rs rt as = (alignPA Ps pt as && alignPA Qs qt as) := by
  intro Ps Qs Rs hF hlen pt qt rt htl as
  induction as generalizing Ps Qs Rs with
  | nil =>
    cases Ps with
    | nil =>
      cases Qs with
      | nil =>
        cases hF
        rcases htl with ⟨rfl, rfl, rfl⟩ | ⟨p, q, r, rfl, rfl, rfl, _⟩ <;> simp [alignPA]
      | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons p Ps' =>
      cases Qs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons q Qs' =>
        rw [List.zip_cons_cons] at hF
        cases hF with
        | cons _ _ => simp [alignPA]
  | cons a as ihw =>
    cases Ps with
    | nil =>
      cases Qs with
      | nil =>
        cases hF
        rcases htl with ⟨rfl, rfl, rfl⟩ | ⟨p, q, r, rfl, rfl, rfl, hr⟩
        · simp [alignPA]
        · simp only [alignPA, hr, ihw (Ps := []) (Qs := []) .nil rfl]
          simp [Bool.and_assoc, Bool.and_left_comm]
      | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons p Ps' =>
      cases Qs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons q Qs' =>
        rw [List.zip_cons_cons] at hF
        cases hF with
        | cons hr hrest =>
          simp only [alignPA, hr, ihw hrest (by simpa using hlen)]
          simp [Bool.and_assoc, Bool.and_left_comm]

/-- Whether a field's name must be present for a READ. `fallback` reads to its stand-in, so it
    need not be; `Field.isReq` is the write side's answer and counts it. -/
def Field.isReqA : Field → Bool
  | .req _ => true
  | _ => false

/-- `reqPresentT` in the form the object row uses: a declared name that must be read is
    present. -/
theorem reqPresentT_req (fields : Finset Name) (fld : {k // k ∈ fields} → Field)
    (keys : Finset Name) :
    reqPresentT fields fld keys
      = decide (∀ k : {k // k ∈ fields}, Field.isReqA (fld k) = true → k.1 ∈ keys) := by
  unfold reqPresentT
  refine decide_eq_decide.mpr ⟨fun hh k hreq => ?_, fun hh k => ?_⟩
  · have hk := hh k
    cases hf : fld k with
    | req t => rw [hf] at hk; exact of_decide_eq_true hk
    | optional t => rw [hf] at hreq; exact absurd hreq (by simp [Field.isReqA])
    | fallback t d => rw [hf] at hreq; exact absurd hreq (by simp [Field.isReqA])
  · cases hf : fld k with
    | req t => exact decide_eq_true (hh k (by rw [hf]; rfl))
    | optional t => rfl
    | fallback t d => rfl

/-- The declared set is the intersection and the required set the union, which is what the two
    presence tests conjoin to. -/
theorem reqPresentT_of_bodies {a b : Body} {F : {k // k ∈ Body.shared a b} → Field}
    (hab : Body.reqShared a b = true) (hba : Body.reqShared b a = true)
    (hisreqA : ∀ k, Field.isReqA (F k)
      = (Field.isReqA (a.at ⟨k.1, Body.mem_shared_left k.2⟩)
         || Field.isReqA (b.at ⟨k.1, Body.mem_shared_right k.2⟩)))
    (keys : Finset Name) :
    reqPresentT (Body.shared a b) F keys
      = (reqPresentT a.fields a.at keys && reqPresentT b.fields b.at keys) := by
  rw [reqPresentT_req, reqPresentT_req, reqPresentT_req, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  unfold Body.reqShared at hab hba
  have hA := of_decide_eq_true hab
  have hB := of_decide_eq_true hba
  constructor
  · intro hs
    refine ⟨fun k hreq => ?_, fun k hreq => ?_⟩
    · have hr : Field.isReq (a.at k) = true := by
        cases hf : a.at k with
        | req t => rfl
        | optional t => rw [hf] at hreq; exact absurd hreq (by simp [Field.isReqA])
        | fallback t d => rw [hf] at hreq; exact absurd hreq (by simp [Field.isReqA])
      have hk : k.1 ∈ Body.shared a b := mem_shared_iff.mpr ⟨k.2, hA k hr⟩
      refine hs ⟨k.1, hk⟩ ?_
      rw [hisreqA ⟨k.1, hk⟩, hreq, Bool.true_or]
    · have hr : Field.isReq (b.at k) = true := by
        cases hf : b.at k with
        | req t => rfl
        | optional t => rw [hf] at hreq; exact absurd hreq (by simp [Field.isReqA])
        | fallback t d => rw [hf] at hreq; exact absurd hreq (by simp [Field.isReqA])
      have hk : k.1 ∈ Body.shared a b := mem_shared_iff.mpr ⟨hB k hr, k.2⟩
      refine hs ⟨k.1, hk⟩ ?_
      rw [hisreqA ⟨k.1, hk⟩, hreq, Bool.or_true]
  · rintro ⟨hA', hB'⟩ k hreq
    rw [hisreqA k, Bool.or_eq_true] at hreq
    rcases hreq with hr | hr
    · exact hA' ⟨k.1, Body.mem_shared_left k.2⟩ hr
    · exact hB' ⟨k.1, Body.mem_shared_right k.2⟩ hr


/-- A quantified conjunction splits. The value side's twin takes `Bool` predicates; the read
    side's rows are a `keepT` guard implying an entry, so the congruence has to be at `Prop`. -/
theorem decide_forall_and_prop {α : Sort*} {P Q R : α → Prop}
    [Decidable (∀ k, R k)] [Decidable (∀ k, P k)] [Decidable (∀ k, Q k)]
    (h : ∀ k, (R k ↔ (P k ∧ Q k))) :
    decide (∀ k, R k) = (decide (∀ k, P k) && decide (∀ k, Q k)) := by
  simp only [h, forall_and]
  simp

/-- A name one body declares and the other does not forces the other to `refuse`: under
    `drop` the certificate would have made the declared sets equal. -/
theorem rest_refuse_of_dropFits {a b : Body} {r : Rest}
    (hr : Rest.merge a.rest b.rest = some r) (hb : Body.dropFits b a = true)
    {k : Name} (hka : k ∈ a.fields) (hkb : k ∉ b.fields) : b.rest = .refuse := by
  unfold Body.dropFits at hb
  cases hbr : b.rest with
  | drop => rw [hbr] at hb; exact absurd (of_decide_eq_true hb k hka) hkb
  | refuse => rfl
  | codec t => rw [hbr] at hr; cases har : a.rest <;> rw [har] at hr <;> simp [Rest.merge] at hr

/-- The merged rest is `drop` exactly where both are. -/
theorem merge_eq_drop_iff {ra rb r : Rest} (hr : Rest.merge ra rb = some r) :
    r = .drop ↔ (ra = .drop ∧ rb = .drop) := by
  cases ra <;> cases rb <;> simp_all [Rest.merge]

/-- `Rest.merge` reads its two policies alike. -/
theorem merge_comm (ra rb : Rest) : Rest.merge ra rb = Rest.merge rb ra := by
  cases ra <;> cases rb <;> rfl

/-- A `refuse` on either side merges to `refuse`. -/
theorem merge_refuse_of_left {ra rb r : Rest} (hr : Rest.merge ra rb = some r)
    (h : rb = .refuse) : r = .refuse := by
  cases ra <;> rw [h] at hr <;> simp_all [Rest.merge]

/-- Every kept entry goes through both bodies' fields, a shared name through the meet. -/
theorem objAdmA_of_bodies {a b : Body} {r : Rest} {F : {k // k ∈ Body.shared a b} → Field}
    (hr : Rest.merge a.rest b.rest = some r)
    (hda : Body.dropFits a b = true) (hdb : Body.dropFits b a = true)
    (ihf : ∀ (k : {k // k ∈ Body.shared a b}) (c : Attr),
      AdmAField (F k) c
        = (AdmAField (a.at ⟨k.1, Body.mem_shared_left k.2⟩) c
            && AdmAField (b.at ⟨k.1, Body.mem_shared_right k.2⟩) c))
    (keys : Finset Name) (g : {k // k ∈ keys} → Attr) :
    objAdmA ⟨Body.shared a b, fun k => AdmAField (F k)⟩ (AdmARest r)
        (keepT r (Body.shared a b)) keys g
      = (objAdmA ⟨a.fields, fun k => AdmAField (a.at k)⟩ (AdmARest a.rest)
           (keepT a.rest a.fields) keys g
         && objAdmA ⟨b.fields, fun k => AdmAField (b.at k)⟩ (AdmARest b.rest)
           (keepT b.rest b.fields) keys g) := by
  have hnc : ∀ t, a.rest ≠ .codec t := by
    intro t ht; rw [ht] at hr; simp [Rest.merge] at hr
  have hnc' : ∀ t, b.rest ≠ .codec t := by
    intro t ht; rw [ht] at hr; cases har : a.rest <;> rw [har] at hr <;> simp [Rest.merge] at hr
  have hrestA : AdmARest a.rest = none := by
    cases har : a.rest with
    | drop => rfl | refuse => rfl | codec t => exact absurd har (hnc t)
  have hrestB : AdmARest b.rest = none := by
    cases hbr : b.rest with
    | drop => rfl | refuse => rfl | codec t => exact absurd hbr (hnc' t)
  have hrestR : AdmARest r = none := by
    cases hrr : r with
    | drop => rfl | refuse => rfl
    | codec t =>
      exfalso; cases har : a.rest <;> cases hbr : b.rest <;>
        rw [har, hbr] at hr <;> simp [Rest.merge, hrr] at hr
  simp only [objAdmA, entryPA, MapOf.at, hrestA, hrestB, hrestR]
  refine decide_forall_and_prop (fun k => ?_)
  by_cases hk : k.1 ∈ Body.shared a b
  · have ha := Body.mem_shared_left hk
    have hb := Body.mem_shared_right hk
    have hkr : keepT r (Body.shared a b) k.1 = true := by
      cases hrr : r with
      | drop => simp [keepT, hk]
      | refuse => rfl
      | codec t => simp [keepT]
    have hkA : keepT a.rest a.fields k.1 = true := by
      cases har : a.rest with
      | drop => simp [keepT, ha] | refuse => rfl | codec t => simp [keepT]
    have hkB : keepT b.rest b.fields k.1 = true := by
      cases hbr : b.rest with
      | drop => simp [keepT, hb] | refuse => rfl | codec t => simp [keepT]
    simp only [hkr, hkA, hkB, dif_pos hk, dif_pos ha, dif_pos hb, true_implies,
      ihf ⟨k.1, hk⟩ (g k), Bool.and_eq_true]
  · have hnab : ¬ (k.1 ∈ a.fields ∧ k.1 ∈ b.fields) := fun hh => hk (mem_shared_iff.mpr hh)
    by_cases ha : k.1 ∈ a.fields
    · have hb : k.1 ∉ b.fields := fun hh => hnab ⟨ha, hh⟩
      have hbref : b.rest = .refuse := rest_refuse_of_dropFits hr hdb ha hb
      have hrref : r = .refuse := merge_refuse_of_left hr hbref
      simp only [hrref, hbref, keepT, dif_neg hk, dif_neg hb, true_implies]
      simp
    · by_cases hb : k.1 ∈ b.fields
      · have hrc : Rest.merge b.rest a.rest = some r := by rw [merge_comm]; exact hr
        have haref : a.rest = .refuse := rest_refuse_of_dropFits hrc hda hb ha
        have hrref : r = .refuse := merge_refuse_of_left hrc haref
        simp only [hrref, haref, keepT, dif_neg hk, dif_neg ha, true_implies]
        simp
      · cases har : a.rest with
        | drop =>
          cases hbr : b.rest with
          | drop =>
            have hrd : r = .drop := (merge_eq_drop_iff hr).mpr ⟨har, hbr⟩
            simp only [hrd, keepT, decide_eq_true_eq]
            simp [hk, ha, hb]
          | refuse =>
            have hrref : r = .refuse := merge_refuse_of_left hr hbr
            simp only [hrref, keepT, dif_neg hk, dif_neg hb, true_implies]
            simp
          | codec t => exact absurd hbr (hnc' t)
        | refuse =>
          have hrref : r = .refuse :=
            merge_refuse_of_left (by rw [merge_comm]; exact hr) har
          simp only [hrref, keepT, dif_neg hk, dif_neg ha, true_implies]
          simp
        | codec t => exact absurd har (hnc t)


/-- The two policies meet at their conjunction, which is what makes the `opaque` pair a row
    rather than a refusal. -/
theorem AdmA_opaq_and (l l2 : Bool) (a : Attr) :
    AdmA (.opaq (l && l2)) a = (AdmA (.opaq l) a && AdmA (.opaq l2) a) := by
  rw [AdmA_opaq_eq, AdmA_opaq_eq, AdmA_opaq_eq]
  cases hf : (opaqCodec (Attr.depth a) false).p a with
  | none => cases l <;> cases l2 <;> simp [hf]
  | some v =>
    have ht := opaq_p_mono _ a v hf
    cases l <;> cases l2 <;> simp [hf, ht]

/-- A declared name that must be read is a name the map carries. -/
theorem mem_keys_of_req {fields : Finset Name} {fld : {k // k ∈ fields} → Field}
    {keys : Finset Name} (hv : reqPresentT fields fld keys = true) {k : {k // k ∈ fields}}
    (hf : Field.isReqA (fld k) = true) : k.1 ∈ keys := by
  have hh := of_decide_eq_true hv k
  cases hfd : fld k with
  | req t => rw [hfd] at hh; exact of_decide_eq_true hh
  | optional t => rw [hfd] at hf; exact absurd hf (by simp [Field.isReqA])
  | fallback t d => rw [hfd] at hf; exact absurd hf (by simp [Field.isReqA])

/-- A declared name passes the keep filter under every rest, because `drop` keeps exactly the
    declared names. A shared name is declared by both bodies, so the object rows need no
    hypothesis about the filter. -/
theorem keepT_of_mem {rest : Rest} {fields : Finset Name} {k : Name} (h : k ∈ fields) :
    keepT rest fields k = true := by
  cases rest <;> simp [keepT, h]

/-- No shared field meets to the bottom at an attribute both bodies read. -/
theorem isBottom_false_of_admA_bodies {a b : Body} {F : {k // k ∈ Body.shared a b} → Field}
    (hisreqA : ∀ k, Field.isReqA (F k)
      = (Field.isReqA (a.at ⟨k.1, Body.mem_shared_left k.2⟩)
         || Field.isReqA (b.at ⟨k.1, Body.mem_shared_right k.2⟩)))
    (hreqOf : ∀ k, Field.isBottom (F k) = true → ∃ t, F k = .req t)
    (ihf : ∀ (k : {k // k ∈ Body.shared a b}) (c : Attr),
      AdmAField (F k) c
        = (AdmAField (a.at ⟨k.1, Body.mem_shared_left k.2⟩) c
            && AdmAField (b.at ⟨k.1, Body.mem_shared_right k.2⟩) c))
    {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hA : AdmABody a (.m keys g) = true) (hB : AdmABody b (.m keys g) = true) :
    ∀ k, Field.isBottom (F k) = false := by
  rw [AdmABody_map, Bool.and_eq_true] at hA hB
  intro k
  refine Bool.eq_false_iff.mpr (fun hbot => ?_)
  have ha := Body.mem_shared_left k.2
  have hb := Body.mem_shared_right k.2
  obtain ⟨t, hreqf⟩ := hreqOf k hbot
  have hreq : Field.isReqA (F k) = true := by rw [hreqf]; rfl
  rw [hisreqA k, Bool.or_eq_true] at hreq
  have hk : k.1 ∈ keys := by
    rcases hreq with hr | hr
    · exact mem_keys_of_req hA.1 (k := ⟨k.1, ha⟩) hr
    · exact mem_keys_of_req hB.1 (k := ⟨k.1, hb⟩) hr
  have hrowA := objAdmA_row hA.2 hk ha (keepT_of_mem ha)
  have hrowB := objAdmA_row hB.2 hk hb (keepT_of_mem hb)
  have := ihf k (g ⟨k.1, hk⟩)
  rw [hreqf] at this
  simp only [AdmAField, hrowA, hrowB] at this
  rw [show t = Term.never from eq_never_of_isNever (by simpa [hreqf, Field.isBottom] using hbot)] at this
  simp [AdmA] at this


/-- The read side's required-name test, against the guards the meet reads first. A `fallback`
    name is shared, because `Body.fbShared` holds; a `req` name is present, because the read side
    forces it, and the partner declares every name it reads. -/
theorem reqShared_of_admA {a b : Body} {r : Rest}
    (hr : Rest.merge a.rest b.rest = some r)
    (hfb : Body.fbShared a b = true) (hdb : Body.dropFits b a = true)
    {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hA : AdmABody a (.m keys g) = true) (hB : AdmABody b (.m keys g) = true) :
    Body.reqShared a b = true := by
  refine decide_eq_true (fun k hreq => ?_)
  cases hf : a.at k with
  | fallback t d => exact of_decide_eq_true hfb k (by rw [hf]; rfl)
  | optional t => rw [hf] at hreq; exact absurd hreq (by simp [Field.isReq])
  | req t =>
      have hpres : k.1 ∈ keys := by
        rw [AdmABody_map, Bool.and_eq_true] at hA
        exact mem_keys_of_req hA.1 (by rw [hf]; rfl)
      cases hbr : b.rest with
      | refuse => exact mem_fields_of_admA hbr hB k.1 hpres
      | drop =>
          unfold Body.dropFits at hdb
          rw [hbr] at hdb
          exact of_decide_eq_true hdb k.1 k.2
      | codec t => rw [hbr] at hr; cases har : a.rest <;> rw [har] at hr <;> simp [Rest.merge] at hr

/-- The read side's presence test reads the marks alone, so a field table carrying the body's
    marks has the body's test. -/
theorem reqPresentT_of_isReqA {b : Body} {F : {k // k ∈ b.fields} → Field}
    (hreq : ∀ k, Field.isReqA (F k) = Field.isReqA (b.at k)) (keys : Finset Name) :
    reqPresentT b.fields F keys = reqPresentT b.fields b.at keys := by
  rw [reqPresentT_req, reqPresentT_req]
  exact decide_eq_decide.mpr (forall_congr' fun k => by rw [hreq k])

/-- Every kept entry goes through its field and the right operand's term alike. The rest is a
    codec here, so `keepT` is constantly true and the two sides filter the same names. -/
theorem objAdmA_of_right {b : Body} {x t r : Term} {F : {k // k ∈ b.fields} → Field}
    (hrest : b.rest = .codec t)
    (ihf : ∀ (k : {k // k ∈ b.fields}) (c : Attr),
      AdmAField (F k) c = (AdmAField (b.at k) c && AdmA x c))
    (iht : ∀ c, AdmA r c = (AdmA t c && AdmA x c))
    (keys : Finset Name) (g : {k // k ∈ keys} → Attr) :
    objAdmA ⟨b.fields, fun k => AdmAField (F k)⟩ (some (AdmA r))
        (keepT (.codec r) b.fields) keys g
      = (objAdmA ⟨b.fields, fun k => AdmAField (b.at k)⟩ (some (AdmA t))
           (keepT b.rest b.fields) keys g
         && decide (∀ k : {k // k ∈ keys}, AdmA x (g k) = true)) := by
  simp only [objAdmA, entryPA, MapOf.at, hrest, keepT, true_implies]
  refine decide_forall_and (fun k => ?_)
  by_cases hk : k.1 ∈ b.fields
  · simp only [dif_pos hk]
    exact ihf ⟨k.1, hk⟩ (g k)
  · simp only [dif_neg hk]
    exact iht (g k)

/-- A field at the bottom reads nothing either. -/
theorem AdmAField_of_isBottom {f : Field} (h : Field.isBottom f = true) (c : Attr) :
    AdmAField f c = false := by
  cases f with
  | req t => rw [show t = .never from eq_never_of_isNever h]; rfl
  | fallback t d => rw [show t = .never from eq_never_of_isNever h]; rfl
  | optional t => exact absurd h (by simp [Field.isBottom])

/-- No declared field meets the right operand's term to the bottom at an attribute both read. -/
theorem isBottom_false_of_admA_right {b : Body} {x : Term} {F : {k // k ∈ b.fields} → Field}
    (hreq : ∀ k, Field.isReqA (F k) = Field.isReqA (b.at k))
    (hnfb : ∀ (k : {k // k ∈ b.fields}) (t : Term) (d : Value), F k ≠ .fallback t d)
    (ihf : ∀ (k : {k // k ∈ b.fields}) (c : Attr),
      AdmAField (F k) c = (AdmAField (b.at k) c && AdmA x c))
    {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hA : AdmABody b (.m keys g) = true)
    (hR : decide (∀ k : {k // k ∈ keys}, AdmA x (g k) = true) = true) :
    ∀ k, Field.isBottom (F k) = false := by
  rw [AdmABody_map, Bool.and_eq_true] at hA
  intro k
  refine Bool.eq_false_iff.mpr (fun hbot => ?_)
  have hbotA : Field.isReqA (F k) = true := by
    cases hfd : F k with
    | req t => rfl
    | optional t => rw [hfd] at hbot; exact absurd hbot (by simp [Field.isBottom])
    | fallback t d => exact absurd hfd (hnfb k t d)
  have hk : k.1 ∈ keys := mem_keys_of_req hA.1 ((hreq k) ▸ hbotA)
  have hrow := objAdmA_row hA.2 hk k.2 (keepT_of_mem k.2)
  have hrec := of_decide_eq_true hR ⟨k.1, hk⟩
  have := ihf k (g ⟨k.1, hk⟩)
  rw [AdmAField_of_isBottom hbot, hrow, hrec] at this
  exact absurd this (by simp)

/-- Where a literal reads, its base reads the same value: `literalCodec` is `baseCodec`
    restricted, and `Codec.restrict`'s `p` returns the base's own value where the guard passes. -/
theorem literal_p_base {k : GroundKind} {x : k.Carrier} {a : Attr} {v : Value}
    (h : (literalCodec k x).p a = some v) : (baseCodec k).p a = some v := by
  rw [literalCodec_p_restrict] at h
  simp only [Codec.restrict] at h
  cases hb : (baseCodec k).p a with
  | none => rw [hb] at h; simp at h
  | some w => rw [hb] at h; simp only [Option.bind] at h; split at h <;> simp_all

/-- Where a literal reads, its base reads it to the same value. -/
theorem literal_denote_agree {k : GroundKind} {x : k.Carrier} {a : Attr}
    (h : AdmA (Term.literal k x) a = true) :
    (denote (Term.literal k x)).p a = (baseCodec k).p a := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((AdmA_exact _ a).mp h)
  rw [hw, literal_p_base (show (literalCodec k x).p a = some w from hw)]

/-- Where a literal reads, its base reads: the literal's codec is the base's restricted. -/
theorem AdmA_base_of_literal {k : GroundKind} {x : k.Carrier} {bt : Term} {a : Attr}
    (hb : denote bt = baseCodec k) (h : AdmA (Term.literal k x) a = true) :
    AdmA bt a = true := by
  refine (AdmA_exact bt a).mpr ?_
  rw [hb]
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((AdmA_exact _ a).mp h)
  rw [literal_p_base (show (literalCodec k x).p a = some w from hw)]
  rfl

/-- A literal's guard, read off a successful read: mirror of `literal_p_base`. -/
theorem literal_inL {k : GroundKind} {x : k.Carrier} {a : Attr} {v : Value}
    (h : (literalCodec k x).p a = some v) : inL k x v = true := by
  rw [literalCodec_p_restrict] at h
  simp only [Codec.restrict] at h
  cases hb : (baseCodec k).p a with
  | none => rw [hb] at h; simp at h
  | some w => rw [hb] at h; simp only [Option.bind] at h; split at h <;> simp_all

/-- One base's guard names one inhabitant. -/
theorem inL_inj {k : GroundKind} {x y : k.Carrier} {v : Value}
    (hx : inL k x v = true) (hy : inL k y v = true) : x = y := by
  cases k <;> cases v <;> simp_all [inL] <;>
    first
      | rfl
      | (obtain ⟨_, rfl⟩ := hx; obtain ⟨_, rfl⟩ := hy; rfl)

/-- **Two literals at one base and two values read nothing together.** Simp on `AdmALit` and
    `inL` does not reach the `decimal` and `number` rows; exactness does. -/
theorem AdmALit_never_of_ne {k : GroundKind} {x y : k.Carrier} (hne : ¬ (x = y)) (a : Attr) :
    AdmA (.never : Term) a = (AdmA (Term.literal k x) a && AdmA (Term.literal k y) a) := by
  cases hx : AdmA (Term.literal k x) a with
  | false => simp [AdmA]
  | true =>
      cases hy : AdmA (Term.literal k y) a with
      | false => simp [AdmA]
      | true =>
          exfalso
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((AdmA_exact _ a).mp hx)
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((AdmA_exact _ a).mp hy)
          have hbx := literal_p_base (show (literalCodec k x).p a = some v from hv)
          have hby := literal_p_base (show (literalCodec k y).p a = some w from hw)
          have hvw : v = w := Option.some.inj (hbx.symm.trans hby)
          subst hvw
          exact hne (inL_inj (literal_inL (show (literalCodec k x).p a = some v from hv))
            (literal_inL (show (literalCodec k y).p a = some v from hw)))

/-- Every row that answers the bottom owes only its first half: the second is vacuous, because
    the first says no attribute is read by both factors. -/
theorem bottom_row {x y : Term}
    (h1 : ∀ a : Attr, AdmA (.never : Term) a = (AdmA x a && AdmA y a)) :
    (∀ a : Attr, AdmA (.never : Term) a = (AdmA x a && AdmA y a)) ∧
    (∀ a : Attr, AdmA x a = true → AdmA y a = true →
      (denote (.never : Term)).p a = (denote x).p a ∧
      (denote (.never : Term)).p a = (denote y).p a) :=
  ⟨h1, fun a ha hb => absurd (h1 a) (by rw [ha, hb]; simp [AdmA])⟩


/-- A traversal is a congruence in its element function, at the entries it visits. -/
theorem traverse_congr {α β : Type} {f g : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) → traverse f xs = traverse g xs := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x xs ihx =>
      intro hh
      rw [traverse_cons, traverse_cons, hh x (by simp),
        ihx (fun y hy => hh y (by simp [hy]))]

/-- `allPA` holds at each attribute it quantifies over. -/
theorem allPA_mem {P : AP} : ∀ {as : List Attr}, allPA P as = true → ∀ a ∈ as, P a = true := by
  intro as
  induction as with
  | nil => intro _ a ha; exact absurd ha (by simp)
  | cons b bs ihx =>
      intro hh a ha
      rw [allPA, Bool.and_eq_true] at hh
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact hh.1
      · exact ihx hh.2 a ha'

/-- **The `array` congruence.** Element codecs that agree at every attribute the wire list
    carries read that list to the same value. -/
theorem arrayCodec_p_congr {c d : Codec} {as : List Attr} (hh : ∀ a ∈ as, c.p a = d.p a) :
    (arrayCodec c).p (.l as) = (arrayCodec d).p (.l as) := by
  show (traverse c.p as).map Value.arr = (traverse d.p as).map Value.arr
  rw [traverse_congr hh]

/-- **The `record` congruence.** The name set is the index, so the entry function is the only
    thing to compare. -/
theorem recordCodec_p_congr {c d : Codec} {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hh : ∀ k, c.p (g k) = d.p (g k)) :
    (recordCodec c).p (.m keys g) = (recordCodec d).p (.m keys g) := by
  show (funImage (fun k => c.p (g k))).map (Value.map keys)
      = (funImage (fun k => d.p (g k))).map (Value.map keys)
  rw [funext hh]


/-- `opaque` reads a self-identifying attribute exactly as the base for that attribute does. -/
theorem opaq_p_string (l : Bool) (s : String) :
    (denote (.opaq l)).p (.s s) = (denote (.string : Term)).p (.s s) := opaqCodec_p_s l 0 s

/-- …a stored boolean as `boolean` does, -/
theorem opaq_p_boolean (l : Bool) (b : Bool) :
    (denote (.opaq l)).p (.bool b) = (denote (.boolean : Term)).p (.bool b) :=
  opaqCodec_p_bool l 0 b

/-- …stored bytes as `binary` does, -/
theorem opaq_p_binary (l : Bool) (b : Bytes) :
    (denote (.opaq l)).p (.b b) = (denote (.binary : Term)).p (.b b) := opaqCodec_p_b l 0 b

/-- …and the stored null as `null` does. -/
theorem opaq_p_null (l : Bool) :
    (denote (.opaq l)).p .null = (denote (.null : Term)).p .null := opaqCodec_p_null l 0

/-- …and the lossy one reads a stored numeral as `number` does. The refusing one reads none,
    which is why the `number` row answers the bottom there. -/
theorem opaq_p_number (x : WFNumeral) :
    (denote (.opaq true)).p (.n x) = (denote (.number : Term)).p (.n x) := by
  rw [show (denote (.opaq true)).p (.n x) = (opaqCodec (0 + 1) true).p (.n x) from rfl,
    opaqCodec_p_n]
  rfl

/-- `number`'s read row is its codec's domain, said as an equation so the `opaque` rows can
    conjoin the two. -/
theorem AdmA_number_eq (x : WFNumeral) :
    AdmA (.number : Term) (.n x) = (numberCodec.p (.n x)).isSome := by
  show (match Double.ofDec x.1 with | some d => Numeral.WF d.toDec | none => false) = _
  cases hd : Double.ofDec x.1 with
  | none => simp [numberCodec, hd]
  | some d => cases hw : Numeral.WF d.toDec <;> simp [numberCodec, hd, hw]

/-- The refusing `opaque` is below the lossy one, so where the refusing one admits, the two
    read the same value. -/
theorem opaq_p_lossy {l : Bool} {a : Attr} (hh : AdmA (.opaq false) a = true) :
    (denote (.opaq l)).p a = (denote (.opaq false)).p a := by
  cases l with
  | false => rfl
  | true =>
      rw [AdmA_opaq_eq] at hh
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hh
      show (opaqCodec (Attr.depth a) true).p a = _
      rw [opaq_p_mono _ a v hv]
      exact hv.symm

/-- A declared position that holds nothing empties the tuple: every wire list the tuple
    reads fills each declared position. -/
theorem alignPA_never_false : ∀ {ts : List Term} {tail : Option Term} {ws : List Attr},
    ts.any Term.isNever = true → alignPA (AdmAList ts) (AdmAOptT tail) ws = false := by
  intro ts
  induction ts with
  | nil => intro _ _ h; simp at h
  | cons t ts' ih =>
    intro tail ws h
    cases ws with
    | nil => rfl
    | cons w ws' =>
      simp only [List.any_cons, Bool.or_eq_true] at h
      simp only [AdmAList, alignPA]
      rcases h with ht | hrest
      · rw [show t = Term.never from eq_never_of_isNever ht, show AdmA .never _ = false from rfl, Bool.false_and]
      · rw [ih (tail := tail) (ws := ws') hrest, Bool.and_false]


/-- Normalising a tuple keeps what it reads. -/
theorem AdmA_tupleOf (ts : List Term) (tail : Option Term) (v : Attr) :
    AdmA (Term.tupleOf ts tail) v = AdmA (.tuple ts tail) v := by
  unfold Term.tupleOf
  split
  next hany =>
    cases v <;> simp only [AdmA] <;> try rfl
    exact (alignPA_never_false hany).symm
  next => rfl


/-- A term that admits an attribute is not the bottom. -/
theorem not_isNever_of_admA {t : Term} {b : Attr} (hh : AdmA t b = true) : t.isNever = false := by
  cases t <;> first | rfl | exact absurd hh (by simp [AdmA])

/-- A wire list a tuple aligns leaves no declared position at the bottom, so the normalised
    tuple is the tuple. -/
theorem alignPA_not_never : ∀ {vs : List Term} {tl : Option Term} {as : List Attr},
    alignPA (AdmAList vs) (AdmAOptT tl) as = true → vs.any Term.isNever = false := by
  intro vs
  induction vs with
  | nil => intro _ _ _; rfl
  | cons v vs' ihv =>
      intro tl as hh
      cases as with
      | nil => exact absurd hh (by simp [AdmAList, alignPA])
      | cons b as' =>
          simp only [AdmAList, alignPA, Bool.and_eq_true] at hh
          simp only [List.any_cons, Bool.or_eq_false_iff]
          exact ⟨not_isNever_of_admA hh.1, ihv hh.2⟩

/-- A tuple that reads a wire list is already normal. -/
theorem tupleOf_eq_tuple {vs : List Term} {tl : Option Term} {as : List Attr}
    (hh : alignPA (AdmAList vs) (AdmAOptT tl) as = true) :
    Term.tupleOf vs tl = .tuple vs tl := if_neg (by rw [alignPA_not_never hh]; simp)

/-- The aligned traversal, one declared position at a time. -/
theorem align_traverse_cons {c : Codec} {cs : List Codec} {tc : Option Codec} {b : Attr}
    {as : List Attr} :
    (align (c :: cs) tc (b :: as)).bind (traverse fun ca => ca.1.p ca.2)
      = (c.p b).bind fun y =>
          ((align cs tc as).bind (traverse fun ca => ca.1.p ca.2)).map (y :: ·) := by
  simp only [align]
  cases align cs tc as <;> simp [traverse_cons]

/-- …and one tail position at a time. -/
theorem align_traverse_tail_cons {c : Codec} {b : Attr} {as : List Attr} :
    (align [] (some c) (b :: as)).bind (traverse fun ca => ca.1.p ca.2)
      = (c.p b).bind fun y =>
          ((align [] (some c) as).bind (traverse fun ca => ca.1.p ca.2)).map (y :: ·) := by
  simp only [align]
  cases align ([] : List Codec) (some c) as <;> simp [traverse_cons]

/-- **The `tuple` congruence.** At a wire list the met row aligns, two tuples whose positions
    read alike wherever the met row admits read the whole list alike. -/
theorem align_p_congr : ∀ {as : List Attr} {vs ts : List Term} {tl tail : Option Term},
    alignPA (AdmAList vs) (AdmAOptT tl) as = true →
    List.Forall₂ (fun v t => ∀ b, AdmA v b = true → (denote v).p b = (denote t).p b) vs ts →
    ((tl = none ∧ tail = none) ∨
      ∃ u t, tl = some u ∧ tail = some t ∧
        ∀ b, AdmA u b = true → (denote u).p b = (denote t).p b) →
    (align (denoteList vs) (denoteOpt tl) as).bind (traverse fun ca => ca.1.p ca.2)
      = (align (denoteList ts) (denoteOpt tail) as).bind (traverse fun ca => ca.1.p ca.2) := by
  intro as
  induction as with
  | nil =>
      intro vs ts tl tail hal hF _
      cases hF with
      | nil => rcases tl with _ | u <;> rcases tail with _ | t <;> rfl
      | cons _ _ => exact absurd hal (by simp [AdmAList, alignPA])
  | cons b as' ihx =>
      intro vs ts tl tail hal hF htl
      cases hF with
      | nil =>
          rcases htl with ⟨rfl, rfl⟩ | ⟨u, t, rfl, rfl, hu⟩
          · exact absurd hal (by simp [AdmAList, AdmAOptT, alignPA])
          · simp only [AdmAList, AdmAOptT, alignPA, Bool.and_eq_true] at hal
            have hrec := ihx (vs := []) (ts := []) (tl := some u) (tail := some t) hal.2 .nil
              (Or.inr ⟨u, t, rfl, rfl, hu⟩)
            simp only [denoteList, denoteOpt] at hrec
            simp only [denoteList, denoteOpt, align_traverse_tail_cons, hrec, hu b hal.1]
      | cons hvt hrest =>
          rename_i v vs' t ts'
          simp only [AdmAList, alignPA, Bool.and_eq_true] at hal
          simp only [denoteList, align_traverse_cons,
            ihx hal.2 hrest htl, hvt b hal.1]

/-- **The `array` half of the same congruence**: a met tuple against the array it was met with. -/
theorem align_p_congr_array : ∀ {as : List Attr} {vs : List Term} {tl : Option Term} {e : Term},
    alignPA (AdmAList vs) (AdmAOptT tl) as = true →
    (∀ v ∈ vs, ∀ b, AdmA v b = true → (denote v).p b = (denote e).p b) →
    (∀ u ∈ tl, ∀ b, AdmA u b = true → (denote u).p b = (denote e).p b) →
    (align (denoteList vs) (denoteOpt tl) as).bind (traverse fun ca => ca.1.p ca.2)
      = traverse (denote e).p as := by
  intro as
  induction as with
  | nil =>
      intro vs tl e hal _ _
      cases vs with
      | nil => rcases tl with _ | u <;> rfl
      | cons _ _ => exact absurd hal (by simp [AdmAList, alignPA])
  | cons b as' ihx =>
      intro vs tl e hal hvs htl
      cases vs with
      | nil =>
          cases tl with
          | none => exact absurd hal (by simp [AdmAList, AdmAOptT, alignPA])
          | some u =>
              simp only [AdmAList, AdmAOptT, alignPA, Bool.and_eq_true] at hal
              have hu := htl u (by simp)
              have hrec := ihx (vs := []) (tl := some u) (e := e) hal.2 (by simp) htl
              simp only [denoteList, denoteOpt] at hrec
              simp only [denoteList, denoteOpt, align_traverse_tail_cons, traverse_cons,
                hrec, hu b hal.1]
      | cons v vs' =>
          simp only [AdmAList, alignPA, Bool.and_eq_true] at hal
          simp only [denoteList, align_traverse_cons, traverse_cons,
            ihx hal.2 (fun w hw => hvs w (by simp [hw])) htl,
            hvs v (by simp) b hal.1]

/-- Normalising a refinement keeps what it reads. -/
theorem AdmA_refineOf (z : Term) (p : Pred) (a : Attr) :
    AdmA (Term.refineOf z p) a = AdmA (.refine z p) a := by
  unfold Term.refineOf
  split
  next hz => rw [show z = Term.never from eq_never_of_isNever hz]; simp [AdmA, refineReads]
  next => rfl

/-- Normalising a refinement changes no reading at an attribute the inner term admits. -/
theorem refineOf_p {w : Term} {p : Pred} {a : Attr} (hw : AdmA w a = true) :
    (denote (Term.refineOf w p)).p a
      = ((denote w).p a).bind (fun v => if p.eval v then some v else none) := by
  rw [show Term.refineOf w p = .refine w p from
    if_neg (by rw [not_isNever_of_admA hw]; simp)]
  rfl

/-- A refinement's gate reads the inner term, so terms that read alike gate alike. -/
theorem refineReads_congr {t u : Term} {q : Value → Bool} {a : Attr}
    (hh : (denote t).p a = (denote u).p a) : refineReads t q a = refineReads u q a := by
  simp only [refineReads, hh]

/-- **The refinement row, with the refinement on the left.** The predicate is data, so it rides
    on the meet of the inner terms; the reading agreement is what makes the gate agree. -/
theorem refine_row_l {x y w : Term} {p : Pred}
    (ih1 : ∀ b, AdmA w b = (AdmA x b && AdmA y b))
    (ih2 : ∀ b, AdmA x b = true → AdmA y b = true →
      (denote w).p b = (denote x).p b ∧ (denote w).p b = (denote y).p b) :
    (∀ a, AdmA (Term.refineOf w p) a = (AdmA (.refine x p) a && AdmA y a)) ∧
    (∀ a, AdmA (.refine x p) a = true → AdmA y a = true →
      (denote (Term.refineOf w p)).p a = (denote (.refine x p)).p a ∧
      (denote (Term.refineOf w p)).p a = (denote y).p a) := by
  constructor
  · intro a
    rw [AdmA_refineOf]
    show (AdmA w a && refineReads w p.eval a) = ((AdmA x a && refineReads x p.eval a) && AdmA y a)
    cases hw : AdmA w a with
    | false =>
        rw [ih1 a, Bool.and_eq_false_iff] at hw
        rcases hw with hx | hy
        · rw [hx]; simp
        · rw [hy]; simp
    | true =>
        have hxy := ih1 a
        rw [hw] at hxy
        have hx : AdmA x a = true := (Bool.and_eq_true .. ▸ hxy.symm : _).1
        have hy : AdmA y a = true := (Bool.and_eq_true .. ▸ hxy.symm : _).2
        rw [refineReads_congr (ih2 a hx hy).1, hx, hy]
        simp
  · intro a ha hb
    rw [show AdmA (.refine x p) a = (AdmA x a && refineReads x p.eval a) from rfl,
      Bool.and_eq_true] at ha
    obtain ⟨hx, hr⟩ := ha
    have hw : AdmA w a = true := by rw [ih1 a, hx, hb]; rfl
    obtain ⟨hd1, hd2⟩ := ih2 a hx hb
    cases hp : (denote x).p a with
    | none => rw [refineReads_none hp] at hr; exact absurd hr (by simp)
    | some v =>
        rw [refineReads_some hp] at hr
        have hwv : (denote w).p a = some v := hd1.trans hp
        have hyv : (denote y).p a = some v := hd2.symm.trans hwv
        refine ⟨?_, ?_⟩
        · rw [refineOf_p hw, hwv,
            show (denote (.refine x p)).p a
              = ((denote x).p a).bind (fun u => if p.eval u then some u else none) from rfl, hp]
        · simp [refineOf_p hw, hwv, hyv, hr]

/-- …and with the refinement on the right. -/
theorem refine_row_r {x y w : Term} {p : Pred}
    (ih1 : ∀ b, AdmA w b = (AdmA x b && AdmA y b))
    (ih2 : ∀ b, AdmA x b = true → AdmA y b = true →
      (denote w).p b = (denote x).p b ∧ (denote w).p b = (denote y).p b) :
    (∀ a, AdmA (Term.refineOf w p) a = (AdmA x a && AdmA (.refine y p) a)) ∧
    (∀ a, AdmA x a = true → AdmA (.refine y p) a = true →
      (denote (Term.refineOf w p)).p a = (denote x).p a ∧
      (denote (Term.refineOf w p)).p a = (denote (.refine y p)).p a) := by
  constructor
  · intro a
    rw [AdmA_refineOf]
    show (AdmA w a && refineReads w p.eval a) = (AdmA x a && (AdmA y a && refineReads y p.eval a))
    cases hw : AdmA w a with
    | false =>
        rw [ih1 a, Bool.and_eq_false_iff] at hw
        rcases hw with hx | hy
        · rw [hx]; simp
        · rw [hy]; simp
    | true =>
        have hxy := ih1 a
        rw [hw] at hxy
        have hx : AdmA x a = true := (Bool.and_eq_true .. ▸ hxy.symm : _).1
        have hy : AdmA y a = true := (Bool.and_eq_true .. ▸ hxy.symm : _).2
        rw [refineReads_congr (ih2 a hx hy).2, hx, hy]
        simp
  · intro a ha hb
    rw [show AdmA (.refine y p) a = (AdmA y a && refineReads y p.eval a) from rfl,
      Bool.and_eq_true] at hb
    obtain ⟨hy, hr⟩ := hb
    have hw : AdmA w a = true := by rw [ih1 a, ha, hy]; rfl
    obtain ⟨hd1, hd2⟩ := ih2 a ha hy
    cases hp : (denote y).p a with
    | none => rw [refineReads_none hp] at hr; exact absurd hr (by simp)
    | some v =>
        rw [refineReads_some hp] at hr
        have hwv : (denote w).p a = some v := hd2.trans hp
        have hxv : (denote x).p a = some v := hd1.symm.trans hwv
        refine ⟨?_, ?_⟩
        · simp [refineOf_p hw, hwv, hxv, hr]
        · rw [refineOf_p hw, hwv,
            show (denote (.refine y p)).p a
              = ((denote y).p a).bind (fun u => if p.eval u then some u else none) from rfl, hp]


/-- The options that survive are the ones that read; the bottoms read nothing. -/
theorem AdmAAny_filter_never : ∀ (ts : List Term) (v : Attr),
    AdmAAny (ts.filter (fun z => !z.isNever)) v = AdmAAny ts v
  | [], _ => rfl
  | t :: ts, v => by
      cases ht : t.isNever with
      | true =>
        have htn : t = Term.never := eq_never_of_isNever ht
        subst htn
        rw [List.filter_cons, if_neg (by simp [Term.isNever]), AdmAAny_cons,
          AdmAAny_filter_never ts v]
        rfl
      | false =>
        rw [List.filter_cons, if_pos (by simp [ht]), AdmAAny_cons, AdmAAny_cons,
          AdmAAny_filter_never ts v]


/-- A certified list of survivors reads what its options read. -/
theorem AdmA_ofOptions {ts : List Term} (hc : unionOk ts = true) (v : Attr) :
    AdmA (Term.ofOptions ts) v = AdmAAny ts v := by
  match ts with
  | [] => rfl
  | [t] => simp only [Term.ofOptions, AdmAAny_cons, AdmAAny_nil, Bool.or_false]
  | _ :: _ :: _ => exact selOptA_eq_AdmAAny hc v


/-- The join over the met options is the join over the options, met with the partner. -/
theorem AdmAAny_meet {y : Term} (v : Attr) : ∀ {os zs : List Term},
    List.Forall₂ (fun t w => ∀ u, AdmA w u = (AdmA t u && AdmA y u)) os zs →
    AdmAAny zs v = (AdmAAny os v && AdmA y v) := by
  intro os zs h
  induction h with
  | nil => simp
  | cons hh _ ihx =>
    rw [AdmAAny_cons, AdmAAny_cons, hh v, ihx]
    cases AdmA _ v <;> cases AdmA y v <;> simp


/-- A `Forall₂` relates every left element to some right one. -/
theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ {x}, x ∈ as → ∃ y ∈ bs, R x y
  | _, _, .nil, _, hx => by simp at hx
  | _, _, .cons hr hrest, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨_, List.mem_cons_self, hr⟩
      · obtain ⟨y, hy, hry⟩ := forall₂_mem_left hrest hx'
        exact ⟨y, List.mem_cons_of_mem _ hy, hry⟩

/-- **Under the certificate a term's read row is its structural test.** Lifted out of
    `selOptA_eq_AdmAAny`, which needs it in this form and states it inline. -/
theorem admitOptA_of_AdmA {os : List Term} (hc : unionOk os = true) {t : Term} (ht : t ∈ os)
    {a : Attr} (hh : AdmA t a = true) : admitOptA (specOf t, AdmA t) a = true := by
  simp only [unionOk, Bool.and_eq_true, List.all_eq_true] at hc
  cases t with
  | object b =>
      obtain ⟨hr, hnf⟩ := namesAgree_parts (hc.2 _ ht)
      cases a with
      | m keys g => simpa only [admitOptA, specOf] using structural_of_AdmABody hr hnf hh
      | _ => exact absurd hh (by cases b; simp [AdmA, AdmABody])
  | _ => exact hh

/-- Where the row answers, exactly one option passes the structural test, and its row is true
    there. This is `selOptA`'s own `match`, read backwards. -/
theorem filter_eq_singleton_of_selOptA {ts : List Term} {a : Attr}
    (hh : selOptA (AdmASpecs ts) a = true) :
    ∃ t, ts.filter (fun u => admitOptA (specOf u, AdmA u) a) = [t] ∧ AdmA t a = true := by
  rw [selOptA, AdmASpecs_eq, filter_map_AdmASpecs] at hh
  cases hL : ts.filter (fun u => admitOptA (specOf u, AdmA u) a) with
  | nil => rw [hL] at hh; simp at hh
  | cons t rest =>
      cases rest with
      | nil => exact ⟨t, rfl, by rw [hL] at hh; simpa using hh⟩
      | cons _ _ => rw [hL] at hh; simp at hh

/-- **A union reads through the one option that admits.** `select` answers only at a singleton
    filter, and `filter_AdmASpecs` is that filter in the term list's own terms. -/
theorem union_p_of_filter {ts : List Term} {t : Term} {a : Attr}
    (hf : ts.filter (fun u => admitOptA (specOf u, AdmA u) a) = [t]) :
    (denote (.union ts)).p a = (denote t).p a := by
  rw [denote_union_sems]
  show select (optionSems ts) (·.admitA) (·.c.p) a = _
  unfold select
  rw [filter_AdmASpecs (fun u _ => AdmA_exact u) a, hf]
  simp [optionSemOf_c]

/-- …and so does a list of survivors, whatever its length. -/
theorem ofOptions_p_of_filter {ts : List Term} {t : Term} {a : Attr}
    (hf : ts.filter (fun u => admitOptA (specOf u, AdmA u) a) = [t]) :
    (denote (Term.ofOptions ts)).p a = (denote t).p a := by
  match ts with
  | [] => simp at hf
  | [s] =>
      rw [List.filter_cons] at hf
      split at hf
      · rw [show Term.ofOptions [s] = s from rfl]
        simp only [List.filter_nil, List.cons.injEq] at hf
        rw [hf.1]
      · simp at hf
  | _ :: _ :: _ => exact union_p_of_filter hf

/-- A table that declares no stand-in contributes no name to `fbNames`. -/
theorem fbNames_empty_of_not_fallback {fields : Finset Name} {F : {k // k ∈ fields} → Field}
    (hnfb : ∀ (k : {k // k ∈ fields}) (t : Term) (d : Value), F k ≠ .fallback t d)
    (names : Finset Name) :
    fbNames names ⟨fields, fun k => fieldSem (F k)⟩ = ∅ := by
  rw [fbNames]
  refine filter_eq_empty_on (fun k hk => ?_)
  rw [Bool.and_eq_false_iff]
  refine Or.inl ?_
  rw [MapOf.at_mk_pos hk]
  cases hf : F ⟨k, hk⟩ with
  | req _ => rfl
  | optional _ => rfl
  | fallback t d => exact absurd hf (hnfb ⟨k, hk⟩ t d)

/-- **A factor declares no stand-in the map omits**, given that a shared stand-in forces the
    partner's field to be required. -/
theorem fbNames_factor_of_req {a b : Body}
    (hfbReq : ∀ (k : Name) (hk : k ∈ a.fields) (hkb : k ∈ b.fields),
      (∃ t d, a.at ⟨k, hk⟩ = .fallback t d) → ∃ u, b.at ⟨k, hkb⟩ = .req u)
    (hfb : Body.fbShared a b = true)
    {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hB : AdmA (.object b) (.m keys g) = true) :
    fbNames keys ⟨a.fields, fun k => fieldSem (a.at k)⟩ = ∅ := by
  have hreqB : reqPresentT b.fields b.at keys = true := by
    rw [AdmA_object b (.m keys g), AdmABody_map,
      Bool.and_eq_true] at hB
    exact hB.1
  rw [fbNames]
  refine filter_eq_empty_on (fun k hk => ?_)
  rw [Bool.and_eq_false_iff,
    MapOf.at_mk_pos (f := fun k => fieldSem (a.at k)) hk]
  cases hf : a.at ⟨k, hk⟩ with
  | req _ => exact Or.inl rfl
  | optional _ => exact Or.inl rfl
  | fallback t d =>
      refine Or.inr ?_
      have hkb : k ∈ b.fields := of_decide_eq_true hfb ⟨k, hk⟩ (by rw [hf]; rfl)
      obtain ⟨u, hu⟩ := hfbReq k hk hkb ⟨t, d, hf⟩
      have := of_decide_eq_true hreqB ⟨k, hkb⟩
      rw [hu] at this
      simp [this]


/-- …and the mirror. -/
theorem fbNames_factor_of_req' {a b : Body}
    (hfbReq : ∀ (k : Name) (hk : k ∈ b.fields) (hkb : k ∈ a.fields),
      (∃ t d, b.at ⟨k, hk⟩ = .fallback t d) → ∃ u, a.at ⟨k, hkb⟩ = .req u)
    (hfb : Body.fbShared b a = true)
    {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hA : AdmA (.object a) (.m keys g) = true) :
    fbNames keys ⟨b.fields, fun k => fieldSem (b.at k)⟩ = ∅ := by
  have hreqA : reqPresentT a.fields a.at keys = true := by
    rw [AdmA_object a (.m keys g), AdmABody_map,
      Bool.and_eq_true] at hA
    exact hA.1
  rw [fbNames]
  refine filter_eq_empty_on (fun k hk => ?_)
  rw [Bool.and_eq_false_iff,
    MapOf.at_mk_pos (f := fun k => fieldSem (b.at k)) hk]
  cases hf : b.at ⟨k, hk⟩ with
  | req _ => exact Or.inl rfl
  | optional _ => exact Or.inl rfl
  | fallback t d =>
      refine Or.inr ?_
      have hka : k ∈ a.fields := of_decide_eq_true hfb ⟨k, hk⟩ (by rw [hf]; rfl)
      obtain ⟨u, hu⟩ := hfbReq k hk hka ⟨t, d, hf⟩
      have := of_decide_eq_true hreqA ⟨k, hka⟩
      rw [hu] at this
      simp [this]

/-- **The keep filter agrees on the map's own names.** `Rest.merge` answers `refuse` unless both
    rests are `drop`, so the merged filter keeps everything except at `drop` against `drop`, where
    `dropFits` makes the two declared sets equal. The one case that is not structural is `drop`
    against `refuse`: there the `refuse` factor's admission puts the map's names inside its
    declared set, and `dropFits` puts that inside the `drop` factor's. -/
theorem keepT_agree {a b : Body} {r : Rest}
    (hr : Rest.merge a.rest b.rest = some r)
    (hda : Body.dropFits a b = true) (hdb : Body.dropFits b a = true)
    {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hB : AdmA (.object b) (.m keys g) = true) :
    ∀ k ∈ keys, keepT r (Body.shared a b) k = keepT a.rest a.fields k := by
  intro k hk
  cases hra : a.rest with
  | codec t => rw [hra] at hr; cases hrb : b.rest <;> rw [hrb] at hr <;> simp [Rest.merge] at hr
  | refuse =>
      cases hrb : b.rest with
      | codec t => rw [hra, hrb] at hr; simp [Rest.merge] at hr
      | refuse => rw [hra, hrb] at hr; simp only [Rest.merge, Option.some.injEq] at hr; subst hr; rfl
      | drop => rw [hra, hrb] at hr; simp only [Rest.merge, Option.some.injEq] at hr; subst hr; rfl
  | drop =>
      cases hrb : b.rest with
      | codec t => rw [hra, hrb] at hr; simp [Rest.merge] at hr
      | refuse =>
          rw [hra, hrb] at hr; simp only [Rest.merge, Option.some.injEq] at hr; subst hr
          have hkb : k ∈ b.fields :=
            mem_fields_of_admA hrb (by rw [← show AdmA (.object b) (.m keys g)
              = AdmABody b (.m keys g) from rfl]; exact hB) k hk
          rw [Body.dropFits, hra] at hda
          simp only [keepT, decide_eq_true_eq, of_decide_eq_true hda k hkb]
          rfl
      | drop =>
          rw [hra, hrb] at hr; simp only [Rest.merge, Option.some.injEq] at hr; subst hr
          rw [Body.dropFits, hra] at hda
          rw [Body.dropFits, hrb] at hdb
          simp only [keepT, Body.shared, Finset.mem_filter, decide_eq_decide]
          exact ⟨fun h => h.1, fun h => ⟨h, of_decide_eq_true hdb k h⟩⟩


/-- The shared name set reads the same from either side. -/
theorem Body.shared_comm (a b : Body) : Body.shared a b = Body.shared b a := by
  ext k; simp [Body.shared, Finset.mem_filter, and_comm]

/-- **A kept name is shared.** At `drop` against `drop` the merged filter says so outright. At a
    merged `refuse` the filter is vacuous, and the name comes from the map instead: the `refuse`
    factor's admission puts it inside that factor's declared set, and `dropFits` carries it into
    the other's. -/
theorem mem_shared_of_keep {a b : Body} {r : Rest}
    (hr : Rest.merge a.rest b.rest = some r)
    (hda : Body.dropFits a b = true) (hdb : Body.dropFits b a = true)
    {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hA : AdmABody a (.m keys g) = true) (hB : AdmABody b (.m keys g) = true)
    {k : Name} (hk : k ∈ keys) (hkeep : keepT r (Body.shared a b) k = true) :
    k ∈ Body.shared a b := by
  have mk : k ∈ a.fields → k ∈ b.fields → k ∈ Body.shared a b := fun p q =>
    Finset.mem_filter.mpr ⟨p, by simpa using q⟩
  cases hra : a.rest with
  | codec t => rw [hra] at hr; cases hrb : b.rest <;> rw [hrb] at hr <;> simp [Rest.merge] at hr
  | drop =>
      cases hrb : b.rest with
      | codec t => rw [hra, hrb] at hr; simp [Rest.merge] at hr
      | drop =>
          rw [hra, hrb] at hr; simp only [Rest.merge, Option.some.injEq] at hr; subst hr
          simpa only [keepT, decide_eq_true_eq] using hkeep
      | refuse =>
          have hkb : k ∈ b.fields := mem_fields_of_admA hrb hB k hk
          rw [Body.dropFits, hra] at hda
          exact mk (of_decide_eq_true hda k hkb) hkb
  | refuse =>
      have hka : k ∈ a.fields := mem_fields_of_admA hra hA k hk
      cases hrb : b.rest with
      | codec t => rw [hra, hrb] at hr; simp [Rest.merge] at hr
      | refuse => exact mk hka (mem_fields_of_admA hrb hB k hk)
      | drop =>
          rw [Body.dropFits, hrb] at hdb
          exact mk hka (of_decide_eq_true hdb k hka)

/-- **The transport, with the kept name set a variable.** Two images over equal name sets agree
    where their entries agree. `subst` does the work, so the membership proof inside the entry
    never has to be rewritten, which is what defeats `rw` on the filter itself. -/
theorem funImage_map_congr {S S' : Finset Name} (hS : S = S')
    {g : {k // k ∈ S} → Option Value} {g' : {k // k ∈ S'} → Option Value}
    (hg : ∀ (k : Name) (h : k ∈ S) (h' : k ∈ S'), g ⟨k, h⟩ = g' ⟨k, h'⟩)
    {fb fb' : Name → Option Value} :
    (funImage g).map (fun d => (⟨S ∪ ∅, fun k => if h : k.1 ∈ S then d ⟨k.1, h⟩
        else (fb k.1).getD .null⟩ : MapOf Value))
      = (funImage g').map (fun d => (⟨S' ∪ ∅, fun k => if h : k.1 ∈ S' then d ⟨k.1, h⟩
        else (fb' k.1).getD .null⟩ : MapOf Value)) := by
  subst hS
  have himg : g = g' := funext fun k => hg k.1 k.2 k.2
  subst himg
  refine congrArg (fun F => Option.map F (funImage g)) (funext fun d => ?_)
  refine congrArg (MapOf.mk (S ∪ ∅)) (funext fun k => ?_)
  have hk : k.1 ∈ S := by simpa using k.2
  rw [dif_pos hk, dif_pos hk]

/-- **The `object` congruence.** Two payload tables that require the same names, keep the same
    names of the map, declare no stand-in the map omits, and read each kept name alike, read the
    whole map alike. `fbNames = ∅` is what rules out the one place the two could differ at a name
    the map does not carry. -/
theorem objRead_congr {sems sems' : MapOf FieldSem} {rc rc' : Option Codec}
    {kn kn' : Name → Bool} {q : MapOf Attr}
    (hreq : reqPresentB sems q.1 = reqPresentB sems' q.1)
    (hfb : fbNames q.1 sems = ∅) (hfb' : fbNames q.1 sems' = ∅)
    (hfil : q.1.filter (kn ·) = q.1.filter (kn' ·))
    (hent : ∀ (k : Name) (h : k ∈ q.1), kn k = true →
        (entryCodec sems rc k).bind (fun c => c.p (q.2 ⟨k, h⟩))
          = (entryCodec sems' rc' k).bind (fun c => c.p (q.2 ⟨k, h⟩))) :
    objRead sems rc kn q = objRead sems' rc' kn' q := by
  unfold objRead
  rw [hreq, hfb, hfb']
  split
  · exact funImage_map_congr hfil
      (fun k h _ => hent k (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp h).2)
  · rfl

/-- …and the same at the term level, which is where the meet's object rows use it. -/
theorem bodySem_p_congr {b b' : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hreq : reqPresentT b.fields b.at keys = reqPresentT b'.fields b'.at keys)
    (hfb : fbNames keys ⟨b.fields, fun k => fieldSem (b.at k)⟩ = ∅)
    (hfb' : fbNames keys ⟨b'.fields, fun k => fieldSem (b'.at k)⟩ = ∅)
    (hfil : keys.filter (keepT b.rest b.fields ·) = keys.filter (keepT b'.rest b'.fields ·))
    (hent : ∀ (k : Name) (h : k ∈ keys), keepT b.rest b.fields k = true →
        (entryCodec ⟨b.fields, fun k => fieldSem (b.at k)⟩ (rcOf (restSem b.rest)) k).bind
            (fun c => c.p (g ⟨k, h⟩))
          = (entryCodec ⟨b'.fields, fun k => fieldSem (b'.at k)⟩ (rcOf (restSem b'.rest)) k).bind
            (fun c => c.p (g ⟨k, h⟩))) :
    (denote (.object b)).p (.m keys g) = (denote (.object b')).p (.m keys g) := by
  have hb : ∀ c : Body, (denote (.object c)).p (.m keys g)
      = (objRead ⟨c.fields, fun k => fieldSem (c.at k)⟩ (rcOf (restSem c.rest))
          (keepB (restSem c.rest) ⟨c.fields, fun k => fieldSem (c.at k)⟩)
          ⟨keys, g⟩).map mapV.into := by
    intro c; cases c; rfl
  rw [hb b, hb b']
  refine congrArg _ (objRead_congr ?_ hfb hfb' ?_
    (fun k h hk => hent k h (by rw [← keepB_eq b.fields b.at b.rest k]; exact hk)))
  · rw [← reqPresentT_eq, ← reqPresentT_eq]; exact hreq
  · refine Eq.trans (filter_congr_on (fun k _ => keepB_eq b.fields b.at b.rest k))
      (Eq.trans hfil (filter_congr_on (fun k _ => keepB_eq b'.fields b'.at b'.rest k)).symm)


/-- **Two objects, over an abstract field table.** Everything after the field agreement reads
    that agreement alone, so the well-founded caller and the structural one share this. -/
theorem object_row_gen {a b : Body} {z : Term} {r : Rest} {Ok : Prop}
    {F : {k // k ∈ Body.shared a b} → Field}
    (hr : Rest.merge a.rest b.rest = some r)
    (hfba : Body.fbShared a b = true) (hfbb : Body.fbShared b a = true)
    (hda : Body.dropFits a b = true) (hdb : Body.dropFits b a = true)
    (hisreqA : Ok → ∀ k, Field.isReqA (F k)
      = (Field.isReqA (a.at ⟨k.1, Body.mem_shared_left k.2⟩)
         || Field.isReqA (b.at ⟨k.1, Body.mem_shared_right k.2⟩)))
    (hreqOf : Ok → ∀ k, Field.isBottom (F k) = true → ∃ t, F k = .req t)
    (hfbM : Ok → ∀ keys : Finset Name,
      fbNames keys ⟨Body.shared a b, fun k => fieldSem (F k)⟩ = ∅)
    (hfbA : Ok → ∀ {keys : Finset Name} {g : {k // k ∈ keys} → Attr},
      AdmA (.object b) (.m keys g) = true →
      fbNames keys ⟨a.fields, fun k => fieldSem (a.at k)⟩ = ∅)
    (hfbB : Ok → ∀ {keys : Finset Name} {g : {k // k ∈ keys} → Attr},
      AdmA (.object a) (.m keys g) = true →
      fbNames keys ⟨b.fields, fun k => fieldSem (b.at k)⟩ = ∅)
    (ihf : Ok → ∀ (k : {k // k ∈ Body.shared a b}),
      (∀ c, AdmAField (F k) c
        = (AdmAField (a.at ⟨k.1, Body.mem_shared_left k.2⟩) c
            && AdmAField (b.at ⟨k.1, Body.mem_shared_right k.2⟩) c))
      ∧ (∀ c, AdmAField (a.at ⟨k.1, Body.mem_shared_left k.2⟩) c = true →
          AdmAField (b.at ⟨k.1, Body.mem_shared_right k.2⟩) c = true →
          (fieldSem (F k)).codec.p c
              = (fieldSem (a.at ⟨k.1, Body.mem_shared_left k.2⟩)).codec.p c
            ∧ (fieldSem (F k)).codec.p c
              = (fieldSem (b.at ⟨k.1, Body.mem_shared_right k.2⟩)).codec.p c))
    (hcase : (z = .never ∧ ¬ (Body.reqShared a b = true ∧ Body.reqShared b a = true))
             ∨ (Body.reqShared a b = true ∧ Body.reqShared b a = true ∧ Ok ∧
                ((z = .never ∧ ¬ (∀ k, Field.isBottom (F k) = false))
                 ∨ z = .object (.mk (Body.shared a b) F r)))) :
    (∀ c, AdmA z c = (AdmA (.object a) c && AdmA (.object b) c)) ∧
    (∀ c, AdmA (.object a) c = true → AdmA (.object b) c = true →
      (denote z).p c = (denote (.object a)).p c ∧ (denote z).p c = (denote (.object b)).p c) := by
  -- an attribute that is not a map is read by no object
  have hnm : ∀ c : Attr, (∀ keys g, c ≠ .m keys g) →
      AdmA z c = (AdmA (.object a) c && AdmA (.object b) c) := by
    intro c hc
    rw [AdmA_object a c,
        AdmA_object b c,
        AdmABody_of_not_m hc, AdmABody_of_not_m hc, Bool.and_self]
    rcases hcase with ⟨rfl, _⟩ | ⟨_, _, _, ⟨rfl, _⟩ | rfl⟩
    · rfl
    · rfl
    · exact AdmABody_of_not_m hc
  -- the first half
  have half1 : ∀ c, AdmA z c = (AdmA (.object a) c && AdmA (.object b) c) := by
    intro c
    cases c
    case m keys g =>
      rw [AdmA_object a (.m keys g),
          AdmA_object b (.m keys g)]
      rcases hcase with ⟨rfl, hne⟩ | ⟨hab, hba, hok, ⟨rfl, hnb⟩ | rfl⟩
      · show (false : Bool) = _
        cases hA : AdmABody a (.m keys g) with
        | false => rfl
        | true =>
          cases hB : AdmABody b (.m keys g) with
          | false => rfl
          | true =>
            exact absurd ⟨reqShared_of_admA hr hfba hdb hA hB,
              reqShared_of_admA ((merge_comm a.rest b.rest) ▸ hr) hfbb hda hB hA⟩ hne
      · show (false : Bool) = _
        cases hA : AdmABody a (.m keys g) with
        | false => rfl
        | true =>
          cases hB : AdmABody b (.m keys g) with
          | false => rfl
          | true =>
            exact absurd (isBottom_false_of_admA_bodies (hisreqA hok) (hreqOf hok) (fun k c => (ihf hok k).1 c) hA hB) hnb
      · show AdmABody (.mk (Body.shared a b) F r)
            (.m keys g) = _
        rw [AdmABody_map, AdmABody_map, AdmABody_map]
        simp only [Body.fields_mk, Body.at_mk, Body.rest_mk]
        rw [reqPresentT_of_bodies hab hba (hisreqA hok), objAdmA_of_bodies hr hda hdb (fun k c => (ihf hok k).1 c)]
        simp [Bool.and_assoc, Bool.and_left_comm]
    all_goals exact hnm _ (fun _ _ hc => Attr.noConfusion hc)
  refine ⟨half1, fun c hA hB => ?_⟩
  cases c
  case m keys g =>
    rw [AdmA_object a (.m keys g)] at hA
    rw [AdmA_object b (.m keys g)] at hB
    rcases hcase with ⟨rfl, hne⟩ | ⟨hab, hba, hok, ⟨rfl, hnb⟩ | rfl⟩
    · exact absurd ⟨reqShared_of_admA hr hfba hdb hA hB,
        reqShared_of_admA ((merge_comm a.rest b.rest) ▸ hr) hfbb hda hB hA⟩ hne
    · exact absurd (isBottom_false_of_admA_bodies (hisreqA hok) (hreqOf hok) (fun k c => (ihf hok k).1 c) hA hB) hnb
    · rw [AdmABody_map, Bool.and_eq_true] at hA hB
      have hreqA := hA.1
      have hreqB := hB.1
      have hAo : AdmA (.object a) (.m keys g) = true := by
        rw [AdmA_object a (.m keys g), AdmABody_map,
          Bool.and_eq_true]
        exact ⟨hA.1, hA.2⟩
      have hBo : AdmA (.object b) (.m keys g) = true := by
        rw [AdmA_object b (.m keys g), AdmABody_map,
          Bool.and_eq_true]
        exact ⟨hB.1, hB.2⟩
      -- the entry agreement, against whichever factor the congruence is applied to
      have hentry : ∀ (k : Name) (hk : k ∈ keys), keepT r (Body.shared a b) k = true →
          ∀ (hks : k ∈ Body.shared a b),
            (fieldSem (F ⟨k, hks⟩)).codec.p (g ⟨k, hk⟩)
                = (fieldSem (a.at ⟨k, Body.mem_shared_left hks⟩)).codec.p (g ⟨k, hk⟩)
              ∧ (fieldSem (F ⟨k, hks⟩)).codec.p (g ⟨k, hk⟩)
                = (fieldSem (b.at ⟨k, Body.mem_shared_right hks⟩)).codec.p (g ⟨k, hk⟩) := by
        intro k hk _ hks
        exact (ihf hok ⟨k, hks⟩).2 (g ⟨k, hk⟩)
          (objAdmA_row hA.2 hk (Body.mem_shared_left hks) (keepT_of_mem (Body.mem_shared_left hks)))
          (objAdmA_row hB.2 hk (Body.mem_shared_right hks)
            (keepT_of_mem (Body.mem_shared_right hks)))
      have hfilA : ∀ k ∈ keys, keepT r (Body.shared a b) k = keepT a.rest a.fields k :=
        keepT_agree hr hda hdb hBo
      have hfilB : ∀ k ∈ keys, keepT r (Body.shared a b) k = keepT b.rest b.fields k := by
        intro k hk
        rw [Body.shared_comm]
        exact keepT_agree ((merge_comm a.rest b.rest) ▸ hr) hdb hda hAo k hk
      constructor
      · refine bodySem_p_congr (b := .mk (Body.shared a b) F r)
          ?_ (hfbM hok keys) (hfbA hok hBo)
          (filter_congr_on (fun k hk => by
            simp only [Body.fields_mk, Body.rest_mk]; exact hfilA k hk))
          (fun k hk hkeep => ?_)
        · simp only [Body.fields_mk, Body.at_mk]
          rw [reqPresentT_of_bodies hab hba (hisreqA hok), hreqA, hreqB]
          rfl
        · simp only [Body.fields_mk, Body.at_mk, Body.rest_mk] at hkeep ⊢
          have hks := mem_shared_of_keep hr hda hdb hAo hBo hk hkeep
          rw [entryCodec_mk_pos hks, entryCodec_mk_pos (Body.mem_shared_left hks)]
          exact (hentry k hk hkeep hks).1
      · refine bodySem_p_congr (b := .mk (Body.shared a b) F r)
          ?_ (hfbM hok keys) (hfbB hok hAo)
          (filter_congr_on (fun k hk => by
            simp only [Body.fields_mk, Body.rest_mk]; exact hfilB k hk))
          (fun k hk hkeep => ?_)
        · simp only [Body.fields_mk, Body.at_mk]
          rw [reqPresentT_of_bodies hab hba (hisreqA hok), hreqA, hreqB]
          rfl
        · simp only [Body.fields_mk, Body.at_mk, Body.rest_mk] at hkeep ⊢
          have hks := mem_shared_of_keep hr hda hdb hAo hBo hk hkeep
          rw [entryCodec_mk_pos hks, entryCodec_mk_pos (Body.mem_shared_right hks)]
          exact (hentry k hk hkeep hks).2
  all_goals exact absurd hA (by rw [AdmA_object a _,
    AdmABody_of_not_m (fun _ _ hc => Attr.noConfusion hc)]; exact Bool.noConfusion)

/-- **The transport into a record's reading.** An object whose keep filter drops nothing writes
    the map's own key set, and the stand-in branch is unreachable, so its output is the record's.
    The filter is a variable again, so `subst` carries the membership proof inside the entry. -/
theorem funImage_record_congr {S T : Finset Name} (hS : S = T)
    {g : {k // k ∈ S} → Option Value} {g' : {k // k ∈ T} → Option Value}
    (hg : ∀ (k : Name) (h : k ∈ S) (h' : k ∈ T), g ⟨k, h⟩ = g' ⟨k, h'⟩)
    {fb : Name → Option Value} :
    (funImage g).map (mapV.into ∘ fun d => (⟨S ∪ ∅, fun k => if h : k.1 ∈ S then d ⟨k.1, h⟩
        else (fb k.1).getD .null⟩ : MapOf Value))
      = (funImage g').map (Value.map T) := by
  subst hS
  have himg : g = g' := funext fun k => hg k.1 k.2 k.2
  subst himg
  refine congrArg (fun F => Option.map F (funImage g)) (funext fun d => ?_)
  show mapV.into _ = mapV.into ⟨S, d⟩
  exact congrArg mapV.into (MapOf.ext (Finset.union_empty S) (fun k _ h2 => dif_pos h2))

/-- **The object-against-record congruence.** `objRec` answers an object whose rest is a
    codec, so the keep filter is constantly true and no name of the map is dropped. With no
    stand-in declared, the output key set is the map's own, which is what the record writes, and
    the two agree entry by entry. -/
theorem bodySem_p_record_congr {b : Body} {t x : Term}
    {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hrest : b.rest = .codec t)
    (hreq : reqPresentT b.fields b.at keys = true)
    (hfb : fbNames keys ⟨b.fields, fun k => fieldSem (b.at k)⟩ = ∅)
    (hent : ∀ (k : Name) (h : k ∈ keys),
      (entryCodec ⟨b.fields, fun k => fieldSem (b.at k)⟩ (rcOf (restSem b.rest)) k).bind
          (fun c => c.p (g ⟨k, h⟩))
        = (denote x).p (g ⟨k, h⟩)) :
    (denote (.object b)).p (.m keys g) = (denote (.record x)).p (.m keys g) := by
  have hb : (denote (.object b)).p (.m keys g)
      = (objRead ⟨b.fields, fun k => fieldSem (b.at k)⟩ (rcOf (restSem b.rest))
          (keepB (restSem b.rest) ⟨b.fields, fun k => fieldSem (b.at k)⟩)
          ⟨keys, g⟩).map mapV.into := by
    cases b; rfl
  have hkn : ∀ k, keepB (restSem b.rest) ⟨b.fields, fun k => fieldSem (b.at k)⟩ k = true := by
    intro k; rw [keepB_eq b.fields b.at b.rest k, hrest]; rfl
  have hfil : keys.filter
      (keepB (restSem b.rest) ⟨b.fields, fun k => fieldSem (b.at k)⟩ ·) = keys :=
    filter_eq_self_on (fun k _ => hkn k)
  rw [hb, show (denote (.record x)).p (.m keys g)
      = (funImage (fun k => (denote x).p (g k))).map (Value.map keys) from rfl]
  unfold objRead
  rw [show reqPresentB ⟨b.fields, fun k => fieldSem (b.at k)⟩ (⟨keys, g⟩ : MapOf Attr).1 = true from
    by rw [← reqPresentT_eq]; exact hreq, if_pos rfl, hfb]
  simp only [Option.map_map]
  exact funImage_record_congr hfil
    (fun k h _ => hent k (Finset.mem_filter.mp h).1)

/-- **An object against a record, over an abstract field table.** Everything after the field
    agreement reads that agreement alone, so the well-founded caller and the structural one share
    this. -/
theorem record_row_gen {b : Body} {x z t r : Term} {F : {k // k ∈ b.fields} → Field}
    (hrest : b.rest = .codec t)
    (hreqA : ∀ k, Field.isReqA (F k) = Field.isReqA (b.at k))
    (hnfb : ∀ (k : {k // k ∈ b.fields}) (u : Term) (d : Value), F k ≠ .fallback u d)
    (hnfbSrc : ∀ (k : {k // k ∈ b.fields}) (u : Term) (d : Value), b.at k ≠ .fallback u d)
    (ihtA : ∀ c, AdmA r c = (AdmA t c && AdmA x c))
    (ihtP : ∀ c, AdmA t c = true → AdmA x c = true →
      (denote r).p c = (denote t).p c ∧ (denote r).p c = (denote x).p c)
    (ihf : ∀ (k : {k // k ∈ b.fields}),
      (∀ c, AdmAField (F k) c = (AdmAField (b.at k) c && AdmA x c))
      ∧ (∀ c, AdmAField (b.at k) c = true → AdmA x c = true →
          (fieldSem (F k)).codec.p c = (fieldSem (b.at k)).codec.p c
            ∧ (fieldSem (F k)).codec.p c = (denote x).p c))
    (hcase : (z = .never ∧ ¬ (∀ k, Field.isBottom (F k) = false))
             ∨ z = .object (.mk b.fields F (.codec r))) :
    (∀ c, AdmA z c = (AdmA (.object b) c && AdmA (.record x) c)) ∧
    (∀ c, AdmA (.object b) c = true → AdmA (.record x) c = true →
      (denote z).p c = (denote (.object b)).p c ∧ (denote z).p c = (denote (.record x)).p c) := by
  have hnm : ∀ c : Attr, (∀ keys g, c ≠ .m keys g) →
      AdmA z c = (AdmA (.object b) c && AdmA (.record x) c) := by
    intro c hc
    have hrx : AdmA (.record x) c = false := by cases c with
      | m keys g => exact absurd rfl (hc keys g)
      | _ => rfl
    rw [AdmA_object b c, AdmABody_of_not_m hc, hrx, Bool.and_self]
    rcases hcase with ⟨rfl, _⟩ | rfl
    · rfl
    · exact AdmABody_of_not_m hc
  have half1 : ∀ c, AdmA z c = (AdmA (.object b) c && AdmA (.record x) c) := by
    intro c
    cases c
    case m keys g =>
      rw [AdmA_object b (.m keys g),
          AdmA_record x keys g]
      rcases hcase with ⟨rfl, hnb⟩ | rfl
      · show (false : Bool) = _
        cases hA : AdmABody b (.m keys g) with
        | false => rfl
        | true =>
          cases hR : decide (∀ k : {k // k ∈ keys}, AdmA x (g k) = true) with
          | false => rfl
          | true =>
            exact absurd (isBottom_false_of_admA_right hreqA hnfb (fun k c => (ihf k).1 c) hA hR) hnb
      · show AdmABody (.mk b.fields F (.codec r))
            (.m keys g) = _
        rw [AdmABody_map, AdmABody_map]
        simp only [Body.fields_mk, Body.at_mk, Body.rest_mk, hrest]
        rw [reqPresentT_of_isReqA hreqA, show AdmARest (.codec r) = some (AdmA r) from rfl,
            show AdmARest (.codec t) = some (AdmA t) from rfl,
            objAdmA_of_right hrest (fun k c => (ihf k).1 c) ihtA]
        simp only [hrest]
        simp [Bool.and_assoc, Bool.and_left_comm]
    all_goals exact hnm _ (fun _ _ hc => Attr.noConfusion hc)
  refine ⟨half1, fun c hA hR => ?_⟩
  cases c
  case m keys g =>
    rw [AdmA_object b (.m keys g)] at hA
    rw [AdmA_record x keys g] at hR
    rcases hcase with ⟨rfl, hnb⟩ | rfl
    · exact absurd (isBottom_false_of_admA_right hreqA hnfb (fun k c => (ihf k).1 c) hA hR) hnb
    · rw [AdmABody_map, Bool.and_eq_true] at hA
      have hrec : ∀ (k : Name) (hk : k ∈ keys), AdmA x (g ⟨k, hk⟩) = true :=
        fun k hk => of_decide_eq_true hR ⟨k, hk⟩
      -- the rest codec's row, at a name the object does not declare
      have hrestrow : ∀ (k : Name) (hk : k ∈ keys), k ∉ b.fields → AdmA t (g ⟨k, hk⟩) = true := by
        intro k hk hnf
        have hh := of_decide_eq_true hA.2 ⟨k, hk⟩ (by rw [hrest]; rfl)
        simpa only [entryPA,
          MapOf.at_of_not_mem (m := ⟨b.fields, fun k => AdmAField (b.at k)⟩) hnf, hrest,
          AdmARest] using hh
      -- the entry agreement, shared by the two congruences
      have hentry : ∀ (k : Name) (hk : k ∈ keys),
          ((entryCodec ⟨b.fields, fun k => fieldSem (F k)⟩
              (rcOf (restSem (Rest.codec r))) k).bind (fun c => c.p (g ⟨k, hk⟩))
            = (entryCodec ⟨b.fields, fun k => fieldSem (b.at k)⟩ (rcOf (restSem b.rest)) k).bind
              (fun c => c.p (g ⟨k, hk⟩)))
          ∧ ((entryCodec ⟨b.fields, fun k => fieldSem (F k)⟩
              (rcOf (restSem (Rest.codec r))) k).bind (fun c => c.p (g ⟨k, hk⟩))
            = (denote x).p (g ⟨k, hk⟩)) := by
        intro k hk
        by_cases hf : k ∈ b.fields
        · rw [entryCodec_mk_pos hf, entryCodec_mk_pos hf]
          exact (ihf ⟨k, hf⟩).2 (g ⟨k, hk⟩)
            (objAdmA_row hA.2 hk hf (keepT_of_mem hf)) (hrec k hk)
        · rw [entryCodec_mk_neg (f := fun k => fieldSem (F k)) hf,
            entryCodec_mk_neg (f := fun k => fieldSem (b.at k)) hf, hrest]
          exact ihtP (g ⟨k, hk⟩) (hrestrow k hk hf) (hrec k hk)
      constructor
      · refine bodySem_p_congr (b := .mk b.fields F (.codec r))
          ?_ (fbNames_empty_of_not_fallback hnfb keys) (fbNames_empty_of_not_fallback hnfbSrc keys)
          (filter_congr_on (fun k _ => by simp [hrest, keepT, Body.rest_mk]))
          (fun k hk _ => ?_)
        · simp only [Body.fields_mk, Body.at_mk]; exact reqPresentT_of_isReqA hreqA keys
        · simpa only [Body.fields_mk, Body.at_mk, Body.rest_mk] using (hentry k hk).1
      · refine bodySem_p_record_congr (b := .mk b.fields F
          (.codec r)) rfl ?_ (fbNames_empty_of_not_fallback hnfb keys) (fun k hk => ?_)
        · simp only [Body.fields_mk, Body.at_mk]
          rw [reqPresentT_of_isReqA hreqA keys]; exact hA.1
        · simpa only [Body.fields_mk, Body.at_mk, Body.rest_mk] using (hentry k hk).2
  all_goals exact absurd hA (by rw [AdmA_object b _,
    AdmABody_of_not_m (fun _ _ hc => Attr.noConfusion hc)]; exact Bool.noConfusion)

section StructuralAdmA
-- the object rows put the whole field table to `decide` under a binder
set_option maxHeartbeats 1000000

/-! ## The read side's homomorphism and its reading agreement, structurally

The same three layers the value side uses. The depth bounds are gone with the measure: the list
and tail lifts have measure-free twins here, and the object rows go through `record_row_gen` and
`object_row_gen`, the general field-table forms that the well-founded proof now shares. -/

/-- The conclusion of the read-side homomorphism, at one pair. -/
abbrev AdmAAt (x y z : Term) : Prop :=
  (∀ a : Attr, AdmA z a = (AdmA x a && AdmA y a)) ∧
  (∀ a : Attr, AdmA x a = true → AdmA y a = true →
    (denote z).p a = (denote x).p a ∧ (denote z).p a = (denote y).p a)

/-- `f` answers the read side with one term fixed on the left, at every right operand. -/
def AdmASound (x : Term) (f : Term → Option Term) : Prop :=
  ∀ y z, f y = some z → AdmAAt x y z

/-- …and over the operands the shared inner hands a family. -/
def AdmAFam (x : Term) (fam : Term → Option Term) : Prop :=
  ∀ y z, Delegated y → fam y = some z → AdmAAt x y z

mutual
/-- Every row that reads the right operand alone reads what the family reads. -/
theorem admA_meetSRight {x : Term} {fam : Term → Option Term} (hf : AdmAFam x fam) :
    ∀ y z, meetSRight fam y = some z → AdmAAt x y z
  | .never, _, h => by
      simp only [meetSRight, Option.some.injEq] at h; subst h
      exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩
  | .held _ _ _, _, h => by simp [meetSRight] at h
  | .legacy _ _, _, h => by simp [meetSRight] at h
  | .custom _ _, _, h => by simp [meetSRight] at h
  | .lazy _, _, h => by simp [meetSRight] at h
  | .refine y p, _, h => by
      simp only [meetSRight] at h
      split at h
      · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨ih1, ih2⟩ := admA_meetSRight hf y w hw
        exact refine_row_r ih1 ih2
      · exact absurd h (by simp)
  | .union os, _, h => by
      obtain ⟨zs, hF, hco, hcz, rfl⟩ := meetSRight_union h
      have hB := admA_meetSRightL hf os zs hF
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · rw [AdmA_ofOptions hcz, AdmAAny_filter_never,
          AdmA_union _ a, selOptA_eq_AdmAAny hco, Bool.and_comm]
        exact AdmAAny_meet a (List.Forall₂.imp (fun _ _ hh => hh.1) hB)
      · obtain ⟨t, hft, hta⟩ :=
          filter_eq_singleton_of_selOptA (show selOptA (AdmASpecs _) a = true from hb)
        obtain ⟨w, hwmem, hwA, hwP⟩ := forall₂_mem_left hB (mem_of_filter_eq_singleton hft).1
        have hwa : AdmA w a = true := by rw [hwA a, hta, ha]; rfl
        have hsurv : w ∈ zs.filter (fun z => !z.isNever) :=
          List.mem_filter.mpr ⟨hwmem, by rw [not_isNever_of_admA hwa]; rfl⟩
        obtain ⟨u, hfu, _⟩ := filter_eq_singleton_of_selOptA
          (show selOptA (AdmASpecs (zs.filter (fun z => !z.isNever))) a = true by
            rw [selOptA_eq_AdmAAny hcz]; exact AdmAAny_of_mem hsurv hwa)
        have hwu : w = u := by
          have hm : w ∈ (zs.filter (fun z => !z.isNever)).filter
              (fun v => admitOptA (specOf v, AdmA v) a) :=
            List.mem_filter.mpr ⟨hsurv, admitOptA_of_AdmA hcz hsurv hwa⟩
          rw [hfu, List.mem_singleton] at hm
          exact hm
        subst hwu
        rw [ofOptions_p_of_filter hfu, union_p_of_filter hft]
        exact ⟨(hwP a hta ha).2, (hwP a hta ha).1⟩
  | .string, _, h => hf .string _ trivial h
  | .number, _, h => hf .number _ trivial h
  | .decimal, _, h => hf .decimal _ trivial h
  | .boolean, _, h => hf .boolean _ trivial h
  | .binary, _, h => hf .binary _ trivial h
  | .null, _, h => hf .null _ trivial h
  | .literal k lv, _, h => hf (.literal k lv) _ trivial h
  | .set b, _, h => hf (.set b) _ trivial h
  | .opaq l, _, h => hf (.opaq l) _ trivial h
  | .array e, _, h => hf (.array e) _ trivial h
  | .record c, _, h => hf (.record c) _ trivial h
  | .tuple ts tl, _, h => hf (.tuple ts tl) _ trivial h
  | .object b, _, h => hf (.object b) _ trivial h
termination_by structural y => y

/-- The union row's options, lifted pointwise. -/
theorem admA_meetSRightL {x : Term} {fam : Term → Option Term} (hf : AdmAFam x fam) :
    ∀ os zs, List.Forall₂ (fun t w => meetSRight fam t = some w) os zs →
      List.Forall₂ (fun t w =>
        (∀ b, AdmA w b = (AdmA t b && AdmA x b)) ∧
        (∀ b, AdmA t b = true → AdmA x b = true →
          (denote w).p b = (denote t).p b ∧ (denote w).p b = (denote x).p b)) os zs
  | [], _, h => by cases h; exact .nil
  | t :: ts, _, h => by
      cases h with
      | cons hh ht =>
          obtain ⟨h1, h2⟩ := admA_meetSRight hf t _ hh
          exact .cons ⟨fun b => by rw [h1 b, Bool.and_comm],
            fun b hbt hbx => ⟨(h2 b hbx hbt).2, (h2 b hbx hbt).1⟩⟩ (admA_meetSRightL hf ts _ ht)
termination_by structural os => os
end

/-- The catch-all of every family: two constructors in different attribute slots read nothing
    together, so the pair is the bottom. -/
local macro "admA_never" fam:ident : tactic => `(tactic|
  (simp only [$fam:ident, Option.some.injEq] at *
   subst_vars
   refine bottom_row (fun a => ?_)
   first
     | (refine Eq.trans ?g1 (AdmA_and_false ?g2 a).symm
        case g2 =>
          first
            | rfl
            | (cases ‹GroundKind› <;> rfl)
            | (cases ‹SetBase› <;> rfl)
            | (cases ‹GroundKind› <;> cases ‹SetBase› <;> rfl)
        case g1 => rfl)
     | (cases a <;> simp [AdmA, inD, isStored])))

/-- The base row: the same constructor on both sides is reflexive on both halves. -/
theorem admA_same (x : Term) : AdmAAt x x x :=
  ⟨fun a => (Bool.and_self _).symm, fun a _ _ => ⟨rfl, rfl⟩⟩

/-- `string` reads `S`, and what it meets reads the same attribute. -/
theorem admA_famString : AdmAFam Term.string famString := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case string => simp only [famString, Option.some.injEq] at h; subst h; exact admA_same _
  case decimal => simp [famString] at h
  case literal k lv =>
      cases k <;> simp only [famString, Option.some.injEq, reduceCtorEq] at h <;>
        (try subst h) <;>
        first
          | (refine ⟨fun a => ?_, fun a ha hb => ⟨literal_denote_agree hb, rfl⟩⟩
             cases hx : AdmA (Term.literal _ _) a with
             | false => simp
             | true => rw [AdmA_base_of_literal rfl hx]; simp)
          | (refine bottom_row (fun a => ?_)
             cases a <;> simp_all [AdmA, AdmALit, inL, inD, isStored, literalCodec,
               Codec.restrict, baseCodec, decimalCodec])
  case opaq l =>
      simp only [famString, Option.some.injEq] at h; subst h
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · cases a <;>
          (try simp only [AdmA_opaq_str, AdmA_opaq_bool, AdmA_opaq_bin, AdmA_opaq_null]) <;>
          simp [AdmA]
      · cases a <;> refine ⟨?_, ?_⟩ <;>
          simp_all [AdmA, opaq_p_string, opaq_p_boolean, opaq_p_binary, opaq_p_null]
  all_goals admA_never famString

/-- `boolean` reads `BOOL`, and what it meets reads the same attribute. -/
theorem admA_famBoolean : AdmAFam Term.boolean famBoolean := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case boolean => simp only [famBoolean, Option.some.injEq] at h; subst h; exact admA_same _
  case literal k lv =>
      simp only [famBoolean] at h
      split at h
      next hk =>
        subst hk
        simp only [Option.some.injEq] at h; subst h
        refine ⟨fun a => ?_, fun a ha hb => ⟨literal_denote_agree hb, rfl⟩⟩
        cases hx : AdmA (Term.literal _ _) a with
        | false => simp
        | true => rw [AdmA_base_of_literal rfl hx]; simp
      next hk =>
        simp only [Option.some.injEq] at h; subst h
        refine bottom_row (fun a => ?_)
        cases k <;> cases a <;> simp_all [AdmA, AdmALit, inL, inD, isStored, literalCodec,
          Codec.restrict, baseCodec, decimalCodec]
  case opaq l =>
      simp only [famBoolean, Option.some.injEq] at h; subst h
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · cases a <;>
          (try simp only [AdmA_opaq_str, AdmA_opaq_bool, AdmA_opaq_bin, AdmA_opaq_null]) <;>
          simp [AdmA]
      · cases a <;> refine ⟨?_, ?_⟩ <;>
          simp_all [AdmA, opaq_p_string, opaq_p_boolean, opaq_p_binary, opaq_p_null]
  all_goals admA_never famBoolean

/-- `binary` reads `B`, and what it meets reads the same attribute. -/
theorem admA_famBinary : AdmAFam Term.binary famBinary := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case binary => simp only [famBinary, Option.some.injEq] at h; subst h; exact admA_same _
  case literal k lv =>
      simp only [famBinary] at h
      split at h
      next hk =>
        subst hk
        simp only [Option.some.injEq] at h; subst h
        refine ⟨fun a => ?_, fun a ha hb => ⟨literal_denote_agree hb, rfl⟩⟩
        cases hx : AdmA (Term.literal _ _) a with
        | false => simp
        | true => rw [AdmA_base_of_literal rfl hx]; simp
      next hk =>
        simp only [Option.some.injEq] at h; subst h
        refine bottom_row (fun a => ?_)
        cases k <;> cases a <;> simp_all [AdmA, AdmALit, inL, inD, isStored, literalCodec,
          Codec.restrict, baseCodec, decimalCodec]
  case opaq l =>
      simp only [famBinary, Option.some.injEq] at h; subst h
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · cases a <;>
          (try simp only [AdmA_opaq_str, AdmA_opaq_bool, AdmA_opaq_bin, AdmA_opaq_null]) <;>
          simp [AdmA]
      · cases a <;> refine ⟨?_, ?_⟩ <;>
          simp_all [AdmA, opaq_p_string, opaq_p_boolean, opaq_p_binary, opaq_p_null]
  all_goals admA_never famBinary

/-- `null` reads `NULL`, and what it meets reads the same attribute. -/
theorem admA_famNull : AdmAFam Term.null famNull := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case null => simp only [famNull, Option.some.injEq] at h; subst h; exact admA_same _
  case literal k lv =>
      simp only [famNull] at h
      split at h
      next hk =>
        subst hk
        simp only [Option.some.injEq] at h; subst h
        refine ⟨fun a => ?_, fun a ha hb => ⟨literal_denote_agree hb, rfl⟩⟩
        cases hx : AdmA (Term.literal _ _) a with
        | false => simp
        | true => rw [AdmA_base_of_literal rfl hx]; simp
      next hk =>
        simp only [Option.some.injEq] at h; subst h
        refine bottom_row (fun a => ?_)
        cases k <;> cases a <;> simp_all [AdmA, AdmALit, inL, inD, isStored, literalCodec,
          Codec.restrict, baseCodec, decimalCodec]
  case opaq l =>
      simp only [famNull, Option.some.injEq] at h; subst h
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · cases a <;>
          (try simp only [AdmA_opaq_str, AdmA_opaq_bool, AdmA_opaq_bin, AdmA_opaq_null]) <;>
          simp [AdmA]
      · cases a <;> refine ⟨?_, ?_⟩ <;>
          simp_all [AdmA, opaq_p_string, opaq_p_boolean, opaq_p_binary, opaq_p_null]
  all_goals admA_never famNull

/-- `number` reads a stored double, and refuses the `decimal` family. -/
theorem admA_famNumber : AdmAFam Term.number famNumber := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case number => simp only [famNumber, Option.some.injEq] at h; subst h; exact admA_same _
  case decimal => simp [famNumber] at h
  case literal k lv =>
      cases k <;> simp only [famNumber, Option.some.injEq, reduceCtorEq] at h <;>
        (try subst h) <;>
        first
          | (refine ⟨fun a => ?_, fun a ha hb => ⟨literal_denote_agree hb, rfl⟩⟩
             cases hx : AdmA (Term.literal _ _) a with
             | false => simp
             | true => rw [AdmA_base_of_literal rfl hx]; simp)
          | (refine bottom_row (fun a => ?_)
             cases a <;> simp_all [AdmA, AdmALit, inL, inD, isStored, literalCodec,
               Codec.restrict, baseCodec, decimalCodec])
  case opaq l =>
      simp only [famNumber] at h
      split at h
      next hl =>
        subst hl
        simp only [Option.some.injEq] at h; subst h
        refine ⟨fun a => ?_, fun a ha hb => ?_⟩
        · cases a <;>
            (try simp only [AdmA_opaq_num, AdmA_number_eq, Bool.true_and, Bool.and_self]) <;>
            simp [AdmA]
        · cases a <;> refine ⟨?_, ?_⟩ <;> simp_all [AdmA, opaq_p_number]
      next hl =>
        simp only [Bool.not_eq_true] at hl; subst hl
        simp only [Option.some.injEq] at h; subst h
        refine bottom_row (fun a => ?_)
        cases a <;> (try simp only [AdmA_opaq_num]) <;> simp [AdmA, inD]
  all_goals admA_never famNumber

/-- `decimal` reads a stored numeral, and refuses `string` and `number`. -/
theorem admA_famDecimal : AdmAFam Term.decimal famDecimal := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case decimal => simp only [famDecimal, Option.some.injEq] at h; subst h; exact admA_same _
  case string => simp [famDecimal] at h
  case number => simp [famDecimal] at h
  case opaq l => simp [famDecimal] at h
  case literal k lv =>
      cases k <;> simp only [famDecimal, Option.some.injEq, reduceCtorEq] at h <;>
        (try subst h) <;>
        first
          | (refine ⟨fun a => ?_, fun a ha hb => ⟨literal_denote_agree hb, rfl⟩⟩
             cases hx : AdmA (Term.literal _ _) a with
             | false => simp
             | true => rw [AdmA_base_of_literal rfl hx]; simp)
          | (refine bottom_row (fun a => ?_)
             cases a <;> simp_all [AdmA, AdmALit, inL, inD, isStored, literalCodec,
               Codec.restrict, baseCodec, decimalCodec])
  all_goals admA_never famDecimal

/-- A literal reads its own value and nothing else, and its base reads it too. -/
theorem admA_famLit (k : GroundKind) (lv : k.Carrier) :
    AdmAFam (.literal k lv) (famLit k lv) := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case literal k' lv' =>
      simp only [famLit] at h
      cases k <;> cases k' <;> simp only [Term.meetLit, reduceCtorEq] at h <;>
        (try split at h) <;>
        (try (simp only [Option.some.injEq] at h
              subst h
              subst_vars
              first
                | exact admA_same _
                | (refine bottom_row (fun a => ?_)
                   first
                     | exact AdmALit_never_of_ne (by assumption) a
                     | (cases a <;> simp_all [AdmA, AdmALit, inL, inD, isStored,
                          literalCodec_p_restrict, Codec.restrict, baseCodec, decimalCodec,
                          numberCodec, stringCodec, booleanCodec, binaryCodec, nullCodec]))))
  case string | number | decimal | boolean | binary | null =>
      cases k <;>
        simp only [famLit, reduceCtorEq, reduceIte, Option.some.injEq] at h <;>
        (try subst h) <;>
        first
          | (refine ⟨fun a => ?_, fun a ha hb => ⟨rfl, literal_denote_agree ha⟩⟩
             cases hx : AdmA (Term.literal _ _) a with
             | false => simp
             | true => rw [AdmA_base_of_literal rfl hx]; simp)
          | (refine bottom_row (fun a => ?_)
             cases a <;> simp_all [AdmA, AdmALit, inL, inD, isStored, literalCodec,
               Codec.restrict, baseCodec, decimalCodec])
  case opaq l => simp [famLit] at h
  all_goals admA_never famLit

/-- Two set bases read together where they are equal. -/
theorem admA_famSet (b : SetBase) : AdmAFam (.set b) (famSet b) := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case set b' =>
      cases b <;> cases b' <;>
        simp only [famSet, reduceCtorEq, reduceIte, Option.some.injEq] at h <;>
        (try subst h) <;>
        first
          | exact admA_same _
          | (refine bottom_row (fun a => ?_)
             cases a <;> simp_all [AdmA, AdmASet, isStored])
  case opaq l => simp [famSet] at h
  all_goals admA_never famSet

/-- `opaque` reads each self-identifying base, and conjoins with another `opaque`. -/
theorem admA_famOpaq (l : Bool) : AdmAFam (.opaq l) (famOpaq l) := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case string | boolean | binary | null =>
      simp only [famOpaq, Option.some.injEq] at h; subst h
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · cases a <;>
          (try simp only [AdmA_opaq_str, AdmA_opaq_bool, AdmA_opaq_bin, AdmA_opaq_null]) <;>
          simp [AdmA]
      · cases a <;> refine ⟨?_, ?_⟩ <;>
          simp_all [AdmA, opaq_p_string, opaq_p_boolean, opaq_p_binary, opaq_p_null]
  case number =>
      simp only [famOpaq] at h
      split at h
      next hl =>
        subst hl
        simp only [Option.some.injEq] at h; subst h
        refine ⟨fun a => ?_, fun a ha hb => ?_⟩
        · cases a <;>
            (try simp only [AdmA_opaq_num, AdmA_number_eq, Bool.true_and, Bool.and_self]) <;>
            simp [AdmA]
        · cases a <;> refine ⟨?_, ?_⟩ <;> simp_all [AdmA, opaq_p_number]
      next hl =>
        simp only [Bool.not_eq_true] at hl; subst hl
        simp only [Option.some.injEq] at h; subst h
        refine bottom_row (fun a => ?_)
        cases a <;> (try simp only [AdmA_opaq_num]) <;> simp [AdmA, inD]
  case opaq l' =>
      simp only [famOpaq, Option.some.injEq] at h; subst h
      refine ⟨AdmA_opaq_and l l', fun a ha hb => ⟨?_, ?_⟩⟩ <;>
        cases l <;> cases l' <;>
        first
          | rfl
          | exact (opaq_p_lossy ha).symm
          | exact (opaq_p_lossy hb).symm
  all_goals simp [famOpaq] at h


/-! ### The container families. The lifts are measure-free. -/

/-- Both halves at one element, from the soundness of the call the family carries. -/
theorem admA_split {e : Term} {f : Term → Option Term} (hf : AdmASound e f)
    {t v : Term} (hv : f t = some v) (b : Attr) (hb : AdmA v b = true) :
    AdmA e b = true ∧ AdmA t b = true ∧
      (denote v).p b = (denote e).p b ∧ (denote v).p b = (denote t).p b := by
  obtain ⟨h1, h2⟩ := hf t v hv
  rw [h1 b, Bool.and_eq_true] at hb
  exact ⟨hb.1, hb.2, h2 b hb.1 hb.2⟩

/-- A tuple's positions against one element, lifted pointwise on the read side. -/
theorem admAList_lift {e : Term} {f : Term → Option Term} (hf : AdmASound e f) :
    ∀ {ts vs : List Term}, List.Forall₂ (fun t v => f t = some v) ts vs →
      List.Forall₂ (fun p q => ∀ b, q b = (p b && AdmA e b)) (AdmAList ts) (AdmAList vs) := by
  intro ts
  induction ts with
  | nil => intro vs hts; cases hts; exact .nil
  | cons t ts' ihx =>
      intro vs hts
      cases hts with
      | cons hh hrest =>
          exact .cons (fun b => by rw [(hf t _ hh).1 b, Bool.and_comm]) (ihx hrest)

/-- …and the tail. -/
theorem admAOptT_lift {e : Term} {f : Term → Option Term} (hf : AdmASound e f)
    {tail tl : Option Term}
    (htl : (tail = none ∧ tl = none) ∨
      ∃ t u, tail = some t ∧ tl = some u ∧ f t = some u) :
    (AdmAOptT tail = none ∧ AdmAOptT tl = none) ∨
      ∃ p q, AdmAOptT tail = some p ∧ AdmAOptT tl = some q ∧
        ∀ b, q b = (p b && AdmA e b) := by
  rcases htl with ⟨rfl, rfl⟩ | ⟨t, u, rfl, rfl, hu⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨AdmA t, AdmA u, rfl, rfl, fun b => by rw [(hf t u hu).1 b, Bool.and_comm]⟩

/-- …and what the met positions read, against both factors. -/
theorem denoteList_lift {e : Term} {f : Term → Option Term} (hf : AdmASound e f) :
    ∀ {ts vs : List Term}, List.Forall₂ (fun t v => f t = some v) ts vs →
      List.Forall₂ (fun v t => ∀ b, AdmA v b = true → (denote v).p b = (denote t).p b) vs ts
        ∧ (∀ v ∈ vs, ∀ b, AdmA v b = true → (denote v).p b = (denote e).p b) := by
  intro ts
  induction ts with
  | nil => intro vs hts; cases hts; exact ⟨.nil, by simp⟩
  | cons t ts' ihx =>
      intro vs hts
      cases hts with
      | cons hh hrest =>
          obtain ⟨hF, hE⟩ := ihx hrest
          refine ⟨.cons (fun b hb => (admA_split hf hh b hb).2.2.2) hF, ?_⟩
          intro v hv b hb
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact (admA_split hf hh b hb).2.2.1
          · exact hE v hv' b hb

/-- …and what the met tail reads. -/
theorem tailDenote_lift {e : Term} {f : Term → Option Term} (hf : AdmASound e f)
    {tail tl : Option Term}
    (htl : (tail = none ∧ tl = none) ∨
      ∃ t u, tail = some t ∧ tl = some u ∧ f t = some u) :
    ((tl = none ∧ tail = none) ∨
      ∃ u t, tl = some u ∧ tail = some t ∧
        ∀ b, AdmA u b = true → (denote u).p b = (denote t).p b)
    ∧ (∀ u ∈ tl, ∀ b, AdmA u b = true → (denote u).p b = (denote e).p b) := by
  rcases htl with ⟨rfl, rfl⟩ | ⟨t, u, rfl, rfl, hu⟩
  · exact ⟨Or.inl ⟨rfl, rfl⟩, by simp⟩
  · refine ⟨Or.inr ⟨u, t, rfl, rfl, fun b hb => (admA_split hf hu b hb).2.2.2⟩, ?_⟩
    intro w hw b hb
    rw [Option.mem_def, Option.some.injEq] at hw
    subst hw
    exact (admA_split hf hu b hb).2.2.1


/-- An array reads an array at the element, and a tuple at every declared position. -/
theorem admA_famArr {x' : Term} {f : Term → Option Term} (hf : AdmASound x' f) :
    AdmAFam (.array x') (famArr f) := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case array e =>
      simp only [famArr] at h
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨ih1, ih2⟩ := hf e w hw
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · cases a <;> simp only [AdmA, Bool.and_self, allPA_and ih1]
      · cases a
        case l as =>
          simp only [AdmA] at ha hb
          simp only [denote_array]
          exact ⟨arrayCodec_p_congr
                   (fun b hm => (ih2 b (allPA_mem ha b hm) (allPA_mem hb b hm)).1),
                 arrayCodec_p_congr
                   (fun b hm => (ih2 b (allPA_mem ha b hm) (allPA_mem hb b hm)).2)⟩
        all_goals (exfalso; revert ha; simp [AdmA])
  case tuple ts tail =>
      obtain ⟨vs, tl, rfl, hts, htl⟩ := famArr_tuple h
      have hFA := admAList_lift hf hts
      have hTA := admAOptT_lift hf htl
      obtain ⟨hP1, hP2⟩ := denoteList_lift hf hts
      obtain ⟨hT1, hT2⟩ := tailDenote_lift hf htl
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · rw [AdmA_tupleOf]
        cases a <;> simp only [AdmA, Bool.and_self, alignPA_meet_all hFA hTA]
      · cases a
        case l as =>
          simp only [AdmA] at ha hb
          have hz : alignPA (AdmAList vs) (AdmAOptT tl) as = true := by
            simp only [alignPA_meet_all hFA hTA, ha, hb, Bool.and_self]
          rw [tupleOf_eq_tuple hz]
          exact ⟨congrArg (Option.map Value.arr) (align_p_congr_array hz hP2 hT2),
                 congrArg (Option.map Value.arr) (align_p_congr hz hP1 hT1)⟩
        all_goals (exfalso; revert ha; simp [AdmA])
  case opaq l => simp [famArr] at h
  all_goals admA_never famArr

/-- A record reads a record at the value term. -/
theorem admA_famRecTerm {x' : Term} {f : Term → Option Term} (hf : AdmASound x' f)
    {c w : Term} (hw : f c = some w) : AdmAAt (.record x') (.record c) (.record w) := by
  obtain ⟨ih1, ih2⟩ := hf c w hw
  refine ⟨fun a => ?_, fun a ha hb => ?_⟩
  · cases a <;> simp only [AdmA, Bool.and_self, decide_forall_and (fun k => ih1 _)]
  · cases a
    case m keys g =>
      simp only [AdmA, decide_eq_true_eq] at ha hb
      simp only [denote_record]
      exact ⟨recordCodec_p_congr (fun k => (ih2 (g k) (ha k) (hb k)).1),
             recordCodec_p_congr (fun k => (ih2 (g k) (ha k) (hb k)).2)⟩
    all_goals (exfalso; revert ha; simp [AdmA])


/-- A field met with one term on the left, as the read side needs it. -/
theorem AdmAField_fieldMeetT {f : Term → Option Term} {fl fm : Field}
    (h : fieldMeetT f fl = some fm) :
    ∃ tx tz, f tx = some tz ∧ AdmAField fl = AdmA tx ∧ AdmAField fm = AdmA tz ∧
      (fieldSem fl).codec = denote tx ∧ (fieldSem fm).codec = denote tz := by
  cases fl <;> simp only [fieldMeetT, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨tz, hz, rfl⟩ := h <;> exact ⟨_, tz, hz, rfl, rfl, rfl, rfl⟩

/-- A field met with a term on the left keeps its own read-side mark. -/
theorem isReqA_fieldMeetT {f : Term → Option Term} {fl fm : Field}
    (h : fieldMeetT f fl = some fm) : Field.isReqA fm = Field.isReqA fl := by
  cases fl <;> simp only [fieldMeetT, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨tz, _, rfl⟩ := h <;> rfl

/-- …and never answers a `fallback`. -/
theorem fieldMeetT_not_fallback {f : Term → Option Term} {fl fm : Field}
    (h : fieldMeetT f fl = some fm) {t : Term} {d : Value} : fm ≠ .fallback t d := by
  cases fl <;> simp only [fieldMeetT, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨z, _, rfl⟩ := h <;> simp

/-- A record reads a record at the value term, and an object through every field. -/
theorem admA_famRec {x' : Term} {f : Term → Option Term} (hf : AdmASound x' f) :
    AdmAFam (.record x') (famRec f) := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case record c =>
      simp only [famRec] at h
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      exact admA_famRecTerm hf hw
  case object b =>
      simp only [famRec] at h
      obtain ⟨t, r, hrest, hmt, hok, hcase⟩ := recObj_extract h
      have hnfbSrc : ∀ (k : {k // k ∈ b.fields}) (u : Term) (d : Value),
          b.at k ≠ .fallback u d := by
        intro k u d hfd
        obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfd] at hfm; simp [fieldMeetT] at hfm
      have hreqA : ∀ k : {k // k ∈ b.fields},
          Field.isReqA ((fieldMeetT f (b.at k)).getD (.optional .never))
            = Field.isReqA (b.at k) := by
        intro k
        obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfm, Option.getD_some]; exact isReqA_fieldMeetT hfm
      have hnfb : ∀ (k : {k // k ∈ b.fields}) (u : Term) (d : Value),
          (fieldMeetT f (b.at k)).getD (.optional .never) ≠ .fallback u d := by
        intro k u d
        obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfm, Option.getD_some]; exact fieldMeetT_not_fallback hfm
      obtain ⟨ihtA, ihtP⟩ := hf t r hmt
      have ihf : ∀ (k : {k // k ∈ b.fields}),
          (∀ c, AdmAField ((fieldMeetT f (b.at k)).getD (.optional .never)) c
            = (AdmAField (b.at k) c && AdmA x' c))
          ∧ (∀ c, AdmAField (b.at k) c = true → AdmA x' c = true →
              (fieldSem ((fieldMeetT f (b.at k)).getD (.optional .never))).codec.p c
                  = (fieldSem (b.at k)).codec.p c
                ∧ (fieldSem ((fieldMeetT f (b.at k)).getD (.optional .never))).codec.p c
                  = (denote x').p c) := by
        intro k
        obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        obtain ⟨tx, tz, hz, hx, hfz, hcx, hcz⟩ := AdmAField_fieldMeetT hfm
        obtain ⟨hA1, hA2⟩ := hf tx tz hz
        rw [hfm, Option.getD_some, hfz, hx, hcz, hcx]
        exact ⟨fun c => by rw [hA1 c, Bool.and_comm], fun c hxa hxx => ⟨(hA2 c hxx hxa).2,
          (hA2 c hxx hxa).1⟩⟩
      have hgen := record_row_gen (x := x') (z := z) hrest hreqA hnfb hnfbSrc
        (fun c => by rw [ihtA c, Bool.and_comm])
        (fun c ht hx => ⟨(ihtP c hx ht).2, (ihtP c hx ht).1⟩) ihf hcase
      exact ⟨fun c => by rw [hgen.1 c, Bool.and_comm], fun c hx hb => (hgen.2 c hb hx).symm⟩
  case opaq l => simp [famRec] at h
  all_goals admA_never famRec


/-! ### The tuple lifts, zipped and measure-free. -/

/-- Two tuples' positions, zipped and lifted pointwise. -/
theorem admAList_zip_lift :
    ∀ {ts us : List Term} {fs : List (Term → Option Term)} {vs : List Term},
      List.Forall₂ AdmASound ts fs →
      List.Forall₂ (fun (p : (Term → Option Term) × Term) v => p.1 p.2 = some v) (fs.zip us) vs →
      List.Forall₂ (fun (pq : AP × AP) r => ∀ w, r w = (pq.1 w && pq.2 w))
        ((AdmAList ts).zip (AdmAList us)) (AdmAList vs) := by
  intro ts
  induction ts with
  | nil => intro us fs vs hfs hF; cases hfs; rw [List.zip_nil_left] at hF; cases hF; exact .nil
  | cons t ts' ihx =>
      intro us fs vs hfs hF
      cases hfs with
      | cons hf hfs' =>
          cases us with
          | nil => rw [List.zip_nil_right] at hF; cases hF; exact .nil
          | cons u us' =>
              cases hF with
              | cons hh ht => exact .cons (fun w => (hf u _ hh).1 w) (ihx hfs' ht)

/-- …and their tails. -/
theorem admAOptT_zip_lift {tail tail' tl : Option Term}
    {ftail : Option (Term → Option Term)}
    (hft : (tail = none ∧ ftail = none) ∨
      ∃ t ft, tail = some t ∧ ftail = some ft ∧ AdmASound t ft)
    (htl : (ftail = none ∧ tail' = none ∧ tl = none) ∨
      ∃ ft u w, ftail = some ft ∧ tail' = some u ∧ tl = some w ∧ ft u = some w) :
    (AdmAOptT tail = none ∧ AdmAOptT tail' = none ∧ AdmAOptT tl = none) ∨
      ∃ p q r, AdmAOptT tail = some p ∧ AdmAOptT tail' = some q ∧ AdmAOptT tl = some r ∧
        ∀ w, r w = (p w && q w) := by
  rcases hft with ⟨rfl, rfl⟩ | ⟨t, ft, rfl, rfl, hs⟩
  · rcases htl with ⟨_, rfl, rfl⟩ | ⟨ft, u, w, hfe, _, _, _⟩
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · exact absurd hfe (by simp)
  · rcases htl with ⟨hfe, _, _⟩ | ⟨ft', u, w, hfe, rfl, rfl, hw⟩
    · exact absurd hfe (by simp)
    · simp only [Option.some.injEq] at hfe; subst hfe
      exact Or.inr ⟨AdmA t, AdmA u, AdmA w, rfl, rfl, rfl, (hs u w hw).1⟩

/-- …and what the met positions read, against both tuples. -/
theorem denoteList_zip_lift :
    ∀ {ts us : List Term} {fs : List (Term → Option Term)} {vs : List Term},
      ts.length = us.length →
      List.Forall₂ AdmASound ts fs →
      List.Forall₂ (fun (p : (Term → Option Term) × Term) v => p.1 p.2 = some v) (fs.zip us) vs →
      List.Forall₂ (fun v t => ∀ b, AdmA v b = true → (denote v).p b = (denote t).p b) vs ts
        ∧ List.Forall₂ (fun v u => ∀ b, AdmA v b = true →
            (denote v).p b = (denote u).p b) vs us := by
  intro ts
  induction ts with
  | nil =>
      intro us fs vs hlen hfs hF
      cases us with
      | nil => cases hfs; rw [List.zip_nil_left] at hF; cases hF; exact ⟨.nil, .nil⟩
      | cons => exact absurd hlen (by simp only [List.length_nil, List.length_cons]; omega)
  | cons t ts' ihx =>
      intro us fs vs hlen hfs hF
      cases hfs with
      | cons hf hfs' =>
          cases us with
          | nil => exact absurd hlen (by simp only [List.length_nil, List.length_cons]; omega)
          | cons u us' =>
              cases hF with
              | cons hh ht =>
                  obtain ⟨hA, hB⟩ := ihx (by simp only [List.length_cons] at hlen; omega) hfs' ht
                  exact ⟨.cons (fun b hb => (admA_split hf hh b hb).2.2.1) hA,
                         .cons (fun b hb => (admA_split hf hh b hb).2.2.2) hB⟩

/-- …and what the met tails read. -/
theorem tailDenote_zip_lift {tail tail' tl : Option Term}
    {ftail : Option (Term → Option Term)}
    (hft : (tail = none ∧ ftail = none) ∨
      ∃ t ft, tail = some t ∧ ftail = some ft ∧ AdmASound t ft)
    (htl : (ftail = none ∧ tail' = none ∧ tl = none) ∨
      ∃ ft u w, ftail = some ft ∧ tail' = some u ∧ tl = some w ∧ ft u = some w) :
    ((tl = none ∧ tail = none) ∨ ∃ u t, tl = some u ∧ tail = some t ∧
        ∀ b, AdmA u b = true → (denote u).p b = (denote t).p b)
    ∧ ((tl = none ∧ tail' = none) ∨ ∃ u t, tl = some u ∧ tail' = some t ∧
        ∀ b, AdmA u b = true → (denote u).p b = (denote t).p b) := by
  rcases hft with ⟨rfl, rfl⟩ | ⟨t, ft, rfl, rfl, hs⟩
  · rcases htl with ⟨_, rfl, rfl⟩ | ⟨ft, u, w, hfe, _, _, _⟩
    · exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact absurd hfe (by simp)
  · rcases htl with ⟨hfe, _, _⟩ | ⟨ft', u, w, hfe, rfl, rfl, hw⟩
    · exact absurd hfe (by simp)
    · simp only [Option.some.injEq] at hfe; subst hfe
      exact ⟨Or.inr ⟨w, t, rfl, rfl, fun b hb => (admA_split hs hw b hb).2.2.1⟩,
             Or.inr ⟨w, u, rfl, rfl, fun b hb => (admA_split hs hw b hb).2.2.2⟩⟩


/-- A tuple's positions applied at one term, lifted pointwise. -/
theorem admAApplyAt_lift {e : Term} :
    ∀ {ts : List Term} {fs : List (Term → Option Term)} {vs : List Term},
      List.Forall₂ AdmASound ts fs →
      List.Forall₂ (fun f v => f e = some v) fs vs →
      List.Forall₂ (fun p q => ∀ w, q w = (p w && AdmA e w)) (AdmAList ts) (AdmAList vs) := by
  intro ts
  induction ts with
  | nil => intro fs vs hfs hv; cases hfs; cases hv; exact .nil
  | cons t ts' ihx =>
      intro fs vs hfs hv
      cases hfs with
      | cons hf hfs' =>
          cases hv with
          | cons hh ht => exact .cons (fun w => by rw [(hf e _ hh).1 w, Bool.and_comm]) (ihx hfs' ht)

/-- …and what they read. -/
theorem denoteApplyAt_lift {e : Term} :
    ∀ {ts : List Term} {fs : List (Term → Option Term)} {vs : List Term},
      List.Forall₂ AdmASound ts fs →
      List.Forall₂ (fun f v => f e = some v) fs vs →
      List.Forall₂ (fun v t => ∀ b, AdmA v b = true → (denote v).p b = (denote t).p b) vs ts
        ∧ (∀ v ∈ vs, ∀ b, AdmA v b = true → (denote v).p b = (denote e).p b) := by
  intro ts
  induction ts with
  | nil => intro fs vs hfs hv; cases hfs; cases hv; exact ⟨.nil, by simp⟩
  | cons t ts' ihx =>
      intro fs vs hfs hv
      cases hfs with
      | cons hf hfs' =>
          cases hv with
          | cons hh ht =>
              obtain ⟨hF, hE⟩ := ihx hfs' ht
              refine ⟨.cons (fun b hb => (admA_split hf hh b hb).2.2.1) hF, ?_⟩
              intro v hv' b hb
              rcases List.mem_cons.mp hv' with rfl | hv''
              · exact (admA_split hf hh b hb).2.2.2
              · exact hE v hv'' b hb

/-- A tuple reads an array at every position, and another tuple by arity. -/
theorem admA_famTup {ts : List Term} {tail : Option Term}
    {fs : List (Term → Option Term)} {ftail : Option (Term → Option Term)}
    (hfs : List.Forall₂ AdmASound ts fs)
    (hft : (tail = none ∧ ftail = none) ∨
      ∃ t ft, tail = some t ∧ ftail = some ft ∧ AdmASound t ft) :
    AdmAFam (.tuple ts tail) (famTup fs ftail) := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case array e =>
      simp only [famTup] at h
      split at h
      next vs tl hvs htl =>
        simp only [Option.some.injEq] at h; subst h
        have hF : List.Forall₂ (fun f w => f e = some w) fs vs :=
          allSome_map_forall₂ _ (by rw [← applyAt_eq]; exact hvs)
        have hT : ((AdmAOptT tail = none ∧ AdmAOptT tl = none) ∨
              ∃ p q, AdmAOptT tail = some p ∧ AdmAOptT tl = some q ∧
                ∀ b, q b = (p b && AdmA e b))
            ∧ (((tl = none ∧ tail = none) ∨ ∃ u t, tl = some u ∧ tail = some t ∧
                  ∀ b, AdmA u b = true → (denote u).p b = (denote t).p b)
               ∧ (∀ u ∈ tl, ∀ b, AdmA u b = true → (denote u).p b = (denote e).p b)) := by
          rcases hft with ⟨rfl, rfl⟩ | ⟨t, ft, rfl, rfl, hs⟩
          · replace htl : some (none : Option Term) = some tl := htl
            simp only [Option.some.injEq] at htl; subst htl
            exact ⟨.inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩, by simp⟩
          · replace htl : Option.map some (ft e) = some tl := htl
            obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp htl
            refine ⟨.inr ⟨AdmA t, AdmA u, rfl, rfl, fun b => by
                      rw [(hs e u hu).1 b, Bool.and_comm]⟩,
                    .inr ⟨u, t, rfl, rfl, fun b hb => (admA_split hs hu b hb).2.2.1⟩, ?_⟩
            intro w hw b hb
            rw [Option.mem_def, Option.some.injEq] at hw; subst hw
            exact (admA_split hs hu b hb).2.2.2
        obtain ⟨hTA, hTD⟩ := hT
        obtain ⟨hP1, hP2⟩ := denoteApplyAt_lift hfs hF
        refine ⟨fun a => ?_, fun a ha hb => ?_⟩
        · rw [AdmA_tupleOf]
          cases a <;> simp only [AdmA, Bool.and_self] <;>
            rw [Bool.and_comm, alignPA_meet_all (admAApplyAt_lift hfs hF) hTA]
        · cases a
          case l as =>
            simp only [AdmA] at ha hb
            have hz : alignPA (AdmAList vs) (AdmAOptT tl) as = true := by
              simp only [alignPA_meet_all (admAApplyAt_lift hfs hF) hTA, ha, hb, Bool.and_self]
            rw [tupleOf_eq_tuple hz]
            exact ⟨congrArg (Option.map Value.arr) (align_p_congr hz hP1 hTD.1),
                   congrArg (Option.map Value.arr) (align_p_congr_array hz hP2 hTD.2)⟩
          all_goals (exfalso; revert hb; simp [AdmA])
      next => exact absurd h (by simp)
  case tuple us tail' =>
      simp only [famTup] at h
      split at h
      next hlen =>
        split at h
        next vs tl hvs htl =>
          simp only [Option.some.injEq] at h; subst h
          have hF : List.Forall₂
              (fun (p : (Term → Option Term) × Term) w => p.1 p.2 = some w) (fs.zip us) vs :=
            allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hvs)
          have hTraw : (ftail = none ∧ tail' = none ∧ tl = none) ∨
              ∃ ft u w, ftail = some ft ∧ tail' = some u ∧ tl = some w ∧ ft u = some w := by
            cases hfe : ftail with
            | none =>
                cases tail' with
                | none =>
                    rw [hfe] at htl
                    replace htl : some (none : Option Term) = some tl := htl
                    simp only [Option.some.injEq] at htl; subst htl
                    exact .inl ⟨rfl, rfl, rfl⟩
                | some u => rw [hfe] at htl; exact absurd htl (by simp)
            | some ft =>
                cases tail' with
                | none => rw [hfe] at htl; exact absurd htl (by simp)
                | some u =>
                    rw [hfe] at htl
                    replace htl : Option.map some (ft u) = some tl := htl
                    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp htl
                    exact .inr ⟨ft, u, w, rfl, rfl, rfl, hw⟩
          have hlenT : ts.length = us.length := hfs.length_eq.trans hlen
          have hFA := admAList_zip_lift hfs hF
          have hTA := admAOptT_zip_lift hft hTraw
          obtain ⟨hP1, hP2⟩ := denoteList_zip_lift hlenT hfs hF
          obtain ⟨hT1, hT2⟩ := tailDenote_zip_lift hft hTraw
          refine ⟨fun a => ?_, fun a ha hb => ?_⟩
          · rw [AdmA_tupleOf]
            cases a <;> simp only [AdmA, Bool.and_self,
              alignPA_meet_zip hFA
                (by rw [AdmAList_length, AdmAList_length]; exact hlenT) hTA]
          · cases a
            case l as =>
              simp only [AdmA] at ha hb
              have hz : alignPA (AdmAList vs) (AdmAOptT tl) as = true := by
                simp only [alignPA_meet_zip hFA
                  (by rw [AdmAList_length, AdmAList_length]; exact hlenT) hTA, ha, hb,
                  Bool.and_self]
              rw [tupleOf_eq_tuple hz]
              exact ⟨congrArg (Option.map Value.arr) (align_p_congr hz hP1 hT1),
                     congrArg (Option.map Value.arr) (align_p_congr hz hP2 hT2)⟩
            all_goals (exfalso; revert ha; simp [AdmA])
        next => exact absurd h (by simp)
      next hlen =>
        split at h
        next hb2 =>
          simp only [Option.some.injEq] at h; subst h
          simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hb2
          obtain ⟨hb1, hb2'⟩ := hb2
          have htn : tail = none := by
            rcases hft with ⟨rfl, _⟩ | ⟨t, ft, rfl, rfl, _⟩
            · rfl
            · exact absurd hb1 (by simp)
          subst htn; subst hb2'
          have hne : ts.length ≠ us.length := fun hc => hlen (hfs.length_eq.symm.trans hc)
          refine bottom_row (fun a => ?_)
          cases a
          case l ws =>
            simp only [AdmA, AdmAOptT]
            cases hA : alignPA (AdmAList ts) none ws with
            | false => simp
            | true =>
              cases hB : alignPA (AdmAList us) none ws with
              | false => simp
              | true =>
                exact absurd
                  (((alignPA_none_length hA).trans (AdmAList_length _)).symm.trans
                    ((alignPA_none_length hB).trans (AdmAList_length _))) hne
          all_goals simp [AdmA]
        next => exact absurd h (by simp)
  case opaq l => simp [famTup] at h
  all_goals admA_never famTup


/-- The four structural guards `objObj` passes before it answers. -/
theorem objObj_guards {a b : Body} {g : {k // k ∈ a.fields} → Field → Option Field} {z : Term}
    (h : objObj a g b = some z) :
    Body.fbShared a b = true ∧ Body.fbShared b a = true ∧
      Body.dropFits a b = true ∧ Body.dropFits b a = true := by
  unfold objObj at h
  split at h
  next =>
    split at h
    next hfb =>
      split at h
      next hd =>
        rw [Bool.and_eq_true] at hfb hd
        exact ⟨hfb.1, hfb.2, hd.1, hd.2⟩
      next => exact absurd h (by simp)
    next => exact absurd h (by simp)
  next => exact absurd h (by simp)

/-- An object reads an object over the shared names, and a record through every field. -/
theorem admA_famObj {a : Body} {g : {k // k ∈ a.fields} → Field → Option Field}
    {gt : {k // k ∈ a.fields} → Term → Option Field}
    {frest : Option (Term → Option Term)}
    (hg : ∀ (k : {k // k ∈ a.fields}) (fl fm : Field), g k fl = some fm →
      (∀ c, AdmAField fm c = (AdmAField (a.at k) c && AdmAField fl c))
      ∧ (∀ c, AdmAField (a.at k) c = true → AdmAField fl c = true →
          (fieldSem fm).codec.p c = (fieldSem (a.at k)).codec.p c
            ∧ (fieldSem fm).codec.p c = (fieldSem fl).codec.p c))
    (hgreq : ∀ (k : {k // k ∈ a.fields}) (fl fm : Field), g k fl = some fm →
      Field.isReqA fm = (Field.isReqA (a.at k) || Field.isReqA fl))
    (hgbot : ∀ (k : {k // k ∈ a.fields}) (fl fm : Field), g k fl = some fm →
      Field.isBottom fm = true → ∃ t, fm = .req t)
    (hgfb : ∀ (k : {k // k ∈ a.fields}) (fl fm : Field), g k fl = some fm →
      ∀ (u : Term) (d : Value), fm ≠ .fallback u d)
    (hgpair : ∀ (k : {k // k ∈ a.fields}) (fl fm : Field), g k fl = some fm →
      (∃ u d, a.at k = .fallback u d) → ∃ v, fl = .req v)
    (hgpair' : ∀ (k : {k // k ∈ a.fields}) (fl fm : Field), g k fl = some fm →
      (∃ u d, fl = .fallback u d) → ∃ v, a.at k = .req v)
    (hgt : ∀ (k : {k // k ∈ a.fields}) (y : Term) (fm : Field), gt k y = some fm →
      (∀ c, AdmAField fm c = (AdmAField (a.at k) c && AdmA y c))
      ∧ (∀ c, AdmAField (a.at k) c = true → AdmA y c = true →
          (fieldSem fm).codec.p c = (fieldSem (a.at k)).codec.p c
            ∧ (fieldSem fm).codec.p c = (denote y).p c))
    (hgtreq : ∀ (k : {k // k ∈ a.fields}) (y : Term) (fm : Field), gt k y = some fm →
      Field.isReqA fm = Field.isReqA (a.at k))
    (hgtfb : ∀ (k : {k // k ∈ a.fields}) (y : Term) (fm : Field), gt k y = some fm →
      ∀ (u : Term) (d : Value), fm ≠ .fallback u d)
    (hgtsrc : ∀ (k : {k // k ∈ a.fields}) (y : Term) (fm : Field), gt k y = some fm →
      ∀ (u : Term) (d : Value), a.at k ≠ .fallback u d)
    (hfr : ∀ fr, frest = some fr → ∃ t, a.rest = .codec t ∧ AdmASound t fr) :
    AdmAFam (.object a) (famObj a g gt frest) := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case object b =>
      simp only [famObj] at h
      obtain ⟨hfba, hfbb, hda, hdb⟩ := objObj_guards h
      obtain ⟨r, hr, hcase⟩ := objObj_extract h
      refine object_row_gen (Ok := ∀ k : {k // k ∈ Body.shared a b},
          (g ⟨k.1, Body.mem_shared_left k.2⟩
            (b.at ⟨k.1, Body.mem_shared_right k.2⟩)).isSome = true)
        hr hfba hfbb hda hdb (fun hok k => ?_) (fun hok k hbot => ?_) (fun hok keys => ?_)
        (fun hok => fbNames_factor_of_req (fun k hk hkb hfd => by
            have hks : k ∈ Body.shared a b := Finset.mem_filter.mpr ⟨hk, hkb⟩
            obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok ⟨k, hks⟩)
            exact hgpair ⟨k, hk⟩ _ _ hfm hfd) hfba)
        (fun hok => fbNames_factor_of_req' (fun k hk hka hfd => by
            have hks : k ∈ Body.shared a b := Finset.mem_filter.mpr ⟨hka, by simpa using hk⟩
            obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok ⟨k, hks⟩)
            exact hgpair' ⟨k, hka⟩ _ _ hfm hfd) hfbb)
        (fun hok k => ?_) hcase
      · obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfm, Option.getD_some]; exact hgreq _ _ _ hfm
      · obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfm, Option.getD_some] at hbot ⊢; exact hgbot _ _ _ hfm hbot
      · refine fbNames_empty_of_not_fallback (fun k u d => ?_) keys
        obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfm, Option.getD_some]; exact hgfb _ _ _ hfm u d
      · obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfm, Option.getD_some]; exact hg _ _ _ hfm
  case record x =>
      simp only [famObj] at h
      obtain ⟨fr, r, hfrest, hrx, hok, hcase⟩ := objRec_extract h
      obtain ⟨t, hrest, hsound⟩ := hfr fr hfrest
      obtain ⟨ihtA, ihtP⟩ := hsound x r hrx
      have hsrc : ∀ (k : {k // k ∈ a.fields}) (u : Term) (d : Value), a.at k ≠ .fallback u d := by
        intro k u d
        obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        exact hgtsrc k x fm hfm u d
      refine record_row_gen (x := x) (z := z) hrest (fun k => ?_) (fun k u d => ?_) hsrc
        ihtA ihtP (fun k => ?_) hcase
      · obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfm, Option.getD_some]; exact hgtreq _ _ _ hfm
      · obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfm, Option.getD_some]; exact hgtfb _ _ _ hfm u d
      · obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfm, Option.getD_some]; exact hgt _ _ _ hfm
  case opaq l => simp [famObj] at h
  all_goals admA_never famObj


/-! ### The outer theorem. -/

/-- Two fields meet at the stronger mark, so the read bit is the join. -/
theorem isReqA_Field_meet : ∀ {f fl fm : Field}, Field.meet f fl = some fm →
    Field.isReqA fm = (Field.isReqA f || Field.isReqA fl) := by
  intro f fl fm h
  cases f <;> cases fl <;>
    simp only [Field.meet, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨tz, _, rfl⟩ := h <;> rfl

/-- Only a `req` field can meet to the bottom, which is what `isBottom` asks. -/
theorem reqOf_Field_meet : ∀ {f fl fm : Field}, Field.meet f fl = some fm →
    Field.isBottom fm = true → ∃ t, fm = .req t := by
  intro f fl fm h hbot
  cases f <;> cases fl <;>
    simp only [Field.meet, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨tz, _, rfl⟩ := h <;>
    first
      | exact ⟨tz, rfl⟩
      | exact absurd hbot (by simp [Field.isBottom])

/-- No row of `Field.meet` answers a `fallback`. -/
theorem notFallback_Field_meet : ∀ {f fl fm : Field}, Field.meet f fl = some fm →
    ∀ (u : Term) (d : Value), fm ≠ .fallback u d := by
  intro f fl fm h u d
  cases f <;> cases fl <;>
    simp only [Field.meet, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨tz, _, rfl⟩ := h <;> simp

/-- A `fallback` on the left meets only a `req` on the right. -/
theorem pair_Field_meet : ∀ {f fl fm : Field}, Field.meet f fl = some fm →
    (∃ u d, f = .fallback u d) → ∃ v, fl = .req v := by
  intro f fl fm h hfd
  obtain ⟨u, d, rfl⟩ := hfd
  cases fl <;> simp only [Field.meet, Option.map_eq_some_iff, reduceCtorEq] at h
  exact ⟨_, rfl⟩

/-- …and the mirror. -/
theorem pair_Field_meet' : ∀ {f fl fm : Field}, Field.meet f fl = some fm →
    (∃ u d, fl = .fallback u d) → ∃ v, f = .req v := by
  intro f fl fm h hfd
  obtain ⟨u, d, rfl⟩ := hfd
  cases f <;> simp only [Field.meet, Option.map_eq_some_iff, reduceCtorEq] at h
  exact ⟨_, rfl⟩

/-- A field met with a record's term keeps its own read-side mark. -/
theorem isReqA_Field_meetT : ∀ {f : Field} {y : Term} {fm : Field}, Field.meetT f y = some fm →
    Field.isReqA fm = Field.isReqA f := by
  intro f y fm h
  cases f <;> simp only [Field.meetT, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨tz, _, rfl⟩ := h <;> rfl

/-- …and never answers a `fallback`. -/
theorem notFallback_Field_meetT : ∀ {f : Field} {y : Term} {fm : Field},
    Field.meetT f y = some fm → ∀ (u : Term) (d : Value), fm ≠ .fallback u d := by
  intro f y fm h u d
  cases f <;> simp only [Field.meetT, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨tz, _, rfl⟩ := h <;> simp

/-- …and refuses a `fallback` source outright. -/
theorem src_Field_meetT : ∀ {f : Field} {y : Term} {fm : Field}, Field.meetT f y = some fm →
    ∀ (u : Term) (d : Value), f ≠ .fallback u d := by
  intro f y fm h u d
  cases f <;> simp only [Field.meetT, Option.map_eq_some_iff, reduceCtorEq] at h <;> simp

mutual
/-- **The read side's homomorphism and its reading agreement, together.** Both halves are
    proved at once because a refinement row needs the agreement against whichever factor the
    wrapper sits on. -/
theorem AdmA_meet_both : ∀ x y z, Term.meet x y = some z → AdmAAt x y z
  | .never, _, _, h => by
      simp only [Term.meet, Option.some.injEq] at h; subst h
      exact ⟨fun a => rfl, fun a ha _ => absurd ha (by simp [AdmA])⟩
  | .held _ _ _, y, _, h => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h
             exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩)
          | exact absurd h (by simp [Term.meet])
  | .legacy _ _, y, _, h => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h
             exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩)
          | exact absurd h (by simp [Term.meet])
  | .custom _ _, y, _, h => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h
             exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩)
          | exact absurd h (by simp [Term.meet])
  | .lazy _, y, _, h => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h
             exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩)
          | exact absurd h (by simp [Term.meet])
  | .refine x p, y, _, h => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h
          exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩
      | _ =>
        simp only [Term.meet] at h
        split at h
        · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨ih1, ih2⟩ := AdmA_meet_both x _ w hw
          exact refine_row_l ih1 ih2
        · exact absurd h (by simp)
  | .union os, y, _, h => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h
          exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩
      | _ =>
        obtain ⟨zs, hF, hco, hcz, rfl⟩ := meet_union_of h (by simp)
        have hB := admA_meetL os _ zs hF
        refine ⟨fun a => ?_, fun a ha hb => ?_⟩
        · rw [AdmA_ofOptions hcz, AdmAAny_filter_never,
            AdmA_union _ a, selOptA_eq_AdmAAny hco]
          exact AdmAAny_meet a (List.Forall₂.imp (fun _ _ hh => hh.1) hB)
        · obtain ⟨t, hft, hta⟩ :=
            filter_eq_singleton_of_selOptA (show selOptA (AdmASpecs _) a = true from ha)
          obtain ⟨w, hwmem, hwA, hwP⟩ := forall₂_mem_left hB (mem_of_filter_eq_singleton hft).1
          have hwa : AdmA w a = true := by rw [hwA a, hta, hb]; rfl
          have hsurv : w ∈ zs.filter (fun z => !z.isNever) :=
            List.mem_filter.mpr ⟨hwmem, by rw [not_isNever_of_admA hwa]; rfl⟩
          obtain ⟨u, hfu, _⟩ := filter_eq_singleton_of_selOptA
            (show selOptA (AdmASpecs (zs.filter (fun z => !z.isNever))) a = true by
              rw [selOptA_eq_AdmAAny hcz]; exact AdmAAny_of_mem hsurv hwa)
          have hwu : w = u := by
            have hm : w ∈ (zs.filter (fun z => !z.isNever)).filter
                (fun v => admitOptA (specOf v, AdmA v) a) :=
              List.mem_filter.mpr ⟨hsurv, admitOptA_of_AdmA hcz hsurv hwa⟩
            rw [hfu, List.mem_singleton] at hm
            exact hm
          subst hwu
          rw [ofOptions_p_of_filter hfu, union_p_of_filter hft]
          exact hwP a hta hb
  | .string, y, z, h => admA_meetSRight admA_famString y z h
  | .number, y, z, h => admA_meetSRight admA_famNumber y z h
  | .decimal, y, z, h => admA_meetSRight admA_famDecimal y z h
  | .boolean, y, z, h => admA_meetSRight admA_famBoolean y z h
  | .binary, y, z, h => admA_meetSRight admA_famBinary y z h
  | .null, y, z, h => admA_meetSRight admA_famNull y z h
  | .literal k lv, y, z, h => admA_meetSRight (admA_famLit k lv) y z h
  | .set b, y, z, h => admA_meetSRight (admA_famSet b) y z h
  | .opaq l, y, z, h => admA_meetSRight (admA_famOpaq l) y z h
  | .array e, y, z, h => admA_meetSRight (admA_famArr (fun u w hw => AdmA_meet_both e u w hw)) y z h
  | .record c, y, z, h => admA_meetSRight (admA_famRec (fun u w hw => AdmA_meet_both c u w hw)) y z h
  | .tuple ts tl, y, z, h => by
      cases tl with
      | none =>
          exact admA_meetSRight (admA_famTup (ts := ts) (tail := none)
            (fs := Term.meetSTs ts) (ftail := none) (admA_meetSTs ts) (Or.inl ⟨rfl, rfl⟩)) y z h
      | some t =>
          exact admA_meetSRight (admA_famTup (ts := ts) (tail := some t)
            (fs := Term.meetSTs ts) (ftail := some (Term.meet t)) (admA_meetSTs ts)
            (Or.inr ⟨t, Term.meet t, rfl, rfl, fun u w hw => AdmA_meet_both t u w hw⟩)) y z h
  | .object (.mk fs f r), y, z, h => by
      cases r with
      | codec t =>
          exact admA_meetSRight (admA_famObj (a := .mk fs f (.codec t))
            (fun k fl fm hm => admA_Field_meet (f k) fl fm hm)
            (fun _ _ _ hm => isReqA_Field_meet hm) (fun _ _ _ hm => reqOf_Field_meet hm)
            (fun _ _ _ hm => notFallback_Field_meet hm) (fun _ _ _ hm => pair_Field_meet hm)
            (fun _ _ _ hm => pair_Field_meet' hm)
            (fun k u fm hm => admA_Field_meetT (f k) u fm hm)
            (fun _ _ _ hm => isReqA_Field_meetT hm) (fun _ _ _ hm => notFallback_Field_meetT hm)
            (fun _ _ _ hm => src_Field_meetT hm)
            (fun fr hfr => ⟨t, rfl, by
              simp only [Option.some.injEq] at hfr; subst hfr
              exact fun u w hw => AdmA_meet_both t u w hw⟩)) y z h
      | drop =>
          exact admA_meetSRight (admA_famObj (a := .mk fs f .drop)
            (fun k fl fm hm => admA_Field_meet (f k) fl fm hm)
            (fun _ _ _ hm => isReqA_Field_meet hm) (fun _ _ _ hm => reqOf_Field_meet hm)
            (fun _ _ _ hm => notFallback_Field_meet hm) (fun _ _ _ hm => pair_Field_meet hm)
            (fun _ _ _ hm => pair_Field_meet' hm)
            (fun k u fm hm => admA_Field_meetT (f k) u fm hm)
            (fun _ _ _ hm => isReqA_Field_meetT hm) (fun _ _ _ hm => notFallback_Field_meetT hm)
            (fun _ _ _ hm => src_Field_meetT hm)
            (fun _ hfr => absurd hfr (by simp))) y z h
      | refuse =>
          exact admA_meetSRight (admA_famObj (a := .mk fs f .refuse)
            (fun k fl fm hm => admA_Field_meet (f k) fl fm hm)
            (fun _ _ _ hm => isReqA_Field_meet hm) (fun _ _ _ hm => reqOf_Field_meet hm)
            (fun _ _ _ hm => notFallback_Field_meet hm) (fun _ _ _ hm => pair_Field_meet hm)
            (fun _ _ _ hm => pair_Field_meet' hm)
            (fun k u fm hm => admA_Field_meetT (f k) u fm hm)
            (fun _ _ _ hm => isReqA_Field_meetT hm) (fun _ _ _ hm => notFallback_Field_meetT hm)
            (fun _ _ _ hm => src_Field_meetT hm)
            (fun _ hfr => absurd hfr (by simp))) y z h
termination_by structural x => x

/-- The union row's options, lifted pointwise at the fixed partner. -/
theorem admA_meetL : ∀ (os : List Term) (y : Term) (zs : List Term),
    List.Forall₂ (fun t w => Term.meet t y = some w) os zs →
    List.Forall₂ (fun t w =>
      (∀ b, AdmA w b = (AdmA t b && AdmA y b)) ∧
      (∀ b, AdmA t b = true → AdmA y b = true →
        (denote w).p b = (denote t).p b ∧ (denote w).p b = (denote y).p b)) os zs
  | [], _, _, h => by cases h; exact .nil
  | t :: ts, y, _, h => by
      cases h with
      | cons hh ht => exact .cons (AdmA_meet_both t y _ hh) (admA_meetL ts y _ ht)
termination_by structural os => os

/-- Every position of a tuple carries the meet at that position. -/
theorem admA_meetSTs : ∀ ts : List Term, List.Forall₂ AdmASound ts (Term.meetSTs ts)
  | [] => .nil
  | t :: ts => .cons (fun u w hw => AdmA_meet_both t u w hw) (admA_meetSTs ts)
termination_by structural ts => ts

/-- Two fields at one name read what both read, and read it to the same value. -/
theorem admA_Field_meet : ∀ (f fl : Field) (fm : Field), Field.meet f fl = some fm →
    (∀ c, AdmAField fm c = (AdmAField f c && AdmAField fl c))
    ∧ (∀ c, AdmAField f c = true → AdmAField fl c = true →
        (fieldSem fm).codec.p c = (fieldSem f).codec.p c
          ∧ (fieldSem fm).codec.p c = (fieldSem fl).codec.p c)
  | .req x, .req y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
  | .req x, .optional y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
  | .optional x, .req y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
  | .req x, .fallback y _, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
  | .fallback x _, .req y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
  | .optional x, .optional y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
  | .optional _, .fallback _ _, _, h => by simp [Field.meet] at h
  | .fallback _ _, .optional _, _, h => by simp [Field.meet] at h
  | .fallback _ _, .fallback _ _, _, h => by simp [Field.meet] at h
termination_by structural f => f

/-- …and a field met with a record's term does the same. -/
theorem admA_Field_meetT : ∀ (f : Field) (y : Term) (fm : Field), Field.meetT f y = some fm →
    (∀ c, AdmAField fm c = (AdmAField f c && AdmA y c))
    ∧ (∀ c, AdmAField f c = true → AdmA y c = true →
        (fieldSem fm).codec.p c = (fieldSem f).codec.p c
          ∧ (fieldSem fm).codec.p c = (denote y).p c)
  | .req x, y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
  | .optional x, y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
  | .fallback _ _, _, _, h => by simp [Field.meetT] at h
termination_by structural f => f
end


/-- **`AdmA` is a homomorphism from the meet to conjunction.** Where two terms have a meet, the
    attributes it reads are exactly the attributes both read. -/
theorem AdmA_meet {x y z : Term} (h : Term.meet x y = some z) (a : Attr) :
    AdmA z a = (AdmA x a && AdmA y a) :=
  (AdmA_meet_both x y z h).1 a

/-- **…and it reads them to the same value.** The read agreement is proved with the homomorphism
    and not after it: `AdmA (.refine t p) a` asks the predicate of what `t` decodes `a` to. -/
theorem denote_meet_p {x y z : Term} (h : Term.meet x y = some z) {a : Attr}
    (hx : AdmA x a = true) (hy : AdmA y a = true) :
    (denote z).p a = (denote x).p a ∧ (denote z).p a = (denote y).p a :=
  (AdmA_meet_both x y z h).2 a hx hy

end StructuralAdmA


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
  rw [Adm_meet _ _ _ h, Adm_meet _ _ _ h', Bool.and_comm]

/-- **…and associative on admission**, both bracketings answering. -/
theorem Adm_meet_assoc {x y z xy yz l r : Term}
    (hxy : Term.meet x y = some xy) (hl : Term.meet xy z = some l)
    (hyz : Term.meet y z = some yz) (hr : Term.meet x yz = some r) (v : Value) :
    Adm l v = Adm r v := by
  rw [Adm_meet _ _ _ hl, Adm_meet _ _ _ hxy, Adm_meet _ _ _ hr, Adm_meet _ _ _ hyz, Bool.and_assoc]

/-- **…and idempotent.** -/
theorem Adm_meet_self {x z : Term} (h : Term.meet x x = some z) (v : Value) :
    Adm z v = Adm x v := by
  rw [Adm_meet _ _ _ h, Bool.and_self]

/-- **The bottom absorbs.** -/
theorem Adm_meet_never {x z : Term} (h : Term.meet x .never = some z) (v : Value) :
    Adm z v = false := by
  rw [Adm_meet _ _ _ h, Adm_never, Bool.and_false]

/-- **The meet distributes over a certified union.** `AdmAny` is the join of the options'
    admissions, and `&&` distributes over `||`, so this is the distributive law with the join
    written the way the certificate makes it available. -/
theorem Adm_meet_union {x z : Term} {os : List Term} (hok : unionOk os = true)
    (h : Term.meet x (.union os) = some z) (v : Value) :
    Adm z v = (Adm x v && AdmAny os v) := by
  rw [Adm_meet _ _ _ h, show Adm (.union os) v = selOptV (AdmSpecs os) v from rfl,
    selOptV_eq_AdmAny hok]

/-- …and the distribution, written so a reader sees it: the meet of a term with a join is the
    join of the meets, one option at a time. -/
theorem Adm_meet_union_distrib {x z o : Term} {os : List Term} (hok : unionOk (o :: os) = true)
    (h : Term.meet x (.union (o :: os)) = some z) (v : Value) :
    Adm z v = ((Adm x v && Adm o v) || (Adm x v && AdmAny os v)) := by
  rw [Adm_meet_union hok h, AdmAny_cons]
  cases Adm x v <;> cases Adm o v <;> cases AdmAny os v <;> rfl

/-! ## The laws, on reading

`AdmA_meet` is the homomorphism from the meet to conjunction on the read side, so each law
below is the corresponding law of `Bool` read through it, exactly as the admission laws are.
Each is stated on both sides ANSWERING, for the same reason: whether the meet answers in one
order when it answers in the other is a question about the rows, and the lattice does not need
it.
-/

/-- **The meet is commutative on reading.** -/
theorem AdmA_meet_comm {x y z z' : Term} (h : Term.meet x y = some z)
    (h' : Term.meet y x = some z') (a : Attr) : AdmA z a = AdmA z' a := by
  rw [AdmA_meet h, AdmA_meet h', Bool.and_comm]

/-- **…and associative on reading**, both bracketings answering. -/
theorem AdmA_meet_assoc {x y z xy yz l r : Term}
    (hxy : Term.meet x y = some xy) (hl : Term.meet xy z = some l)
    (hyz : Term.meet y z = some yz) (hr : Term.meet x yz = some r) (a : Attr) :
    AdmA l a = AdmA r a := by
  rw [AdmA_meet hl, AdmA_meet hxy, AdmA_meet hr, AdmA_meet hyz, Bool.and_assoc]

/-- **…and idempotent.** -/
theorem AdmA_meet_self {x z : Term} (h : Term.meet x x = some z) (a : Attr) :
    AdmA z a = AdmA x a := by
  rw [AdmA_meet h, Bool.and_self]

/-- **The bottom absorbs**, and it reads nothing. -/
theorem AdmA_meet_never {x z : Term} (h : Term.meet x .never = some z) (a : Attr) :
    AdmA z a = false := by
  rw [AdmA_meet h, AdmA_never, Bool.and_false]

/-- **The meet distributes over a certified union.** `AdmAAny` is the join of the options'
    readings, and `&&` distributes over `||`, so this is the distributive law with the join
    written the way the certificate makes it available. -/
theorem AdmA_meet_union {x z : Term} {os : List Term} (hok : unionOk os = true)
    (h : Term.meet x (.union os) = some z) (a : Attr) :
    AdmA z a = (AdmA x a && AdmAAny os a) := by
  rw [AdmA_meet h, AdmA_union os a, selOptA_eq_AdmAAny hok]

/-- …and the distribution, written so a reader sees it: the meet of a term with a join is the
    join of the meets, one option at a time. -/
theorem AdmA_meet_union_distrib {x z o : Term} {os : List Term} (hok : unionOk (o :: os) = true)
    (h : Term.meet x (.union (o :: os)) = some z) (a : Attr) :
    AdmA z a = ((AdmA x a && AdmA o a) || (AdmA x a && AdmAAny os a)) := by
  rw [AdmA_meet_union hok h, AdmAAny_cons]
  cases AdmA x a <;> cases AdmA o a <;> cases AdmAAny os a <;> rfl

/-! ## The typed fragment is closed under the meet

`Typed.union` carries §5's (D), and the meet builds unions, so the rows that distribute a union
owe it. `dincomp_of_unionOk` reads (D) off the certificate the same rows already test, which is
why this theorem needs nothing from the denotation at a union.

The object rows are the ones that would need a choice of index. They do not make one:
`typed_canon` restates a derivation at indices that are functions of the term, so the merged
field table is written down. -/

/-- Option judgements for a list, where each option has one. -/
theorem typedListμ_of_all : ∀ {ss : List Term}, (∀ t ∈ ss, ∃ T μ, Typed t T μ) →
    ∃ Ts μs, TypedListμ ss Ts μs
  | [], _ => ⟨[], [], .nil⟩
  | t :: ts, h => by
    obtain ⟨T, μ, hty⟩ := h t List.mem_cons_self
    obtain ⟨Ts, μs, hs⟩ := typedListμ_of_all (fun u hu => h u (List.mem_cons_of_mem _ hu))
    exact ⟨T :: Ts, μ :: μs, .cons hty hs⟩

/-- **A certified list of derivable survivors gives a derivable union.** -/
theorem typed_ofOptions {ss : List Term} (hok : unionOk ss = true)
    (h : ∀ t ∈ ss, ∃ T μ, Typed t T μ) : ∃ T μ, Typed (Term.ofOptions ss) T μ := by
  rcases ss with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact ⟨_, _, Typed.never⟩
  · exact h a List.mem_cons_self
  · obtain ⟨Ts, μs, hL⟩ := typedListμ_of_all h
    exact ⟨_, _, Typed.union hL (dincomp_of_unionOk hok hL)⟩


/-- Each option of a derivable union is derivable. -/
theorem typedListμ_mem : ∀ {os : List Term} {Ts μs}, TypedListμ os Ts μs →
    ∀ t ∈ os, ∃ T μ, Typed t T μ
  | _, _, _, .nil, _, ht => nomatch ht
  | _, _, _, .cons hty hs, t, ht => by
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact ⟨_, _, hty⟩
    · exact typedListμ_mem hs t ht'

/-- …read off the judgement of the union itself. -/
theorem typed_union_inv {os : List Term} :
    (∃ T μ, Typed (.union os) T μ) → ∀ t ∈ os, ∃ T μ, Typed t T μ
  | ⟨_, _, h⟩ => by cases h with | union hL _ => exact typedListμ_mem hL

/-- Inversions: a derivable container gives derivable components. -/
theorem typed_array_inv {a : Term} : (∃ T μ, Typed (.array a) T μ) → ∃ T μ, Typed a T μ
  | ⟨_, _, h⟩ => by cases h with | array h' => exact ⟨_, _, h'⟩

/-- …and a record's value term. -/
theorem typed_record_inv {a : Term} : (∃ T μ, Typed (.record a) T μ) → ∃ T μ, Typed a T μ
  | ⟨_, _, h⟩ => by cases h with | record h' => exact ⟨_, _, h'⟩

/-- …and the term under a refinement. -/
theorem typed_refine_inv {a : Term} {p : Pred} :
    (∃ T μ, Typed (.refine a p) T μ) → ∃ T μ, Typed a T μ
  | ⟨_, _, h⟩ => by cases h with | refine h' => exact ⟨_, _, h'⟩

/-- Normalising a refinement keeps it derivable: the bottom is derivable too. -/
theorem typed_refineOf {t : Term} {p : Pred} (h : ∃ T μ, Typed t T μ) :
    ∃ T μ, Typed (Term.refineOf t p) T μ := by
  obtain ⟨T, μ, hT⟩ := h
  unfold Term.refineOf
  split
  · exact ⟨_, _, Typed.never⟩
  · exact ⟨_, _, Typed.refine hT⟩

/-- Judgements for a list, from one per element. -/
theorem typedList_of_all : ∀ {ts : List Term}, (∀ t ∈ ts, ∃ T μ, Typed t T μ) →
    ∃ Ts, TypedList ts Ts
  | [], _ => ⟨[], .nil⟩
  | t :: ts, h => by
    obtain ⟨T, μ, hty⟩ := h t List.mem_cons_self
    obtain ⟨Ts, hs⟩ := typedList_of_all (fun u hu => h u (List.mem_cons_of_mem _ hu))
    exact ⟨T :: Ts, .cons hty hs⟩

/-- …and for a tail. -/
theorem typedOpt_of_all : ∀ {tail : Option Term}, (∀ t ∈ tail, ∃ T μ, Typed t T μ) →
    ∃ Tt, TypedOpt tail Tt
  | none, _ => ⟨none, .none⟩
  | some t, h => by
    obtain ⟨T, μ, hty⟩ := h t rfl
    exact ⟨some T, .some hty⟩

/-- Normalising a tuple keeps it derivable: a declared position at the bottom gives the
    bottom, which is derivable. -/
theorem typed_tupleOf {ts : List Term} {tail : Option Term}
    (h : ∀ t ∈ ts, ∃ T μ, Typed t T μ) (ht : ∀ t ∈ tail, ∃ T μ, Typed t T μ) :
    ∃ T μ, Typed (Term.tupleOf ts tail) T μ := by
  unfold Term.tupleOf
  split
  · exact ⟨_, _, Typed.never⟩
  · obtain ⟨Ts, hTs⟩ := typedList_of_all h
    obtain ⟨Tt, hTt⟩ := typedOpt_of_all ht
    exact ⟨_, _, Typed.tuple hTs hTt⟩

/-- Inversions for a tuple: each declared position, and the tail. -/
theorem typedList_mem : ∀ {ts : List Term} {Ts}, TypedList ts Ts → ∀ t ∈ ts, ∃ T μ, Typed t T μ
  | _, _, .nil, _, ht => nomatch ht
  | _, _, .cons hty hs, t, ht => by
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact ⟨_, _, hty⟩
    · exact typedList_mem hs t ht'

/-- …and both halves of a tuple at once, which is the form the four tuple rows take. -/
theorem typed_tuple_inv {ts : List Term} {tail : Option Term} :
    (∃ T μ, Typed (.tuple ts tail) T μ) →
    (∀ t ∈ ts, ∃ T μ, Typed t T μ) ∧ (∀ t ∈ tail, ∃ T μ, Typed t T μ)
  | ⟨_, _, h⟩ => by
    cases h with
    | tuple hL hT =>
        refine ⟨typedList_mem hL, ?_⟩
        cases hT with
        | none => exact fun t ht => nomatch ht
        | some hty => exact fun t ht => by cases ht; exact ⟨_, _, hty⟩

/-- The term a field carries. -/
def Field.termOf : Field → Term
  | .req t | .optional t => t
  | .fallback t _ => t

/-- **A derivation restated at indices that are functions of the term.** The held set of a
    derivable term is its denotation's and its member is `μSyn`'s, so an object row can write
    its field table down instead of choosing one. -/
theorem typed_canon {t : Term} (h : ∃ T μ, Typed t T μ) : Typed t (denote t).T (μSyn t) := by
  obtain ⟨T, μ, hT⟩ := h
  have h1 : (denote t).T = T := funext fun v => propext (typed_T_identity hT v)
  have h2 : μSyn t = μ := typed_μSyn hT
  rw [h1, h2]
  exact hT

/-- …and the same at a field, where the mark is `Field.isReq`. -/
theorem typedField_canon {fd : Field} (h : ∃ T μ, Typed (Field.termOf fd) T μ) :
    TypedField fd (denote (Field.termOf fd)).T (Field.isReq fd) (μSyn (Field.termOf fd)) := by
  cases fd with
  | req t => exact TypedField.req (typed_canon h)
  | optional t => exact TypedField.optional (typed_canon h)
  | fallback t v => exact TypedField.fallback (typed_canon h)

/-- A typed field carries a derivable term, whichever mark it has. -/
theorem typedField_termOf {fd : Field} {T π μ} (h : TypedField fd T π μ) :
    ∃ T' μ', Typed (Field.termOf fd) T' μ' := by
  cases h with
  | req h' => exact ⟨_, _, h'⟩
  | optional h' => exact ⟨_, _, h'⟩
  | fallback h' => exact ⟨_, _, h'⟩

/-- Inversion for an object: every declared field's term is derivable, and the rest is typed. -/
theorem typed_object_inv {b : Body} (h : ∃ T μ, Typed (.object b) T μ) :
    (∀ k, ∃ T μ, Typed (Field.termOf (b.at k)) T μ) ∧ ∃ R, TypedRest b.rest R := by
  obtain ⟨T, μ, hT⟩ := h
  cases hT with
  | object hf hr => exact ⟨fun k => typedField_termOf (hf k), _, hr⟩

/-- A rest that merges is closed, so its held set has no open part. -/
theorem typedRest_none_of_merge {x y r : Rest} {R : Option Held} (hm : Rest.merge x y = some r)
    (h : TypedRest x R) : R = none := by
  cases h <;> cases y <;> simp_all [Rest.merge]

/-- …and the same for the right factor. -/
theorem typedRest_none_of_merge_right {x y r : Rest} {R : Option Held}
    (hm : Rest.merge x y = some r) (h : TypedRest y R) : R = none := by
  cases h <;> cases x <;> simp_all [Rest.merge]

section StructuralTyped
set_option maxHeartbeats 1000000

/-! ### The same three layers, on the structural meet

The shared inner owns every row that reads the right operand alone. The nine flat families own
one left constructor each, and each of their rows answers a factor or the bottom. The four
container families carry the recursion at a subterm. -/

/-- `f` carries derivability with one term fixed on the left, at EVERY right operand. -/
def TypedSound (x : Term) (f : Term → Option Term) : Prop :=
  ∀ y z, f y = some z → (∃ T μ, Typed x T μ) → (∃ T μ, Typed y T μ) → ∃ T μ, Typed z T μ

/-- `fam` carries derivability with one term fixed on the left, over the operands it is handed. -/
def TypedFam (x : Term) (fam : Term → Option Term) : Prop :=
  ∀ y z, Delegated y → fam y = some z → (∃ T μ, Typed x T μ) → (∃ T μ, Typed y T μ) →
    ∃ T μ, Typed z T μ

/-- An object is derivable where every declared field's term is and the rest is typed: the
    indices are written down as functions of each field's own term rather than chosen. -/
theorem typed_object_of {fs : Finset Name} {F : {k // k ∈ fs} → Field} {r : Rest}
    {R : Option Held} (hf : ∀ k, ∃ T μ, Typed (Field.termOf (F k)) T μ) (hr : TypedRest r R) :
    ∃ T μ, Typed (.object (.mk fs F r)) T μ :=
  ⟨_, _, Typed.object (body := .mk fs F r) (R := R)
    (bind := fun k => (Field.isReq (F k), (denote (Field.termOf (F k))).T))
    (μs := fun k => μSyn (Field.termOf (F k)))
    (fun k => typedField_canon (hf k)) hr⟩

/-- The record-side field meet meets the field's term, with the record's term on the left. -/
theorem termOf_fieldMeetT {f : Term → Option Term} {fl fm : Field}
    (h : fieldMeetT f fl = some fm) : f (Field.termOf fl) = some (Field.termOf fm) := by
  cases fl <;> simp only [fieldMeetT, Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨tz, hz, rfl⟩ := h <;> exact hz

mutual
/-- Every row that reads the right operand alone is derivable wherever the family is. -/
theorem typed_meetSRight {x : Term} {fam : Term → Option Term} (hf : TypedFam x fam) :
    ∀ y z, meetSRight fam y = some z → (∃ T μ, Typed x T μ) → (∃ T μ, Typed y T μ) →
      ∃ T μ, Typed z T μ
  | .never, _, h, _, _ => by
      simp only [meetSRight, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
  | .held _ _ _, _, h, _, _ => by simp [meetSRight] at h
  | .legacy _ _, _, h, _, _ => by simp [meetSRight] at h
  | .custom _ _, _, h, _, _ => by simp [meetSRight] at h
  | .lazy _, _, h, _, _ => by simp [meetSRight] at h
  | .refine y p, _, h, hx, hy => by
      simp only [meetSRight] at h
      split at h
      · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        exact typed_refineOf (typed_meetSRight hf y w hw hx (typed_refine_inv hy))
      · exact absurd h (by simp)
  | .union os, _, h, hx, hy => by
      obtain ⟨zs, hF, _, hcz, rfl⟩ := meetSRight_union h
      refine typed_ofOptions hcz ?_
      intro t ht
      obtain ⟨o, ho, hom⟩ :=
        forall₂_mem_right (typed_meetSRightL hf os zs hF) (List.mem_of_mem_filter ht)
      exact hom hx (typed_union_inv hy o ho)
  | .string, _, h, hx, hy => hf .string _ trivial h hx hy
  | .number, _, h, hx, hy => hf .number _ trivial h hx hy
  | .decimal, _, h, hx, hy => hf .decimal _ trivial h hx hy
  | .boolean, _, h, hx, hy => hf .boolean _ trivial h hx hy
  | .binary, _, h, hx, hy => hf .binary _ trivial h hx hy
  | .null, _, h, hx, hy => hf .null _ trivial h hx hy
  | .literal k lv, _, h, hx, hy => hf (.literal k lv) _ trivial h hx hy
  | .set b, _, h, hx, hy => hf (.set b) _ trivial h hx hy
  | .opaq l, _, h, hx, hy => hf (.opaq l) _ trivial h hx hy
  | .array e, _, h, hx, hy => hf (.array e) _ trivial h hx hy
  | .record c, _, h, hx, hy => hf (.record c) _ trivial h hx hy
  | .tuple ts tl, _, h, hx, hy => hf (.tuple ts tl) _ trivial h hx hy
  | .object b, _, h, hx, hy => hf (.object b) _ trivial h hx hy
termination_by structural y => y

/-- The list companion: the union row's options, lifted pointwise. -/
theorem typed_meetSRightL {x : Term} {fam : Term → Option Term} (hf : TypedFam x fam) :
    ∀ os zs, List.Forall₂ (fun t w => meetSRight fam t = some w) os zs →
      List.Forall₂ (fun t w => (∃ T μ, Typed x T μ) → (∃ T μ, Typed t T μ) →
        ∃ T μ, Typed w T μ) os zs
  | [], _, h => by cases h; exact .nil
  | t :: ts, _, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun hx hy => typed_meetSRight hf t _ hh hx hy)
            (typed_meetSRightL hf ts _ ht)
termination_by structural os => os
end

/-- The tactic every flat family uses: a row answers one of its factors, the bottom, or nothing. -/
local macro "typed_fam" fam:ident : tactic => `(tactic|
  (intro y z hd h hx hy
   cases y <;> first | exact hd.elim | skip
   all_goals
     (simp only [$fam:ident, Term.meetLit] at h
      repeat' split at h
      all_goals
        first
          | (simp only [reduceCtorEq] at h; done)
          | (simp only [Option.some.injEq] at h
             subst h
             first
               | exact hx
               | exact hy
               | exact ⟨_, _, Typed.never⟩
               | exact ⟨_, _, Typed.opaq _⟩))))

/-- `string` meets its own literals and `opaque`, and each answer is a factor or the bottom. -/
theorem typed_famString : TypedFam Term.string famString := by typed_fam famString

/-- `number` likewise. -/
theorem typed_famNumber : TypedFam Term.number famNumber := by typed_fam famNumber

/-- `decimal` likewise. -/
theorem typed_famDecimal : TypedFam Term.decimal famDecimal := by typed_fam famDecimal

/-- `boolean` likewise. -/
theorem typed_famBoolean : TypedFam Term.boolean famBoolean := by typed_fam famBoolean

/-- `binary` likewise. -/
theorem typed_famBinary : TypedFam Term.binary famBinary := by typed_fam famBinary

/-- `null` likewise. -/
theorem typed_famNull : TypedFam Term.null famNull := by typed_fam famNull

/-- A literal meets its own base and an equal literal, and is the bottom elsewhere. -/
theorem typed_famLit (k : GroundKind) (lv : k.Carrier) :
    TypedFam (.literal k lv) (famLit k lv) := by typed_fam famLit

/-- Two set bases meet where they are equal. -/
theorem typed_famSet (b : SetBase) : TypedFam (.set b) (famSet b) := by typed_fam famSet

/-- `opaque` meets each self-identifying base, and another `opaque` at the conjoined policy. -/
theorem typed_famOpaq (l : Bool) : TypedFam (.opaq l) (famOpaq l) := by typed_fam famOpaq

/-! ### The container families: the four that read the recursion. -/

/-- An array meets an array at the element, and a tuple at every declared position. -/
theorem typed_famArr {x' : Term} {f : Term → Option Term} (hf : TypedSound x' f) :
    TypedFam (.array x') (famArr f) := by
  intro y z hd h hx hy
  cases y <;> first | exact hd.elim | skip
  case array e =>
      simp only [famArr] at h
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨T, μ, hT⟩ := hf e w hw (typed_array_inv hx) (typed_array_inv hy)
      exact ⟨_, _, Typed.array hT⟩
  case tuple ts tail =>
      obtain ⟨vs, tl, rfl, hts, htl⟩ := famArr_tuple h
      obtain ⟨hts', htail'⟩ := typed_tuple_inv hy
      refine typed_tupleOf ?_ ?_
      · intro w hw
        obtain ⟨t, ht, hm⟩ := forall₂_mem_right hts hw
        exact hf t w hm (typed_array_inv hx) (hts' t ht)
      · intro w hw
        rcases htl with ⟨-, rfl⟩ | ⟨t, u, rfl, rfl, hm⟩
        · exact nomatch hw
        · cases hw
          exact hf t _ hm (typed_array_inv hx) (htail' t rfl)
  case opaq l => simp [famArr] at h
  all_goals
    (simp only [famArr, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)

/-- A tuple's position functions, applied at one term: every answer is derivable. -/
theorem typed_applyAt_lift {y : Term} (hy : ∃ T μ, Typed y T μ) :
    ∀ {ts : List Term} {fs : List (Term → Option Term)} {vs : List Term},
      List.Forall₂ TypedSound ts fs → (∀ t ∈ ts, ∃ T μ, Typed t T μ) →
      List.Forall₂ (fun f v => f y = some v) fs vs →
      ∀ v ∈ vs, ∃ T μ, Typed v T μ := by
  intro ts
  induction ts with
  | nil => intro fs vs hfs _ hv; cases hfs; cases hv; intro v hvm; exact nomatch hvm
  | cons t ts ihs =>
      intro fs vs hfs hts hv
      cases hfs with
      | cons hf hfs' =>
          cases hv with
          | cons hh ht =>
              intro v hvm
              rcases List.mem_cons.mp hvm with rfl | hvm'
              · exact hf y v hh (hts t List.mem_cons_self) hy
              · exact ihs hfs' (fun u hu => hts u (List.mem_cons_of_mem _ hu)) ht v hvm'

/-- …and the same two tuples' positions zipped. -/
theorem typed_zipF_lift :
    ∀ {ts us : List Term} {fs : List (Term → Option Term)} {vs : List Term},
      List.Forall₂ TypedSound ts fs → (∀ t ∈ ts, ∃ T μ, Typed t T μ) →
      (∀ u ∈ us, ∃ T μ, Typed u T μ) →
      List.Forall₂ (fun (p : (Term → Option Term) × Term) v => p.1 p.2 = some v) (fs.zip us) vs →
      ∀ v ∈ vs, ∃ T μ, Typed v T μ := by
  intro ts
  induction ts with
  | nil => intro us fs vs hfs _ _ hv; cases hfs; cases hv; intro v hvm; exact nomatch hvm
  | cons t ts ihs =>
      intro us fs vs hfs hts hus hv
      cases hfs with
      | cons hf hfs' =>
          cases us with
          | nil => cases hv; intro v hvm; exact nomatch hvm
          | cons u us =>
              cases hv with
              | cons hh ht =>
                  intro v hvm
                  rcases List.mem_cons.mp hvm with rfl | hvm'
                  · exact hf u v hh (hts t List.mem_cons_self) (hus u List.mem_cons_self)
                  · exact ihs hfs' (fun w hw => hts w (List.mem_cons_of_mem _ hw))
                      (fun w hw => hus w (List.mem_cons_of_mem _ hw)) ht v hvm'

/-- A tuple meets an array at every declared position, and a tuple of one arity positionwise. -/
theorem typed_famTup {ts : List Term} {tail : Option Term}
    {fs : List (Term → Option Term)} {ftail : Option (Term → Option Term)}
    (hfs : List.Forall₂ TypedSound ts fs)
    (hft : (tail = none ∧ ftail = none) ∨
      ∃ t ft, tail = some t ∧ ftail = some ft ∧ TypedSound t ft) :
    TypedFam (.tuple ts tail) (famTup fs ftail) := by
  intro y z hd h hx hy
  obtain ⟨hts, htail⟩ := typed_tuple_inv hx
  cases y <;> first | exact hd.elim | skip
  case array e =>
      simp only [famTup] at h
      split at h
      next vs tl hvs htl =>
        simp only [Option.some.injEq] at h; subst h
        have hF : List.Forall₂ (fun f w => f e = some w) fs vs :=
          allSome_map_forall₂ _ (by rw [← applyAt_eq]; exact hvs)
        have he := typed_array_inv hy
        refine typed_tupleOf (typed_applyAt_lift he hfs hts hF) ?_
        intro w hw
        rcases hft with ⟨rfl, rfl⟩ | ⟨t, ft, rfl, rfl, hsound⟩
        · replace htl : some (none : Option Term) = some tl := htl
          simp only [Option.some.injEq] at htl; subst htl
          exact nomatch hw
        · replace htl : Option.map some (ft e) = some tl := htl
          obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp htl
          cases hw
          exact hsound e _ hu (htail t rfl) he
      next => exact absurd h (by simp)
  case tuple us tail' =>
      obtain ⟨hus, htail'⟩ := typed_tuple_inv hy
      simp only [famTup] at h
      split at h
      next hlen =>
        split at h
        next vs tl hvs htl =>
          simp only [Option.some.injEq] at h; subst h
          have hF : List.Forall₂
              (fun (p : (Term → Option Term) × Term) w => p.1 p.2 = some w) (fs.zip us) vs :=
            allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hvs)
          refine typed_tupleOf (typed_zipF_lift hfs hts hus hF) ?_
          intro w hw
          rcases hft with ⟨rfl, rfl⟩ | ⟨t, ft, rfl, rfl, hsound⟩
          · cases tail' with
            | none =>
                replace htl : some (none : Option Term) = some tl := htl
                simp only [Option.some.injEq] at htl; subst htl
                exact nomatch hw
            | some u => exact absurd htl (by simp)
          · cases tail' with
            | none => exact absurd htl (by simp)
            | some u =>
                replace htl : Option.map some (ft u) = some tl := htl
                obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp htl
                cases hw
                exact hsound u _ hw' (htail t rfl) (htail' u rfl)
        next => exact absurd h (by simp)
      next =>
        split at h
        next =>
          simp only [Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
        next => exact absurd h (by simp)
  case opaq l => simp [famTup] at h
  all_goals
    (simp only [famTup, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)

/-- A record meets a record at the value term, and an object through every declared field. -/
theorem typed_famRec {x' : Term} {f : Term → Option Term} (hf : TypedSound x' f) :
    TypedFam (.record x') (famRec f) := by
  intro y z hd h hx hy
  cases y <;> first | exact hd.elim | skip
  case record c =>
      simp only [famRec] at h
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨T, μ, hT⟩ := hf c w hw (typed_record_inv hx) (typed_record_inv hy)
      exact ⟨_, _, Typed.record hT⟩
  case object b =>
      simp only [famRec] at h
      obtain ⟨t, r, hrest, hmt, hok, hcase⟩ := recObj_extract h
      obtain ⟨hfb, Rb, hrb⟩ := typed_object_inv hy
      rcases hcase with ⟨rfl, -⟩ | rfl
      · exact ⟨_, _, Typed.never⟩
      · have hrt : ∃ T μ, Typed t T μ := by
          rw [hrest] at hrb
          cases hrb with
          | codec hT => exact ⟨_, _, hT⟩
        obtain ⟨Tr, μr, hTr⟩ := hf t r hmt (typed_record_inv hx) hrt
        refine typed_object_of ?_ (TypedRest.codec hTr)
        intro k
        obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfm, Option.getD_some]
        exact hf _ _ (termOf_fieldMeetT hfm) (typed_record_inv hx) (hfb k)
  case opaq l => simp [famRec] at h
  all_goals
    (simp only [famRec, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)

/-- An object meets an object over the shared names, and a record through every field. -/
theorem typed_famObj {a : Body} {g : {k // k ∈ a.fields} → Field → Option Field}
    {gt : {k // k ∈ a.fields} → Term → Option Field}
    {frest : Option (Term → Option Term)}
    (hg : ∀ (k : {k // k ∈ a.fields}) (fl fm : Field), g k fl = some fm →
      (∃ T μ, Typed (Field.termOf (a.at k)) T μ) → (∃ T μ, Typed (Field.termOf fl) T μ) →
      ∃ T μ, Typed (Field.termOf fm) T μ)
    (hgt : ∀ (k : {k // k ∈ a.fields}) (u : Term) (fm : Field), gt k u = some fm →
      (∃ T μ, Typed (Field.termOf (a.at k)) T μ) → (∃ T μ, Typed u T μ) →
      ∃ T μ, Typed (Field.termOf fm) T μ)
    (hfr : ∀ fr, frest = some fr → ∃ t, a.rest = .codec t ∧ TypedSound t fr) :
    TypedFam (.object a) (famObj a g gt frest) := by
  intro y z hd h hx hy
  obtain ⟨hfa, Ra, hra⟩ := typed_object_inv hx
  cases y <;> first | exact hd.elim | skip
  case object b =>
      simp only [famObj] at h
      obtain ⟨r, hr, hcase⟩ := objObj_extract h
      obtain ⟨hfb, Rb, hrb⟩ := typed_object_inv hy
      rcases hcase with ⟨rfl, -⟩ | ⟨-, -, hok, hz⟩
      · exact ⟨_, _, Typed.never⟩
      · rcases hz with ⟨rfl, -⟩ | rfl
        · exact ⟨_, _, Typed.never⟩
        · refine typed_object_of (R := none) ?_ ?_
          · intro k
            obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
            rw [hfm, Option.getD_some]
            exact hg _ _ _ hfm (hfa _) (hfb _)
          · rw [typedRest_none_of_merge hr hra] at hra
            rw [typedRest_none_of_merge_right hr hrb] at hrb
            exact TypedRest.merge_closed hr hra hrb
  case record x =>
      simp only [famObj] at h
      obtain ⟨fr, r, hfrest, hrx, hok, hcase⟩ := objRec_extract h
      obtain ⟨t, hrest, hsound⟩ := hfr fr hfrest
      rcases hcase with ⟨rfl, -⟩ | rfl
      · exact ⟨_, _, Typed.never⟩
      · have hxin := typed_record_inv hy
        have hrt : ∃ T μ, Typed t T μ := by
          rw [hrest] at hra
          cases hra with
          | codec hT => exact ⟨_, _, hT⟩
        obtain ⟨Tr, μr, hTr⟩ := hsound x r hrx hrt hxin
        refine typed_object_of ?_ (TypedRest.codec hTr)
        intro k
        obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp (hok k)
        rw [hfm, Option.getD_some]
        exact hgt _ _ _ hfm (hfa _) hxin
  case opaq l => simp [famObj] at h
  all_goals
    (simp only [famObj, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)

/-! ### The outer theorem. -/

mutual
/-- **The typed fragment is closed under the meet.** Where two derivable terms have a meet, the
    meet is derivable. The union row is the one that needs the certificate: `unionOk` gives
    pairwise `Orth`, and `dincomp_of_unionOk` reads §5's (D) off it. -/
theorem typed_meet : ∀ x y z, Term.meet x y = some z →
    (∃ T μ, Typed x T μ) → (∃ T μ, Typed y T μ) → ∃ T μ, Typed z T μ
  | .never, _, _, h, _, _ => by
      simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
  | .held _ _ _, y, _, h, _, _ => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)
          | exact absurd h (by simp [Term.meet])
  | .legacy _ _, y, _, h, _, _ => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)
          | exact absurd h (by simp [Term.meet])
  | .custom _ _, y, _, h, _, _ => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)
          | exact absurd h (by simp [Term.meet])
  | .lazy _, y, _, h, _, _ => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)
          | exact absurd h (by simp [Term.meet])
  | .refine x p, y, _, h, hx, hy => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
      | _ =>
        simp only [Term.meet] at h
        split at h
        · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
          exact typed_refineOf (typed_meet x _ w hw (typed_refine_inv hx) hy)
        · exact absurd h (by simp)
  | .union os, y, _, h, hx, hy => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
      | _ =>
        obtain ⟨zs, hF, _, hcz, rfl⟩ := meet_union_of h (by simp)
        refine typed_ofOptions hcz ?_
        intro t ht
        obtain ⟨o, ho, hom⟩ :=
          forall₂_mem_right (typed_meetL os _ zs hF) (List.mem_of_mem_filter ht)
        exact hom (typed_union_inv hx o ho) hy
  | .string, y, z, h, hx, hy => typed_meetSRight typed_famString y z h hx hy
  | .number, y, z, h, hx, hy => typed_meetSRight typed_famNumber y z h hx hy
  | .decimal, y, z, h, hx, hy => typed_meetSRight typed_famDecimal y z h hx hy
  | .boolean, y, z, h, hx, hy => typed_meetSRight typed_famBoolean y z h hx hy
  | .binary, y, z, h, hx, hy => typed_meetSRight typed_famBinary y z h hx hy
  | .null, y, z, h, hx, hy => typed_meetSRight typed_famNull y z h hx hy
  | .literal k lv, y, z, h, hx, hy => typed_meetSRight (typed_famLit k lv) y z h hx hy
  | .set b, y, z, h, hx, hy => typed_meetSRight (typed_famSet b) y z h hx hy
  | .opaq l, y, z, h, hx, hy => typed_meetSRight (typed_famOpaq l) y z h hx hy
  | .array e, y, z, h, hx, hy =>
      typed_meetSRight (typed_famArr (fun t w hw => typed_meet e t w hw)) y z h hx hy
  | .record c, y, z, h, hx, hy =>
      typed_meetSRight (typed_famRec (fun t w hw => typed_meet c t w hw)) y z h hx hy
  | .tuple ts tl, y, z, h, hx, hy => by
      cases tl with
      | none =>
          exact typed_meetSRight (typed_famTup (typed_meetSTs ts) (Or.inl ⟨rfl, rfl⟩)) y z h hx hy
      | some t =>
          exact typed_meetSRight (typed_famTup (typed_meetSTs ts)
            (Or.inr ⟨t, Term.meet t, rfl, rfl, fun u w hw => typed_meet t u w hw⟩)) y z h hx hy
  | .object (.mk fs f r), y, z, h, hx, hy => by
      cases r with
      | codec t =>
          exact typed_meetSRight (typed_famObj (a := .mk fs f (.codec t))
            (fun k fl fm hm => typed_Field_meet (f k) fl fm hm)
            (fun k u fm hm => typed_Field_meetT (f k) u fm hm)
            (fun fr hfr => ⟨t, rfl, by
              simp only [Option.some.injEq] at hfr
              subst hfr
              exact fun u w hw => typed_meet t u w hw⟩)) y z h hx hy
      | drop =>
          exact typed_meetSRight (typed_famObj (a := .mk fs f .drop)
            (fun k fl fm hm => typed_Field_meet (f k) fl fm hm)
            (fun k u fm hm => typed_Field_meetT (f k) u fm hm)
            (fun _ hfr => absurd hfr (by simp))) y z h hx hy
      | refuse =>
          exact typed_meetSRight (typed_famObj (a := .mk fs f .refuse)
            (fun k fl fm hm => typed_Field_meet (f k) fl fm hm)
            (fun k u fm hm => typed_Field_meetT (f k) u fm hm)
            (fun _ hfr => absurd hfr (by simp))) y z h hx hy
termination_by structural x => x

/-- The union row's options, lifted pointwise at the fixed partner. -/
theorem typed_meetL : ∀ (os : List Term) (y : Term) (zs : List Term),
    List.Forall₂ (fun t w => Term.meet t y = some w) os zs →
    List.Forall₂ (fun t w => (∃ T μ, Typed t T μ) → (∃ T μ, Typed y T μ) →
      ∃ T μ, Typed w T μ) os zs
  | [], _, _, h => by cases h; exact .nil
  | t :: ts, y, _, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun hx hy => typed_meet t y _ hh hx hy) (typed_meetL ts y _ ht)
termination_by structural os => os

/-- Every position of a tuple carries the meet at that position. -/
theorem typed_meetSTs : ∀ ts : List Term, List.Forall₂ TypedSound ts (Term.meetSTs ts)
  | [] => .nil
  | t :: ts => .cons (fun u w hw => typed_meet t u w hw) (typed_meetSTs ts)
termination_by structural ts => ts

/-- Two fields at one name carry two terms that meet. -/
theorem typed_Field_meet : ∀ (f fl : Field) (fm : Field), Field.meet f fl = some fm →
    (∃ T μ, Typed (Field.termOf f) T μ) → (∃ T μ, Typed (Field.termOf fl) T μ) →
    ∃ T μ, Typed (Field.termOf fm) T μ
  | .req x, .req y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet x y tz hz hx hy
  | .req x, .optional y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet x y tz hz hx hy
  | .optional x, .req y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet x y tz hz hx hy
  | .req x, .fallback y _, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet x y tz hz hx hy
  | .fallback x _, .req y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet x y tz hz hx hy
  | .optional x, .optional y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet x y tz hz hx hy
  | .optional _, .fallback _ _, _, h, _, _ => by simp [Field.meet] at h
  | .fallback _ _, .optional _, _, h, _, _ => by simp [Field.meet] at h
  | .fallback _ _, .fallback _ _, _, h, _, _ => by simp [Field.meet] at h
termination_by structural f => f

/-- …and a field met with a record's term carries the field's term and that term. -/
theorem typed_Field_meetT : ∀ (f : Field) (y : Term) (fm : Field), Field.meetT f y = some fm →
    (∃ T μ, Typed (Field.termOf f) T μ) → (∃ T μ, Typed y T μ) →
    ∃ T μ, Typed (Field.termOf fm) T μ
  | .req x, y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet x y tz hz hx hy
  | .optional x, y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet x y tz hz hx hy
  | .fallback _ _, _, _, h, _, _ => by simp [Field.meetT] at h
termination_by structural f => f
end

end StructuralTyped

end Calculus
