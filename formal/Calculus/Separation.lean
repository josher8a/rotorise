import Calculus.ExactA

/-!
# Derivability, separation, and what the pair does not record

Two of the twenty-one constructors are derivable from the others. `SepJV` states separation
on the pair, in the one direction that holds. And the negative results say what the pair
does not record, with what to use instead.
-/

namespace Calculus

noncomputable section
/-! ## Two of the twenty-one constructors are derivable

`array` is the degenerate `tuple` — empty fixed part, uniform tail — and `record` the
degenerate `object`: no declared names, `codec` rest. Both rows agree with their general
form *pointwise*, on both sides, so nothing in the analysis depends on them existing.

They are kept anyway, and the reason is the shape of the row rather than the size of the
language. `array`'s row is `allP`, one fold; the `tuple` it expands to is `alignP`, which
carries a length discipline that at `([], some c)` can never fire. `record`'s row is one
`decide` over the key set; the `object` it expands to is `valPresentT && objAdmV`, a
presence guard over an empty field table — vacuous — conjoined with a traversal that
consults `entryP` at every name only to be handed the rest policy back. So the narrow
constructor buys a row a reader can check by eye, and that is the **opposite** trade from
`set`, where a narrower constructor bought *exactness*: `set b` cannot be spelled as a
`refine` of anything, and indexing by the base is what made `encSet`'s collision guard
provably dead. Convenience here, necessity there.

### …and `union` is not a congruence for codec equivalence

`record c` and `object ∅ noFields (.codec c)` have identical rows on both sides, hence —
by `Adm_exact`/`AdmA_exact`, which take no hypothesis — identical domains on both sides.
They are the same codec as far as anything observable through `e` and `p` can tell.

`union` still distinguishes them, and `union_not_congruent` is the pair. An option's
admission is `admitOptV`, which matches the **constructor**: `specOf (.record c) = none`,
so the option is admitted *by attempt*, while `specOf (.object (.mk ∅ noFields (.codec c)))` is
`some ⟨∅, _⟩`, so the option is admitted *by names* — and an empty name spec admits no map
that carries a name. On `{"a" ↦ "x"}` the first option answers `true` and the second
`false`, with equal domains behind both.

This is not a defect in the rows and not one in `select`; it is the price of deciding an
object option syntactically, which §5 argues for on other grounds ("an open object that must
be an option should declare what it means to keep").
What that passage does not observe is this consequence: **term equivalence is not a
congruence for `union`**, so no rewrite that replaces a subterm by a domain-equal one is
sound inside a `union`. Anything that wants to normalize `record` to `object` — or `array`
to `tuple`, which is safe, both being `specOf = none` — has to check the spec, not the
domain. -/

/-- The empty field table. Not `by simp`: `simp`'s route to a vacuous `Finset ∅` goal reaches
    `Classical.choice`, and this is a *definition*, so it would put the axiom under every
    theorem below rather than under a proof. `Finset.notMem_empty` is the direct term. -/
def noFields : {k // k ∈ (∅ : Finset Name)} → Field :=
  fun k => absurd k.2 (Finset.notMem_empty k.1)

/-- `array`'s fold is its `tuple`'s alignment. The induction is on the value's list, not the
    term: `alignP [] (some P)` recurses with the same `(([], some P))`, so there is nothing
    structural to follow on the term side. -/
theorem arrayRow (c : Term) (v : Value) : Adm (.array c) v = Adm (.tuple [] (some c)) v := by
  cases v with
  | arr xs =>
    simp only [Adm, AdmList, AdmOptT]
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [allP, alignP, ih]
  | _ => rfl

/-- The same on the read side; `allPA`/`alignPA` are the same two shapes over `Attr`. -/
theorem arrayRowA (c : Term) (a : Attr) : AdmA (.array c) a = AdmA (.tuple [] (some c)) a := by
  cases a with
  | l as =>
    simp only [AdmA, AdmAList, AdmAOptT]
    induction as with
    | nil => rfl
    | cons x as ih => simp [allPA, alignPA, ih]
  | _ => rfl

/-- `record`'s one `decide` is its `object`'s guard-and-traverse, with both extra pieces
    dead: the presence guard quantifies over an empty field table, and `entryP` finds no
    declaration at any name and hands back the rest policy.

    Spelled out rather than left to `simp`. The one-line `simp [Adm, valPresentT, objAdmV,
    entryP, AdmRest, noFields, MapOf.at]` proves it and reaches `Classical.choice` — the
    `decide` over a `Finset` subtype is where simp picks up a classical instance — which
    `#assert_axioms_all` rejects. `decide_eq_true` and `dif_neg` are the two facts actually
    needed. -/
theorem recordRow (c : Term) (v : Value) :
    Adm (.record c) v = Adm (.object (.mk ∅ noFields (.codec c))) v := by
  cases v with
  | map keys f =>
    have hv : valPresentT ∅ noFields keys = true :=
      decide_eq_true (fun k => absurd k.2 (Finset.notMem_empty k.1))
    have he : ∀ k : Name, entryP ⟨∅, fun k => AdmField (noFields k)⟩ (some (Adm c)) k
        = some (Adm c) := fun k => by
      simp only [entryP, MapOf.at, dif_neg (Finset.notMem_empty k)]
    simp only [Adm, AdmBody, hv, Bool.true_and, objAdmV, AdmRest, he]
  | _ => rfl

/-- The read side, with one extra dead piece: `keepT (.codec c) ∅` is the constant `true`,
    an open rest keeping every name, so `objAdmA`'s guard discharges by `true_implies`. -/
theorem recordRowA (c : Term) (a : Attr) :
    AdmA (.record c) a = AdmA (.object (.mk ∅ noFields (.codec c))) a := by
  cases a with
  | m keys g =>
    have hv : reqPresentT ∅ noFields keys = true :=
      decide_eq_true (fun k => absurd k.2 (Finset.notMem_empty k.1))
    have he : ∀ k : Name, entryPA ⟨∅, fun k => AdmAField (noFields k)⟩ (some (AdmA c)) k
        = some (AdmA c) := fun k => by
      simp only [entryPA, MapOf.at, dif_neg (Finset.notMem_empty k)]
    simp only [AdmA, AdmABody, hv, Bool.true_and, objAdmA, AdmARest, keepT, he, true_implies]
  | _ => rfl

/-! ### Row equality is domain equality, for free

Each of the four above becomes a statement about `e` and `p` with no further work, which is
what an unconditional `Adm_exact`/`AdmA_exact` buys: the row *is* the domain, so a proof
that two rows agree is a proof that two codecs' domains agree. Under the old exactness —
a hypothesis to discharge per term — each of these would have needed its own discharge. -/

theorem arrayDom (c : Term) (v : Value) :
    ((denote (.array c)).e v).isSome = ((denote (.tuple [] (some c))).e v).isSome :=
  Bool.coe_iff_coe.mp
    ((Adm_exact (.array c) v).symm.trans (arrayRow c v ▸ Adm_exact (.tuple [] (some c)) v))

theorem arrayDomA (c : Term) (a : Attr) :
    ((denote (.array c)).p a).isSome = ((denote (.tuple [] (some c))).p a).isSome :=
  Bool.coe_iff_coe.mp
    ((AdmA_exact (.array c) a).symm.trans (arrayRowA c a ▸ AdmA_exact (.tuple [] (some c)) a))

theorem recordDom (c : Term) (v : Value) :
    ((denote (.record c)).e v).isSome = ((denote (.object (.mk ∅ noFields (.codec c)))).e v).isSome :=
  Bool.coe_iff_coe.mp
    ((Adm_exact (.record c) v).symm.trans
      (recordRow c v ▸ Adm_exact (.object (.mk ∅ noFields (.codec c))) v))

theorem recordDomA (c : Term) (a : Attr) :
    ((denote (.record c)).p a).isSome = ((denote (.object (.mk ∅ noFields (.codec c)))).p a).isSome :=
  Bool.coe_iff_coe.mp
    ((AdmA_exact (.record c) a).symm.trans
      (recordRowA c a ▸ AdmA_exact (.object (.mk ∅ noFields (.codec c))) a))

/-- `record` is admitted by attempt… -/
theorem specOf_record (c : Term) : specOf (.record c) = none := rfl

/-- …and the `object` with its domain is admitted by names. -/
theorem specOf_object_isSome (c : Term) :
    (specOf (.object (.mk ∅ noFields (.codec c)))).isSome = true := rfl

/-- **`union` is not a congruence for domain equality.** `recordDom` and `recordDomA` say
    these two terms have the same `e` and the same `p` at every point. As *options* they
    disagree at `{"a" ↦ "x"}`: the first is attempted and admits, the second is asked for
    its names and refuses, because its spec is empty and the map is not.

    So a normalization pass over `Term` may not replace `record c` by its `object` inside a
    `union` — nor, in general, replace any subterm by a domain-equal one there. See the
    section note above; §5 gives the reason `ρ` goes unread and does not draw this
    corollary. -/
theorem union_not_congruent :
    admitOptV (specOf (.record .string), Adm (.record .string))
        (.map {"a"} (fun _ => .str "x")) = true
      ∧ admitOptV (specOf (.object (.mk ∅ noFields (.codec .string))),
          Adm (.object (.mk ∅ noFields (.codec .string)))) (.map {"a"} (fun _ => .str "x")) = false :=
  ⟨rfl, rfl⟩

/-! ## Separation on the pair, and the one direction that fails

`SepJV` and `SepJA` state separation on the rows this file proves exact. The value side is a
single clause — `Adm` folds the kind gate into its own rows, so there is no second disjunct
for a coarse label to supply. The attribute side keeps a member disjunct, and
`sepJA_needs_member` is the pair that shows it doing work: `legacy` widens a read past the
member its own term claims, so `AdmA` does not bound `μSyn`.

**What this section exists to record is the direction that fails.** A discharger consumes
disjointness of the options `select` builds, and at an `object` option that is `keysOk` —
names, not contents. So `Adm` is not an over-approximation of admission there, it is strictly
*tighter*, and `not_uAtCan_of_sepJ` at the end of the section is the discharger restated on
`SepJV`/`SepJA` and refuted, with every other premise met. `Orthogonality.lean` states the
discharge on what `select` consults, which is the repair the `object` row invites. -/


/-! ~~selTagV_mem~~ and ~~selTagA_mem~~ went with the tag-filtered sum. They said that the option
the filter lands on is one of the options; a dissection is a certified `union` now, and
`selOptV_mem_admitOpt` is where that fact is read off. -/

/-- **Separation on the joint predicate, value side — one clause.** §5's ~~SepV~~ offers a
    choice between disjoint kinds and disjoint admissible sets; `Adm` carries the kind gate
    in its own rows, so the first disjunct is subsumed (~~Adm_kind~~) and the definition
    collapses. -/
def SepJV (x y : Term) : Prop := ∀ v, Adm x v = true → Adm y v = false

/-- **…and attribute side, which does *not* collapse.** The member disjunct stays, because
    `AdmA` does not bound `μSyn`.

    The reason used to be `setMember`'s — one value kind, three attribute members, so a
    `set` row admitted `SS`, `NS` and `BS` whatever its element term was. That reason is
    **gone**: `set` is indexed by its base, so its wire family is a function of the index
    and its row names one member. The clause survives anyway, because the phenomenon was
    never `set`'s alone. `legacy` widens a read past the member its own term claims — `p`
    falls back to a channel the term carries as data — so `AdmA` still fails to bound
    `μSyn`, and `sepJA_needs_member` is now witnessed there. -/
def SepJA (x y : Term) : Prop :=
  (∃ μx μy, μSyn x = some μx ∧ μSyn y = some μy ∧ μx ≠ μy) ∨
  (∀ a, AdmA x a = true → AdmA y a = false)

/-- A read channel that fires at `N` and nowhere else — `legacy`'s widening, minimal. -/
def rNum : Attr → Option Value := fun a => match a with | .n _ => some (.str "x") | _ => none

/-- **The member disjunct is load-bearing, and the witness moved.**

    It used to be `set(string)` against `set(number)`: they differ in `μSyn` and were
    indistinguishable to `AdmA`, which admitted `NS` at both. Indexing `set` killed that
    pair — the wire family is now a function of the base, so `AdmA` separates those two on
    its own — and it did **not** kill the disjunct, because `set` was never the only way to
    have a read that outruns `μSyn`.

    `legacy` is. `legacy(string, r)` stores `S`, and `r` reading an `.n` widens `p` past the
    member the term claims; `decimal` stores `N` and admits the same attribute. So the two
    are separated by `μSyn` and not by `AdmA`, which is exactly what the first clause of
    `SepJA` is for. -/
theorem sepJA_needs_member :
    ¬ (∀ a, AdmA (.legacy .string rNum) a = true → AdmA .decimal a = false) := by
  intro h
  exact absurd (h (.n (.of "1")) (by simp [AdmA, rNum])) (by simp [AdmA]; decide)

/-- …and the pair really is separated — by the member disjunct alone, which is what makes
    `SepJA`'s two clauses independent rather than redundant. -/
theorem sepJA_legacy_decimal : SepJA (.legacy .string rNum) .decimal :=
  Or.inl ⟨.S, .N, rfl, rfl, by decide⟩

/-! ## What the pair does not record, and what to use instead

A predicate on values does not say how a term is *written*. `string` and `refine(string, ⊤)`
denote the same pair and have the same `Adm`, so nothing defined on the pair tells them
apart. The retired table that answered this read the constructor instead, which is why
nothing consumed it. `Decides` below is the semantic notion §5's prose was reaching for,
pinned from the pair rather than read off the syntax. The witness that the two
questions are different is the one theorem kept from that table's section, immediately
below. -/

/-- A refinement by the trivially-true predicate: the same pair as the bare base. -/
def qTop : Value → Bool := fun _ => true

/-- **How a term is written is not a function of what it admits.** Two terms, one a
    refinement of the other, agreeing on the joint predicate at every value. -/
theorem Adm_string_eq_refine : Adm .string = Adm (.refine .string (.closure qTop)) := by
  funext v; simp [Adm, Pred.eval, qTop]





/-- **`SepJV` suffices for the codec-level discharge.** The joint predicate is tighter than
    the rows it replaces, so `SepJV` is a *weaker* statement — but `Adm_sound` connects it
    straight to the denotation: where `x` writes, `y` refuses.

    This said "and that is all the discharge needs", which is where it over-claimed. What a
    discharger consumes is disjointness of the *options* `select` builds, and an object option
    is admitted by `keysOk` rather than by attempting its codec. The section
    below is that gap, with the pair that refutes the stronger reading. -/
theorem admitV_of_sepJV {x y : Term} (h : SepJV x y) (v : Value) (a : Attr)
    (hx : (denote x).e v = some a) : ((denote y).e v).isSome = false := by
  have hAx : Adm x v = true := Adm_sound x hx
  have hAy : Adm y v = false := h v hAx
  cases hy : (denote y).e v with
  | none => rfl
  | some b => exact absurd (Adm_sound y hy) (by simp [hAy])

/-- …and on the attribute side, from `SepJA`'s second disjunct. -/
theorem admitA_of_sepJA {x y : Term} (h : ∀ a, AdmA x a = true → AdmA y a = false)
    (a : Attr) (v : Value) (hx : (denote x).p a = some v) :
    ((denote y).p a).isSome = false := by
  have hAx : AdmA x a = true := AdmA_sound x hx
  have hAy : AdmA y a = false := h a hAx
  cases hy : (denote y).p a with
  | none => rfl
  | some w => exact absurd (AdmA_sound y hy) (by simp [hAy])

/-! ### …and it does **not** suffice for the discharger, because of `adm`'s `object` row

The paragraph above says the discharge never needed `adm`'s extra strength. That is true of
the two theorems it is stated about and false of the theorem the migration exists to move,
and the difference is worth being precise about because the whole retirement of `adm` turns
on it.

`admitV_of_sepJV` is a claim about the **codec**: where `x`'s `e` writes, `y`'s `e` refuses.
A discharger is a claim about the **options `select` builds**, and at an `object` those are not
the same test. `admitOptV` records the asymmetry already — an object option is
admitted by `keysOk`, which reads which names a map carries and never what they hold — but
the corollary was not drawn: `Adm` is not an over-approximation of `OptionSem.admitV` at an
object, it is strictly *tighter*, and disjointness of a tighter predicate does not imply
disjointness of admission.

`adm (.object _) = ⊤` is what makes §5's generation sound here, and it is not slack. It is
exactly the over-approximation that turns `adm`-disjointness into admission-disjointness,
and it is why ~~SepV~~ cannot separate two objects at all: both `κ`s are `[map]` and both
`adm`s are `⊤`, so neither disjunct is available. Restate the discharger on `SepJV` and the
pair separates — while `select` attempts both options, so (U) genuinely fails. The premise
gets *stronger* and the theorem becomes *false*.

The witness is two objects with the same names and different field terms. Both are derivable
(`Typed.object`), both closed (`rest = drop`), and both lawful, so no other premise of the
discharger is what declines them — which is what makes `not_uAtCan_of_sepJ` a
refutation of the migration rather than a failure to find its proof.

And the `object` row is the *only* obstruction: `admitV_Adm_nonObject` and
`admitA_AdmA_nonObject` are the containments the discharger needs, and they hold, from
exactness alone, for every term whose `specOf` is `none` — which is every term but an
`object`. -/

/-- One required field, holding a string. -/
def bodyReqStr : Body := .mk {"a"} (fun _ => .req .string) .drop

/-- The same name, the same policy, a different field term. -/
def bodyReqNum : Body := .mk {"a"} (fun _ => .req .number) .drop

def objReqStr : Term := .object bodyReqStr
def objReqNum : Term := .object bodyReqNum

/-- A map the first object writes and the second refuses. -/
def mapReqStr : Value := .map {"a"} (fun _ => .str "x")


theorem Adm_objReqStr : Adm objReqStr mapReqStr = true := by
  simp [objReqStr, bodyReqStr, mapReqStr, Adm, AdmBody, AdmField, objAdmV,
    valPresentT, entryP, MapOf.at]

theorem Adm_objReqNum : Adm objReqNum mapReqStr = false := by
  simp [objReqNum, bodyReqNum, mapReqStr, Adm, AdmBody, AdmField, objAdmV,
    valPresentT, entryP, MapOf.at, inD]

/-- **The joint predicate separates the pair on the writable side.** A map the first admits
    carries a string at `"a"`, which the second's field term refuses; and neither admits a
    value that is not a map. -/
theorem sepJV_objReq : SepJV objReqStr objReqNum := by
  intro v hv
  cases v with
  | map keys g =>
    simp only [objReqStr, bodyReqStr, Adm, AdmBody, valPresentT, objAdmV, entryP, MapOf.at,
      Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [objReqNum, bodyReqNum, Adm, AdmBody, valPresentT, objAdmV, entryP, MapOf.at,
      decide_eq_true_eq, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine Or.inr fun h => ?_
    have ha : "a" ∈ keys := hv.1 ⟨"a", Finset.mem_singleton_self _⟩
    have h1 := hv.2 ⟨"a", ha⟩
    have h2 := h ⟨"a", ha⟩
    simp only [Finset.mem_singleton, dif_pos, AdmField] at h1 h2
    cases hg : g ⟨"a", ha⟩ <;> simp_all [Adm, inD]
  | _ => rfl

/-- …and on the readable side, on the `AdmA` disjunct: the member disjunct is no help,
    both objects being `⇝ M`. -/
theorem sepJA_objReq : SepJA objReqStr objReqNum := by
  refine Or.inr fun a ha => ?_
  cases a with
  | m keys g =>
    simp only [objReqStr, bodyReqStr, AdmA, AdmABody, reqPresentT, objAdmA, entryPA,
      MapOf.at, keepT, Bool.and_eq_true, decide_eq_true_eq] at ha
    simp only [objReqNum, bodyReqNum, AdmA, AdmABody, reqPresentT, objAdmA, entryPA,
      MapOf.at, keepT, decide_eq_true_eq, Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    refine Or.inr fun h => ?_
    have ha' : "a" ∈ keys := ha.1 ⟨"a", Finset.mem_singleton_self _⟩
    have h1 := ha.2 ⟨"a", ha'⟩
    have h2 := h ⟨"a", ha'⟩
    simp only [Finset.mem_singleton, dif_pos, AdmAField] at h1 h2
    cases hg : g ⟨"a", ha'⟩ <;> simp_all [AdmA]
  | _ => rfl

theorem typed_objReqStr :
    Typed objReqStr (HObject {"a"} (fun _ => (true, fun v => ∃ s, v = .str s)) none)
      (some .M) := .object (fun _ => .req .string) .drop

theorem typed_objReqNum :
    Typed objReqNum
      (HObject {"a"}
        (fun _ => (true, fun v => ∃ d, v = .num d ∧ Numeral.WF d.toDec = true)) none)
      (some .M) := .object (fun _ => .req .number) .drop

theorem lawful_objReqStr : Lawful (denote objReqStr) :=
  soundness typed_objReqStr ⟨fun _ => trivial, trivial⟩ ⟨fun _ => trivial, trivial⟩

theorem lawful_objReqNum : Lawful (denote objReqNum) :=
  soundness typed_objReqNum ⟨fun _ => trivial, trivial⟩ ⟨fun _ => trivial, trivial⟩

/-- **The pair is not uniquely admitting.** `select` counts an object option by its
    structure, the two specs are the same spec, and neither field is a literal — so content
    admission asks nothing of either, a map the first option writes is admitted by both, and
    the filter is not a singleton. This is the pair structural admission does **not** resolve,
    and the reason the phase is literals rather than field terms. -/
theorem not_uAtCan_objReq : ¬ UAtCan [objReqStr, objReqNum] := by
  intro h
  obtain ⟨a, ha⟩ :=
    Option.isSome_iff_exists.mp ((Adm_exact objReqStr mapReqStr).mp Adm_objReqStr)
  have hfil := (h (optionSemOf (denote objReqStr) (specOf objReqStr)) (by simp [semsOf])
    mapReqStr a (by rw [optionSemOf_c]; exact ha)).2
  simp [semsOf, objReqStr, objReqNum, bodyReqStr, bodyReqNum, specOf, Body.spec, optionSemOf,
    OptionSem.byStructure, keysOk, literalsOk, litOkV, altsOkV, altsOfField, MapOf.at,
    mapReqStr] at hfil

/-- **Admission does not imply the row**, which is the route the discharger would have to
    take. An object option admits by names; `Adm` asks the field terms. -/
theorem not_admitV_le_Adm :
    ¬ ∀ (t : Term) (v : Value),
      (optionSemOf (denote t) (specOf t)).admitV v = true → Adm t v = true := fun h =>
  absurd (h objReqNum mapReqStr rfl) (by simp [Adm_objReqNum])

/-- **The discharger, restated on the joint predicate, is false.** Every premise holds of
    `[objReqStr, objReqNum]` and the conclusion does not. This is the theorem that would have
    had to survive for the per-aspect tables and their separation to be retired *in favour of*
    `Adm`, `AdmA`, `SepJV` and `SepJA`; it does not, which is why the separation layer was
    retired in favour of `Orthogonality.lean` instead and the tables stayed. The reason is a
    row rather than a
    proof — see the section note above, which is wider than this theorem: the `object` row is
    the whole obstruction on the *value* side only, and `sepJA_needs_member` is a second one on
    the read side, at a different constructor and reached by no premise here. -/
theorem not_uAtCan_of_sepJ :
    ¬ ∀ (opts : List Term),
      (∀ t ∈ opts, Lawful (denote t)) →
      (∀ t ∈ opts, t.isOpenObject = false) →
      List.Pairwise SepJV opts →
      List.Pairwise SepJA opts →
      UAtCan opts := by
  intro h
  refine not_uAtCan_objReq (h [objReqStr, objReqNum] ?_ ?_ ?_ ?_)
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact lawful_objReqStr
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact lawful_objReqNum
      · exact nomatch ht
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · exact nomatch ht
  · refine .cons (fun y hy => ?_) (.cons (by simp) .nil)
    rcases List.mem_singleton.mp hy with rfl
    exact sepJV_objReq
  · refine .cons (fun y hy => ?_) (.cons (by simp) .nil)
    rcases List.mem_singleton.mp hy with rfl
    exact sepJA_objReq

/-- **The containment the discharger needs, everywhere it holds.** Off an `object`, `specOf`
    is `none`, admission *is* attempted encoding, and exactness identifies it with the row.
    So the `object` row is the whole of the obstruction above. -/
theorem admitV_Adm_nonObject (t : Term) (hs : specOf t = none) {v : Value}
    (h : (optionSemOf (denote t) (specOf t)).admitV v = true) : Adm t v = true := by
  rw [hs] at h
  exact (Adm_exact t v).mpr h

/-- …and its twin on the readable side. -/
theorem admitA_AdmA_nonObject (t : Term) (hs : specOf t = none) {a : Attr}
    (h : (optionSemOf (denote t) (specOf t)).admitA a = true) : AdmA t a = true := by
  rw [hs] at h
  exact (AdmA_exact t a).mpr h

/-! ### `ident`, pinned from below

The section above concluded that `ident` cannot be recovered from the pair and should
therefore be left alone. That was the wrong conclusion from a correct observation. `ident`
is a table like the other three, it had never been pinned from below either, and the reason
it resists the pair is not that it carries something the pair lacks — it is that it carries
something **nothing** justifies.

`Decides` below is the semantic notion §5's prose describes: two values of the same kind,
one written and one refused, so that the kind does not settle admission and an admission is
therefore evidence. Against it, `ident` is neither an over- nor an under-approximation:

* **Too generous.** `refine(string, ⊤)` is `ident` and decides nothing — `q` is checked on
  both halves and always passes. `ident` cannot see this, because it never looks at `q`.
* **Too stingy.** `object` with a required field refuses the empty map and writes a
  populated one, which is deciding by any reading, and `ident` calls it `false`.

And its `refine` row was not an oversight but an artifact: answering `true` there
unconditionally is what made the pinning lemma go through, since a refinement's admissible
set can refuse on `q` alone while the subterm decides nothing. The row existed to satisfy a
lemma, not because refinements decide.

That table could not be made exact — whether an arbitrary `q : Value → Bool` narrows
anything is not a syntactic question — and it erred on both sides at once. Nothing live
depended on it, which is why it went and `Decides` stayed. -/

/-- **What "decides its own membership" actually says.** Two values of the *same kind*, one
    written and one refused: the kind does not settle admission, so an admission is
    evidence. This is the content §5 gestures at when it says a term decides its own
    membership, stated on the denotation. -/
def Decides (t : Term) : Prop :=
  ∃ v w, ((denote t).e v).isSome = true ∧ v.kind = w.kind ∧ ((denote t).e w).isSome = false

/-- A string `literal` decides, as §5 says. -/
theorem decides_literalS : Decides (.literal .string "A") :=
  ⟨.str "A", .str "B",
   by simp [denote, denote, literalCodec, baseCodec, Codec.restrict, inL, stringCodec],
   rfl,
   by simp [denote, denote, literalCodec, baseCodec, Codec.restrict, inL, stringCodec]⟩

/-- `string` does not, as §5 also says. -/
theorem not_decides_string : ¬ Decides .string := by
  rintro ⟨v, w, hv, hk, hw⟩
  simp only [denote, denote] at hv hw
  cases v <;> cases w <;> simp_all [stringCodec, Value.kind]


theorem not_decides_refine_top : ¬ Decides (.refine .string (.closure qTop)) := by
  rintro ⟨v, w, hv, hk, hw⟩
  simp only [denote, denote] at hv hw
  cases v <;> cases w <;>
    simp_all [Codec.restrict, Pred.eval, stringCodec, qTop, Value.kind]

/-- **And too stingy.** An object with a required field refuses the empty map and writes a
    populated one — two `map`s differing in admission — while `ident` calls it `false`. -/
theorem decides_object :
    Decides (.object (.mk {"k"} (fun _ => .req .string) .refuse)) := by
  refine ⟨.map {"k"} (fun _ => .str "a"),
          .map ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)), ?_, rfl, ?_⟩
  · simp +contextual [denote, denote, bodySem, restSem, fieldSem, restSem,
          objectCodec, objectCodecCore, stringCodec,
          valPresentB, valPresentAt, fieldSem, rcOf, FieldSem.codec, carriedCodec,
          mapV, mA, objWrite, entryCodec, MapOf.at, funImage,
          Subtype.forall]
  · simp [denote, denote, bodySem, restSem, fieldSem, restSem,
          objectCodec, objectCodecCore, stringCodec,
          valPresentB, valPresentAt, fieldSem, rcOf, carriedCodec,
          mapV, mA, objWrite, Subtype.forall]


/-! ### …and the two errors are the same combinator

`refine` and `held` are not unrelated rows that happen to be wrong in opposite directions.
They are **one combinator with two adapters**: `Codec.adapt` generalises both, `held` taking
the total `some ∘ f` (`through_e_adapt`) and `refine` the partial identity `partialId q`
(`restrict_e_adapt`). The doc says as much — "the *same* combinator, weaker adapter".

`ident` gives them opposite rows. `refine` is `true` unconditionally; `held` propagates.
So the over-claim and the under-claim are the same mistake seen from two sides, and the
witnesses are duals:

* `refine(string, ⊤)` — the adapter narrows nothing, and `ident` says it decides.
* `held(string, fSplit, _)` — the adapter narrows to one string, and `ident` says it does
  not.

`Adm` has no such split. `Adm_refine_adapt` and `Adm_held_adapt` show it doing the one
thing `adapt` describes on both rows — apply the adapter, then ask the subterm — which is
why it carries `q` and `f` where `ident` carries neither. -/

/-- An adapter that sends one string to itself and everything else off `string`'s carrier.
    Total, so this is a `held` and not a `refine` — and it narrows exactly as a refinement
    would. -/
def fSplit : Value → Value := fun v => match v with | .str "A" => .str "A" | _ => .bool true

/-- **The dual gap.** `held(string, fSplit, _)` writes `"A"` and refuses `"B"` — two values
    of one kind, differing in admission — so it decides. `ident` says `false`. -/
theorem decides_held : Decides (.held .string fSplit (fun v => v)) := by
  refine ⟨.str "A", .str "B", ?_, rfl, ?_⟩
  · simp [denote, denote, Codec.through, stringCodec, fSplit]
  · simp [denote, denote, Codec.through, stringCodec, fSplit]


/-- `Adm` treats the two adapters uniformly: apply it, then ask the subterm. -/
theorem Adm_refine_adapt (t : Term) (p : Pred) (v : Value) :
    Adm (.refine t p) v = ((partialId p.eval v).elim false (Adm t)) := by
  cases hq : p.eval v <;> simp [Adm, partialId, hq]

theorem Adm_held_adapt (t : Term) (f g : Value → Value) (v : Value) :
    Adm (.held t f g) v = ((some (f v)).elim false (Adm t)) := by
  simp [Adm]

/-! ### Adapters and alternatives, and why `legacy` was in the wrong family

`held` and `refine` are `Codec.adapt` with different adapters. `legacy` is **not** an
adapter at all, and asking whether it was is what found the row above.

An adapter *composes*: `adapt`'s read is `(c.p a).bind g`, so it can only lose attributes —
`adapt_p_le`. `legacy`'s read *gains* them: `extendRead`'s `p` is the subterm's channel
falling back to `r`'s, which is a **choice**, not a composition. That is the family `union`
belongs to as well (`altCodec`, n-ary, both sides). `legacy` is the one-sided member: it reads
on two channels and writes on one.

Placing it correctly is what makes the row exact. §5 called `admA(legacy)` `⊤` because
`extendRead` widens past the subterm's set — true, and the wrong conclusion, because the
thing it widens *by* is `r`, which the term carries. The domain is
`dom(p) ∪ dom(r)`, both halves named, and `AdmA` can apply `r` for the same reason it can
apply `held`'s `f` and `custom`'s `cp`.

So `legacy` leaves the attribute hatch, and the ~~widenedRead~~ excuse is deleted rather than
witnessed: it was covering a row that did not need excusing. What survives is the fact the
excuse misread — §5's *passthrough* really is unsound, and the union is not the
passthrough. -/

/-- An adapter never widens the read domain. -/
theorem adapt_p_le {c : Codec} {f g : Value → Option Value} {a : Attr} :
    ((c.adapt f g).p a).isSome = true → (c.p a).isSome = true := by
  intro h
  simp only [Codec.adapt] at h
  cases hc : c.p a with
  | none => rw [hc] at h; simp at h
  | some _ => rfl

/-- `legacy` is the read-side alternative: the subterm's channel, falling back to `r`'s. -/
theorem legacy_p_alt (t : Term) (r : Attr → Option Value) (a : Attr) :
    (denote (.legacy t r)).p a
      = (match (denote t).p a with | some v => some v | none => r a) := rfl

/-- …so its read domain is the union of the two channels, and both are named. -/
theorem legacy_p_isSome (t : Term) (r : Attr → Option Value) (a : Attr) :
    ((denote (.legacy t r)).p a).isSome = (((denote t).p a).isSome || (r a).isSome) := by
  simp only [legacy_p_alt]
  cases (denote t).p a <;> simp

/-- Which is exactly `AdmA`'s row, so `legacy` widens the read side and is exact anyway. -/
theorem AdmA_legacy_union (t : Term) (r : Attr → Option Value) (a : Attr) :
    AdmA (.legacy t r) a = (AdmA t a || (r a).isSome) := by
  simp [AdmA]

/-- **A discharge §5 could not state.** Two sets over disjoint literals separate, because
    `℘⁺fin` has no empty inhabitant and so the two options share none. The non-emptiness
    is the *type's*, which is why every branch here ends at `S.2`.

    The terms are `refine(set(string), liftQ …)` where they were `set(literal …)`, and that
    is the whole of what the re-indexing cost this discharge: with `set` taking a base, a
    literal element is a **restriction of the set**, and `setCodec_restrict` proves the two
    write the same attribute on the nose. Same separation, one spelling further out. -/
theorem sepJV_set_literals :
    SepJV (.refine (.set .string) (.each (.members .string (.of "A" ∅))))
          (.refine (.set .string) (.each (.members .string (.of "B" ∅)))) := by
  intro v hv
  cases v
  case strSet S =>
    obtain ⟨x, hx⟩ := S.2
    simp only [Adm, Bool.and_eq_true, Pred.eval, liftQ, decide_eq_true_eq] at hv
    have hxA : x = "A" := by
      have h1 := (of_decide_eq_true hv.2) x hx
      simpa [inLs, inL] using h1
    simp only [Adm, Pred.eval, liftQ, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine Or.inr (decide_eq_false (fun hall => ?_))
    have h2 := hall x hx
    rw [hxA] at h2
    simp [inLs, inL] at h2
  -- the other two wire families are refused by the *set* row, element by element: a
  -- `string` base admits no number and no byte string, and `℘⁺fin` supplies the element
  case numSet S =>
    obtain ⟨x, hx⟩ := S.2
    simp only [Adm, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact Or.inl (fun hall => by have h := hall x hx; simp [SetBase.adm] at h)
  case binSet S =>
    obtain ⟨x, hx⟩ := S.2
    simp only [Adm, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact Or.inl (fun hall => by have h := hall x hx; simp [SetBase.adm] at h)
  all_goals simp [Adm, Pred.eval, liftQ]

/-- …and the contrast that shows what the non-emptiness is doing: the *array* pair does not
    separate, because both options admit `[]`. This is §5's empty-container argument in its
    correct scope — it is a fact about `array`, `record` and `object`, not about `set`. -/
theorem not_sepJV_array_literals :
    ¬ SepJV (.array (.literal .string "A")) (.array (.literal .string "B")) := by
  intro h
  exact absurd (h (.arr []) (by simp [Adm, allP])) (by simp [Adm, allP])

/-! ### What `set` is, structurally — and the defect that closed

Three readings were worth separating. Two were right and the third found a defect; the
defect is now fixed by the type, and these are the witnesses that it is.

**Not a `union`.** A union is a choice among *codecs*, resolved by (U); a set's elements all
go through **one** codec, so no uniqueness obligation arises. That is why `set` needs no (U)
and `union` does.

**Not `array` with a wrapper either, any more.** It was, while both were lists: the two
shared `traverse c.e vs` and differed only in how the payload list was presented. With the
sets typed there is no shared list to share — `array` traverses a `List Value`, `set` images
a `Finset` — and what survives of the old observation is that the *element* codec is the
same in both.

**And "order does not matter" is now true of the model**, where it was not. §1 types `SS` as
`℘⁺fin(String)` and the reference says the order of a set's values is not preserved and each
value is unique. Three theorems recorded that the model disagreed. They are replaced by the
three below, which say the disagreement is over: an ordering is not a distinction a `Finset`
can make, and a repeat is not an inhabitant it can hold. -/

/-- Two "orderings" of one set are the same value — there is nothing to quotient. -/
theorem set_order_irrelevant :
    (Value.strSet (.of "a" {"b"})) = (Value.strSet (.of "b" {"a"})) :=
  congrArg Value.strSet (Subtype.ext (Finset.ext fun x => by
    simp only [NEFinset.of, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e),
           fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e)⟩))

/-- …and the same attribute. -/
theorem wireSet_order_irrelevant :
    (Attr.ss (.of "a" {"b"})) = (Attr.ss (.of "b" {"a"})) :=
  congrArg Attr.ss (Subtype.ext (Finset.ext fun x => by
    simp only [NEFinset.of, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e),
           fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e)⟩))

/-- A repeat is not an inhabitant: `℘⁺fin` has no multiplicities, and neither does the
    model now. -/
theorem set_no_duplicates :
    (Value.strSet (.of "a" {"a"})) = (Value.strSet (.of "a" ∅)) :=
  congrArg Value.strSet (Subtype.ext (Finset.ext fun x => by
    simp only [NEFinset.of, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, or_false]
    exact ⟨fun h => h.elim id id, fun h => Or.inl h⟩))

/-! ### What (R) would have forced, had the type not settled it

The repair was once going to be a canonical form over lists, and (R) constrained it hard:
retraction is to the *same* value, not an agreeing one, so a codec whose `e` collapsed two
orderings would owe one attribute two readings. `e` could not normalise; it would have had
to accept exactly one representative per set and refuse the rest, with `p` normalising so
that `ker p` collapsed the orderings — §2's sentence, made true by construction.

None of that is needed. `Finset` has one representative per set *as a type*, so there is
nothing for `e` to choose between and nothing for `p` to collapse; `ker p` is equality at
`setCodec` and that is now correct rather than a defect. The constraint is recorded because
it is what rules out the alternative design, not because anything here depends on it.

The canonical form and the axiom-free order it was built on were likewise no longer on the set
path, and `f3bb956` deleted them; the `Classical.choice` hazard they existed to route around is
recorded beside `NEFinset` in `Domain.lean`. Nor, as the next section shows, on the map path: the
quotient the kernel refuses is `Finset (Name × Attr)`, and `M` does not need it. -/

/-! ### The reference, checked against the model

`docs/dynamo-datatypes.md` is the official datatype reference. Most of §1 survives it
exactly — `Numeral.WF`'s 38 digits and `-130 … 125` exponent range are the documented
bounds; binary compares unsigned; empty strings and empty binary are permitted, empty lists
and maps are permitted, empty sets are not, and the model already refuses the last.

Two things do not survive, and they are the same defect at two members.

**`SS`/`NS`/`BS`** — *"Each value within a set must be unique. The order of the values within
a set is not preserved."* Recorded above.

**`M`** — *"A map type attribute can store an **unordered** collection of name-value
pairs."* The model's `M` was a `List (Name × Attr)`, so two orderings of one map were two
attributes and a repeated key was writable, which no map has. Three theorems recorded the
disagreement; they are replaced by the three below.

This one was called sharper than the set case for two reasons, and only the first survives.
The model does *state* the intent elsewhere — `Agree` at `M` compares by key and ignores
order — so the two halves of the model disagreed with each other and not merely with the
reference. But the second reason, that maps cannot be repaired by typing, was wrong, and the
correction is the content of this section. `Finset (Name × Attr)` **is** rejected by the
kernel, exactly as `Finset Value` is, the element type being the one under declaration. What
does not follow is that `M` needs the well-formedness route. The pair need not be the
element: §1's `M` is a finite *partial function*, so the names go in a `Finset` over the
concrete type `Name` and the attributes go in a function's codomain — a strictly positive
position, which the kernel accepts:

    | m (keys : Finset Name) (f : {k // k ∈ keys} → Attr)

Unordered, unique-keyed and total-on-its-keys are now facts about the type. No canonical
order, no ~~Wire.canon~~, and nothing for `e` to choose between. -/

/-- Two "orderings" of one map's names are one name set — there is nothing to quotient. -/
theorem mapKeys_order_irrelevant : ({"a", "b"} : Finset Name) = {"b", "a"} :=
  Finset.ext fun x => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e),
           fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e)⟩

/-- …so the codec has one answer where it used to have two. Equal key sets and
    pointwise-equal entries are one attribute (`MapOf.ext`), and one attribute is one
    reading — the order-sensitivity had nowhere left to live. -/
theorem record_p_order_irrelevant
    (g : {k // k ∈ ({"a", "b"} : Finset Name)} → Attr)
    (g' : {k // k ∈ ({"b", "a"} : Finset Name)} → Attr)
    (h : ∀ k (h₁ : k ∈ ({"a", "b"} : Finset Name)) (h₂ : k ∈ ({"b", "a"} : Finset Name)),
      g ⟨k, h₁⟩ = g' ⟨k, h₂⟩) :
    (recordCodec stringCodec).p (.m {"a", "b"} g)
      = (recordCodec stringCodec).p (.m {"b", "a"} g') :=
  congrArg (fun p : MapOf Attr => (recordCodec stringCodec).p (.m p.1 p.2))
    (MapOf.ext (p := ⟨{"a", "b"}, g⟩) (q := ⟨{"b", "a"}, g'⟩) mapKeys_order_irrelevant h)

/-- A repeated key is not an inhabitant: the map that was supposed to carry `"a"` twice is
    the map that carries it once. -/
theorem mapKeys_no_duplicates : ({"a", "a"} : Finset Name) = {"a"} :=
  Finset.ext fun x => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim id id, fun h => Or.inr h⟩

end

end Calculus
