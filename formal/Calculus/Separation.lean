import Calculus.ExactA

/-!
# Derivability, separation, and what the pair does not record

Two of the twenty-one constructors are derivable from the others. `SepJV` states separation
on the pair, in the one direction that holds. And the negative results say what the pair
does not record, with what to use instead.
-/

namespace Calculus

noncomputable section
/-! ## `array` is derivable, and it is kept

`array` is the degenerate `tuple` — empty fixed part, uniform tail — and its row agrees with
the general form *pointwise*, on both sides, so nothing in the analysis depends on it
existing.

It is kept anyway, and the reason is the shape of the row rather than the size of the
language. `array`'s row is `allP`, one fold; the `tuple` it expands to is `alignP`, which
carries a length discipline that at `([], some c)` can never fire. So the narrow builder buys
a row a reader can check by eye, and that is the **opposite** trade from `set`, where a
narrower *constructor* bought *exactness*: `set b` cannot be spelled as a `refine` of
anything, and indexing by the base is what made `encSet`'s collision guard provably dead.
Convenience here, necessity there.

`record` used to stand beside `array` here, as the degenerate `object`. It does not any more:
it is a builder over the body whose only block is the open one, so `record c` and the object
it expanded to are **one term**, and the pair that compared them has nothing to compare.

### …and `union` is a congruence for codec equivalence

`union_congruent` carries the fact on a live pair: `refine t ⊤` and `t` have identical rows on
both sides, hence — by `Adm_exact`/`AdmA_exact`, which take no hypothesis — identical domains
on both sides. They are the same codec as far as anything observable through `e` and `p` can
tell, and `union` no longer disagrees: every option, `object` included, is admitted by
*attempt*, which runs `Adm` directly. `admitOptV`/`admitOptA` are `Adm`/`AdmA` at every
constructor now, so a domain-equal substitution changes no option's admission, and a rewrite
that replaces a subterm by a domain-equal one is sound inside a `union`.

This used to fail at one constructor: an object option was admitted *by structure* —
`keysOk` and the literal alternatives, and nothing else — which is coarser than `Adm` at a
declared name pinned to no literal. `{"A" ↦ true}` against `{A : req string}` is the pair
that recorded the gap: the structural test answered `true` and the row answered `false`, with
equal domains behind both. That gap closed when the option stopped being decided
syntactically. -/

/-- A refinement by the trivially-true predicate: the same pair as the bare base. -/
def qTop : Value → Bool := fun _ => true

/-- One name, declared `req string` and pinned to no literal — so the structural test asks
    only that the name is present. -/
def tReqStr : Term := .object (.mk {"A"} (fun _ => .req .string) none)

/-- …and a map carrying that name at a boolean, which the structure admits and the row
    refuses. -/
def vBoolAtA : Value := .map {"A"} (fun _ => .bool true)

/-- `array` **is** the degenerate `tuple`, and now on the nose: both builders write the
    same `list`, so the two rows are one term and the equation is `rfl`. It was an
    induction over the value's list while `allP` and `alignP` were two different rows. -/
theorem arrayRow (c : Term) (v : Value) : Adm (.array c) v = Adm (.tuple [] (some c)) v := rfl

/-- The same on the read side, and for the same reason. -/
theorem arrayRowA (c : Term) (a : Attr) : AdmA (.array c) a = AdmA (.tuple [] (some c)) a := rfl

/-! ### `union` and domain equality

`record c` and the object with no declared name and a rest codec used to be two spellings of
one codec with two structural admissions, so a normalization pass that replaced either by the
other used to change what a `union` selected. They are one term now: `record` is a builder
over `object` with a block, and the pair that recorded the difference has nothing left to
compare. `array` and `tuple` merged into `list` the same way, and `arrayRow` above is that
merge on the nose. -/

/-- `refine t ⊤` and `t` admit the same values at every point: the row is `Adm t v && true`,
    so the domains are equal with no hypothesis. -/
theorem refine_top_row (t : Term) : Adm (.refine t (.closure qTop)) = Adm t := by
  funext v; simp [Adm, Pred.eval, qTop]

/-- **`union` is a congruence for domain equality.** `refine t ⊤` and `t` admit the same
    values at every point (`refine_top_row`), and every option — `object` included — is now
    admitted by *attempt*, which runs `Adm` directly: `admitOptV` is `Adm` at every
    constructor, not only at a `refine`. So the two options agree at every value, and a
    rewrite that replaces a subterm by a domain-equal one is sound inside a `union`.

    **This used to fail, and the witness recorded why.** An object option was admitted by
    *structure* — `keysOk` and the literal alternatives, nothing else — which is coarser than
    `Adm` at a declared name pinned to no literal. `{"A" ↦ true}` against `{A : req string}`
    is the pair: the structural test answered `true`, the row answered `false`, and the
    domains were equal behind both. That gap closed when the option stopped being decided
    syntactically. -/
theorem union_congruent (t : Term) (v : Value) :
    admitOptV (specOf t, Adm t) v
      = admitOptV (specOf (.refine t (.closure qTop)), Adm (.refine t (.closure qTop))) v := by
  show Adm t v = Adm (.refine t (.closure qTop)) v
  rw [refine_top_row]

/-! ## Separation on the pair

`SepJV` and `SepJA` state separation on the rows this file proves exact. Each side is one
clause. `Adm` and `AdmA` fold the kind or member gate into their rows. An alternate reader
(`Codec.extendRead`) is outside `Term`, so an alternate reader cannot add a second structural clause.

A discharger consumes disjointness of the options `select` builds, and every option — `object`
included — is now admitted by attempt, which is `Adm`/`AdmA` exactly. `admitV_le_Adm` and
`admitA_le_AdmA`, below the next section, are that containment stated for every constructor. -/


/-! ~~selTagV_mem~~ and ~~selTagA_mem~~ went with the tag-filtered sum. They said that the option
the filter lands on is one of the options; a dissection is a certified `union` now, and
`selOptV_mem_admitOpt` is where that fact is read off. -/

/-- **Separation on the joint predicate, value side — one clause.** §5's ~~SepV~~ offers a
    choice between disjoint kinds and disjoint admissible sets; `Adm` carries the kind gate
    in its own rows, so the first disjunct is subsumed (~~Adm_kind~~) and the definition
    collapses. -/
def SepJV (x y : Term) : Prop := ∀ v, Adm x v = true → Adm y v = false

/-- **…and attribute side, also one clause.** The former member disjunct described an
    alternate reader inside `Term`. The carrier split made that state unrepresentable. -/
def SepJA (x y : Term) : Prop := ∀ a, AdmA x a = true → AdmA y a = false

/-- A read channel that fires at `N` and nowhere else. -/
def rNum : Attr → Option Value := fun a => match a with | .n _ => some (.str "x") | _ => none

/-- An alternate reader may read outside the member of its current term. -/
theorem extendRead_reads_n :
    ((denote .string).extendRead rNum).p (.n (.of "1")) = some (.str "x") := rfl

/-! ## What the pair does not record, and what to use instead

A predicate on values does not say how a term is *written*. `string` and `refine(string, ⊤)`
denote the same pair and have the same `Adm`, so nothing defined on the pair tells them
apart. The retired table that answered this read the constructor instead, which is why
nothing consumed it. `Decides` below is the semantic notion §5's prose was reaching for,
pinned from the pair rather than read off the syntax. The witness that the two
questions are different is the one theorem kept from that table's section, immediately
below. -/

/-- **How a term is written is not a function of what it admits.** Two terms, one a
    refinement of the other, agreeing on the joint predicate at every value. -/
theorem Adm_string_eq_refine : Adm .string = Adm (.refine .string (.closure qTop)) :=
  (refine_top_row .string).symm





/-- **`SepJV` suffices for the codec-level discharge.** The joint predicate is tighter than
    the rows it replaces, so `SepJV` is a *weaker* statement — but `Adm_sound` connects it
    straight to the denotation: where `x` writes, `y` refuses. What a discharger consumes is
    disjointness of the *options* `select` builds, and every option — `object` included — is
    now admitted by attempting its codec, so this is the same fact the discharger needs. -/
theorem admitV_of_sepJV {x y : Term} (h : SepJV x y) (v : Value) (a : Attr)
    (hx : (denote x).e v = some a) : ((denote y).e v).isSome = false := by
  have hAx : Adm x v = true := Adm_sound x hx
  have hAy : Adm y v = false := h v hAx
  cases hy : (denote y).e v with
  | none => rfl
  | some b => exact absurd (Adm_sound y hy) (by simp [hAy])

/-- …and on the attribute side. -/
theorem admitA_of_sepJA {x y : Term} (h : SepJA x y)
    (a : Attr) (v : Value) (hx : (denote x).p a = some v) :
    ((denote y).p a).isSome = false := by
  have hAx : AdmA x a = true := AdmA_sound x hx
  have hAy : AdmA y a = false := h a hAx
  cases hy : (denote y).p a with
  | none => rfl
  | some w => exact absurd (AdmA_sound y hy) (by simp [hAy])

/-! ### …and it now suffices for the discharger, at every constructor

This section used to record a gap: `admitV_of_sepJV` is a claim about the **codec** — where
`x`'s `e` writes, `y`'s `e` refuses — and a discharger is a claim about the **options `select`
builds**, and at an `object` those used not to be the same test. `admitOptV` matched the
asymmetry: an object option was admitted by `keysOk`, which reads which names a map carries
and never what they hold, so `Adm` was strictly *tighter* than `OptionSem.admitV` there, and
disjointness of a tighter predicate did not imply disjointness of admission. The witness was
two objects with the same declared name and different field terms — `SepJV`/`SepJA` separated
the pair, and `select` still confused their options, so the discharger restated on the joint
predicate was false.

Every option is admitted by attempt now, `object` included, so `admitOptV`/`admitOptA` **are**
`Adm`/`AdmA` at every constructor and the gap above is gone: `admitV_le_Adm`/`admitA_le_AdmA`
below hold unconditionally, not only off an `object`. -/

/-- **The containment the discharger needs, at every constructor.** Admission is attempted
    encoding now, whatever the term, and exactness identifies it with the row. -/
theorem admitV_le_Adm (t : Term) {v : Value}
    (h : (optionSemOf (denote t) (specOf t)).admitV v = true) : Adm t v = true :=
  (Adm_exact t v).mpr h

/-- …and its twin on the readable side. -/
theorem admitA_le_AdmA (t : Term) {a : Attr}
    (h : (optionSemOf (denote t) (specOf t)).admitA a = true) : AdmA t a = true :=
  (AdmA_exact t a).mpr h

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
    Decides (.object (.mk {"k"} (fun _ => .req .string) none)) := by
  refine ⟨.map {"k"} (fun _ => .str "a"),
          .map ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)), ?_, rfl, ?_⟩
  · simp +contextual [denote, denote, bodySem, wildSem, fieldSem,
          objectCodec, objectCodecCore, stringCodec,
          valPresentB, valPresentAt, fieldSem, rcOf, FieldSem.codec, carriedCodec,
          mapV, mA, objWrite, entryCodec, MapOf.at, funImage,
          Subtype.forall]
  · simp [denote, denote, bodySem, wildSem, fieldSem,
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
* `held(string, string, fSplit, _)` — the adapter narrows to one string, and `ident` says it does
  not.

`Adm` has no such split. `Adm_refine_adapt` and `Adm_held_adapt` show it doing the one
thing `adapt` describes on both rows — apply the adapter, then ask the subterm — which is
why it carries `q` and `f` where `ident` carries neither. The `held` row also asks the
caller-side term at the value itself. -/

/-- An adapter that sends one string to itself and everything else off `string`'s carrier.
    Total, so this is a `held` and not a `refine` — and it narrows exactly as a refinement
    would. -/
def fSplit : Value → Value := fun v => match v with | .str "A" => .str "A" | _ => .bool true

/-- **The dual gap.** `held(string, string, fSplit, _)` writes `"A"` and refuses `"B"` — two values
    of one kind, differing in admission — so it decides. `ident` says `false`. -/
theorem decides_held : Decides (.held .string .string fSplit (fun v => v)) := by
  refine ⟨.str "A", .str "B", ?_, rfl, ?_⟩
  · simp [denote, denote, Codec.through, Codec.restrict, stringCodec, fSplit]
  · simp [denote, denote, Codec.through, Codec.restrict, stringCodec, fSplit]


/-- `Adm` treats the two adapters uniformly: apply it, then ask the subterm. -/
theorem Adm_refine_adapt (t : Term) (p : Pred) (v : Value) :
    Adm (.refine t p) v = ((partialId p.eval v).elim false (Adm t)) := by
  cases hq : p.eval v <;> simp [Adm, partialId, hq]

theorem Adm_held_adapt (t P : Term) (f g : Value → Value) (v : Value) :
    Adm (.held t P f g) v = (((some (f v)).elim false (Adm t)) && Adm P v) := by
  simp [Adm]

/-! ### Adapters and alternatives, and why `alternate reader` was in the wrong family

`held` and `refine` are `Codec.adapt` with different adapters. `alternate reader` is **not** an
adapter at all, and asking whether it was is what found the row above.

An adapter *composes*: `adapt`'s read is `(c.p a).bind g`, so it can only lose attributes —
`adapt_p_le`. `alternate reader`'s read *gains* them: `extendRead`'s `p` is the subterm's channel
falling back to `r`'s, which is a **choice**, not a composition. That is the family `union`
belongs to as well (`altCodec`, n-ary, both sides). `alternate reader` is the one-sided member: it reads
on two channels and writes on one.

Placing it correctly is what makes the row exact. §5 called `admA(alternate reader)` `⊤` because
`extendRead` widens past the subterm's set — true, and the wrong conclusion, because the
thing it widens *by* is `r`, which the term carries. The domain is
`dom(p) ∪ dom(r)`, both halves named, and `AdmA` can apply `r` for the same reason it can
apply `held`'s `f`.

So `alternate reader` leaves the attribute hatch, and the ~~widenedRead~~ excuse is deleted rather than
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
  exact absurd (h (.arr []) (Adm_array_nil _)) (by rw [Adm_array_nil]; exact fun hc => nomatch hc)

/-! ### What `set` is, structurally — and the defect that closed

Three readings were worth separating. Two were right and the third found a defect; the
defect is now fixed by the type, and these are the witnesses that it is.

**Not a `union`.** A union is a choice among *codecs*, lawful by pairwise compatibility; a
set's elements all go through **one** codec, so no obligation between codecs arises. That is
why `set` needs no compatibility premise and `union` does.

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
