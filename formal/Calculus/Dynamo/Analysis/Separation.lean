import Calculus.Dynamo.Analysis.ExactA

variable {α : Calculus.Table}

/-!
# Derivability, separation, and what the pair does not record

`array` and `record` are builders over other constructors, not constructors. `SepJV` states
separation on the pair, in the one direction that holds. And the negative results say what the pair
does not record, with what to use instead.
-/

namespace Calculus

section
/-! ## `array` and `record` are builders

`array` is the degenerate `tuple`: an empty fixed part and a uniform spread. Both builders write
the same `list`, so `array c` and `tuple [] (some c)` are **one term**, and `arrayRow` is `rfl`.
`set` is the opposite case: a narrower *constructor* buys *exactness*. `set b` cannot be spelled
as a `refine` of anything, and indexing by the base is what makes `setAt`'s collision guard
provably dead.

`record` is the degenerate `object`: a builder over the body whose only block is the open one.
So `record c` and the object it expands to are **one term** too.

### …and `union` is a congruence for codec equivalence

`refine_top_row` carries the fact on a live pair: `refine t ⊤` and `t` have identical rows,
hence, by `Adm_exact`/`AdmA_exact`, which take no hypothesis, identical domains on both sides.
They are the same codec as far as anything observable through `e` and `p` can tell, and
`union` agrees: every option, `object` included, is admitted by *attempt*, and the row of a
`union` is the disjunction of its options' rows. So a domain-equal substitution changes no
option's admission, and a rewrite that replaces a subterm by a domain-equal one is sound inside
a `union`.

**Admission by structure is not a congruence.** A test that reads the declared names and the
literal alternatives and nothing else differs from `Adm` at a declared name pinned to no
literal. `vBoolAtA` against `tReqStr`, `{"A" ↦ true}` against `{A : req string}`, is the pair:
the value carries exactly the declared names and the slot pins no literal, so such a test
answers `true`, and the row answers `false`. So admission reads the row and not the
structure. -/

/-- A refinement by the trivially-true predicate: the same pair as the bare base. -/
def qTop : Value → Bool := fun _ => true

/-- One name, declared `req string` and pinned to no literal, so a test of the names and the
    literals asks only that the name is present. -/
def tReqStr : Term := .object (.mk {"A"} (fun _ => .req .string) none)

/-- …and a map carrying that name at a boolean, which the structure admits and the row
    refuses. -/
def vBoolAtA : Value := .map {"A"} (fun _ => .bool true)

/-- `array` **is** the degenerate `tuple`: both builders write the same `list`, so the two
    rows are one term and the equation is `rfl`. -/
theorem arrayRow (c : Term) (v : Value) : Adm α (.array c) v = Adm α (.tuple [] (some c)) v := rfl

/-- The same on the read side, and for the same reason. -/
theorem arrayRowA (c : Term) (a : Attr) : AdmA α (.array c) a = AdmA α (.tuple [] (some c)) a := rfl

/-! ### `union` and domain equality

`record c` and the object with no declared name and a rest codec are one term: `record` is a
builder over `object` with a block. So a normalization pass that replaces either by the other
changes no term, and no `union` selects differently. `array` and `tuple` are one `list` the same
way, and `arrayRow` above is that equation. -/

/-- `refine t ⊤` and `t` admit the same values at every point: the row is `Adm t v && true`,
    so the domains are equal with no hypothesis. -/
theorem refine_top_row (t : Term) : Adm α (.refine t (.closure qTop) ()) = Adm α t := by
  funext v; simp [Adm_rows, Pred.eval, qTop]

/-! ## Separation on the pair

`SepJV` and `SepJA` state separation on the rows this file proves exact. Each side is one
clause. `Adm` and `AdmA` fold the kind or member gate into their rows. An alternate reader
(`Term.legacy`) asks its own codec in each row, so it cannot add a second structural clause.

A discharger consumes disjointness of the options `select` builds, and every option, `object`
included, is admitted by attempt, which is `Adm`/`AdmA` exactly. `admitV_le_Adm` and
`admitA_le_AdmA`, below the next section, are that containment stated for every constructor. -/


/-! A dissection is a certified `union`. `AdmAny_iff` states that a union admits a value exactly
when one of its options does. -/

variable (α) in
/-- **Separation on the joint predicate, value side, in one clause.** §5 offers a choice between
    disjoint kinds and disjoint admissible sets. `Adm` carries the kind gate in its own rows,
    so disjoint kinds give disjoint admissible sets, and one clause states both. -/
def SepJV (x y : Term) : Prop := ∀ v, Adm α x v = true → Adm α y v = false

variable (α) in
/-- **…and attribute side, also one clause.** The former member disjunct described an
    alternate reader inside `Term`. The carrier split made that state unrepresentable. -/
def SepJA (x y : Term) : Prop := ∀ a, AdmA α x a = true → AdmA α y a = false

/-- A read channel that fires at `N` and nowhere else. -/
def rNum : Attr → Option Value := fun a => match a with | .n _ => some (.str "x") | _ => none

/-- An alternate reader may read outside the member of its current term. -/
theorem extendRead_reads_n :
    ((denote α .string).extendRead rNum).p (.n (.of "1")) = some (.str "x") := rfl

/-! ## What the pair does not record, and what to use instead

A predicate on values does not say how a term is *written*. `string` and `refine(string, ⊤)`
denote the same pair and have the same `Adm`, so nothing defined on the pair tells them
apart. `Decides` below is the semantic notion §5's prose describes, pinned from the pair
rather than read off the syntax. The theorem immediately below is the witness that the two
questions are different. -/

/-- **How a term is written is not a function of what it admits.** Two terms, one a
    refinement of the other, agreeing on the joint predicate at every value. -/
theorem Adm_string_eq_refine : Adm α .string = Adm α (.refine .string (.closure qTop) ()) :=
  (refine_top_row .string).symm





/-- **`SepJV` suffices for the codec-level discharge.** The joint predicate is tighter than
    the rows it replaces, so `SepJV` is a *weaker* statement — but `Adm_sound` connects it
    straight to the denotation: where `x` writes, `y` refuses. What a discharger consumes is
    disjointness of the *options* `select` builds, and every option, `object` included, is
    admitted by attempting its codec, so this is the same fact the discharger needs. -/
theorem admitV_of_sepJV {x y : Term} (h : SepJV α x y) (v : Value) (a : Attr)
    (hx : (denote α x).e v = some a) : ((denote α y).e v).isSome = false := by
  have hAx : Adm α x v = true := Adm_sound (α := α) x hx
  have hAy : Adm α y v = false := h v hAx
  cases hy : (denote α y).e v with
  | none => rfl
  | some b => exact absurd (Adm_sound y hy) (by simp [hAy])

/-- …and on the attribute side. -/
theorem admitA_of_sepJA {x y : Term} (h : SepJA α x y)
    (a : Attr) (v : Value) (hx : (denote α x).p a = some v) :
    ((denote α y).p a).isSome = false :=
  (Alg.AdmA_eq_isSome (S := dynSyn) y [] a).symm.trans (h a (AdmA_sound (α := α) x hx))

/-! ### …and it suffices for the discharger, at every constructor

Every option is admitted by attempt, `object` included, so admission **is** `Adm`/`AdmA` at
every constructor: `admitV_le_Adm`/`admitA_le_AdmA` below hold unconditionally. -/

/-- **The containment the discharger needs, at every constructor.** Admission is attempted
    encoding, whatever the term, and exactness identifies it with the row. -/
theorem admitV_le_Adm (t : Term) {v : Value}
    (h : ((denote α t).e v).isSome = true) : Adm α t v = true :=
  (Adm_exact t v).mpr h

/-- …and its twin on the readable side. -/
theorem admitA_le_AdmA (t : Term) {a : Attr}
    (h : ((denote α t).p a).isSome = true) : AdmA α t a = true :=
  (AdmA_exact t a).mpr h

/-! ### `Decides`, and why no table over the syntax decides it

`Decides` below is the semantic notion §5's prose describes: two values of the same kind,
one written and one refused, so that the kind does not settle admission and an admission is
therefore evidence.

**No table that reads the constructor is exact for `Decides`**, in either direction:

* A row that answers `true` at every `refine` is too generous. `refine(string, ⊤)` decides
  nothing, because `q` is checked on both halves and always passes (`not_decides_refine_top`).
* A row that answers `false` at every `object` is too stingy. An `object` with a required
  field refuses the empty map and writes a populated one, so it decides (`decides_object`).

Whether an arbitrary `q : Value → Bool` narrows anything is not a syntactic question, so the
notion is stated on the denotation. -/

variable (α) in
/-- **What "decides its own membership" actually says.** Two values of the *same kind*, one
    written and one refused: the kind does not settle admission, so an admission is
    evidence. This is the content §5 gestures at when it says a term decides its own
    membership, stated on the denotation. -/
def Decides (t : Term) : Prop :=
  ∃ v w, ((denote α t).e v).isSome = true ∧ v.kind = w.kind ∧ ((denote α t).e w).isSome = false

/-- A string `literal` decides, as §5 says. -/
theorem decides_literalS : Decides α (.literal .string "A") :=
  ⟨.str "A", .str "B",
   by simp [denote_rows, literalCodec, Alg.restrict_e_def, Alg.restrict_p_def, inL, prism_rows, orient_rows],
   rfl,
   by simp [denote_rows, literalCodec, Alg.restrict_e_def, Alg.restrict_p_def, inL, prism_rows, orient_rows]⟩

/-- `string` does not, as §5 also says. -/
theorem not_decides_string : ¬ Decides α .string := by
  rintro ⟨v, w, hv, hk, hw⟩
  simp only [denote_rows] at hv hw
  cases v <;> cases w <;> simp_all [Attr.kind, Member.kind, prism_rows, orient_rows]


theorem not_decides_refine_top : ¬ Decides α (.refine .string (.closure qTop) ()) := by
  rintro ⟨v, w, hv, hk, hw⟩
  simp only [denote_rows] at hv hw
  cases v <;> cases w <;>
    simp_all [Alg.restrict_e_def, Pred.eval, qTop, Attr.kind, Member.kind, prism_rows, orient_rows]

/-- **And too stingy.** An object with a required field refuses the empty map and writes a
    populated one: two `map`s differing in admission, so a row that answers `false` at every
    `object` is wrong. -/
theorem decides_object :
    Decides α (.object (.mk {"k"} (fun _ => .req .string) none)) := by
  refine ⟨.map {"k"} (fun _ => .str "a"),
          .map ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)), ?_, rfl, ?_⟩
  · simp +contextual [denote_rows, objectCodec, prism_rows, orient_rows, Alg.objAt_isSome, absentOf, rcOf, Alg.FieldSem.codec, carriedCodec, mA, entryCodec, MapOf.at]
  · -- the required name is absent: its slot refuses
    rw [Bool.eq_false_iff]
    intro h
    simp only [denote_rows, objectCodec, prism_rows, orient_rows, carriedCodec, mA,
      Option.isSome_map, Option.bind_some, Alg.objAt_isSome] at h
    have := h.1 "k" (by decide) (Finset.notMem_empty _)
    simp [absentOf, MapOf.at] at this


/-! ### …and the two errors are the same combinator

`refine` and `held` are not unrelated rows that happen to be wrong in opposite directions.
They are **one combinator with two adapters**: `Codec.adapt` generalises both, `held` taking
the total `some ∘ f` (`through_e_adapt`) and `refine` the partial identity `partialId q`
(`restrict_e_adapt`). The doc says as much — "the *same* combinator, weaker adapter".

A row that reads the combinator and not the adapter errs at one of the two, and the
witnesses are duals:

* `refine(string, ⊤)`: the adapter narrows nothing, and the term does not decide.
* `held(string, string, fSplit, _)`: the adapter narrows to one string, and the term decides
  (`decides_held`).

`Adm` has no such split. `Adm_refine_adapt` and `Adm_held_adapt` show it doing the one
thing `adapt` describes on both rows, apply the adapter and then ask the subterm, which is
why it carries `q` and `f`. The `held` row also asks the outer at the value itself. -/

/-- An adapter that sends one string to itself and everything else off `string`'s carrier.
    Total, so this is a `held` and not a `refine` — and it narrows exactly as a refinement
    would. -/
def fSplit : Value → Value := fun v => match v with | .str "A" => .str "A" | _ => .bool true

/-- The table that gives each generator the pair `fSplit`, `id`. -/
def splitTable : Table := fun _ => (fSplit, id)

/-- **The dual gap.** `held(string, string, fSplit, _)` writes `"A"` and refuses `"B"`: two values
    of one kind, differing in admission, so it decides. -/
theorem decides_held :
    Decides splitTable (.held false .string .string (.caller 0, false) []) := by
  refine ⟨.str "A", .str "B", ?_, rfl, ?_⟩
  · simp [denote_rows, Alg.TableAt.word, Alg.TableAt.letter, splitTable, Alg.Codec.through, fSplit, prism_rows, orient_rows]
  · simp [denote_rows, Alg.TableAt.word, Alg.TableAt.letter, splitTable, Alg.Codec.through, fSplit, prism_rows, orient_rows]


/-- `Adm` treats the two adapters uniformly: apply it, then ask the subterm. -/
theorem Adm_refine_adapt (t : Term) (p : Pred) (v : Value) :
    Adm α (.refine t p ()) v = ((partialId p.eval v).elim false (Adm α t)) := by
  cases hq : p.eval v <;> simp [Adm_rows, partialId, hq]

theorem Adm_held_adapt (t P : Term) (k₀ : DynGen × Bool) (k : Word) (v : Value) :
    Adm α (.held false t P k₀ k) v =
      (((some ((α.word (k₀ :: k)).1 v)).elim false (Adm α t)) && Adm α P v) := by
  simp [Adm_rows]

/-! ### Adapters and alternatives, and why `alternate reader` is not an adapter

`held` and `refine` are `Codec.adapt` with different adapters. `alternate reader` is **not** an
adapter at all.

An adapter *composes*: `adapt`'s read is `(c.p a).bind g`, so it can only lose attributes
(`adapt_p_le`). `alternate reader`'s read *gains* them: `extendRead`'s `p` is the subterm's
channel falling back to `r`'s, which is a **choice**, not a composition. That is the family
`union` belongs to as well (`altCodec`, n-ary, both sides). `alternate reader` is the one-sided
member: it reads on two channels and writes on one.

The read domain of `extendRead c r` is `dom(p)` and the part of `dom(r)` whose answer `c`
writes. A passthrough that bounds it by the subterm's read domain is unsound, not coarse:
`extendRead (literal "A") r`, with `r` reading `⟨N, "1"⟩` to `"A"`, reads an attribute that the
literal refuses. So the `legacy` row of `AdmA` asks its own codec. -/

/-- An adapter never widens the read domain. -/
theorem adapt_p_le {c : Codec} {f g : Value → Option Value} {a : Attr} :
    ((c.adapt f g).p a).isSome = true → (c.p a).isSome = true := by
  intro h
  simp only [Alg.Codec.adapt, Alg.Codec.ofEP_p] at h
  cases hc : c.p a with
  | none => rw [hc] at h; simp at h
  | some _ => rfl

/-- **A discharge §5 could not state.** Two sets over disjoint literals separate, because
    `℘⁺fin` has no empty inhabitant and so the two options share none. The non-emptiness
    is the *type's*, which is why every branch here starts at `S.2`.

    The literal sits at the element: `set(literal string "A")`. -/
theorem sepJV_set_literals :
    SepJV α (.set (.literal .string "A")) (.set (.literal .string "B")) := by
  -- a string literal writes one string and no other value
  have hlit : ∀ (c : String) (w : Value), ((denote α (.literal .string c)).e w).isSome = true →
      w = .str c := fun c w h => by
    exact inL_iff.mp ((Adm_exact (α := α) (.literal .string c) w).mpr h)
  intro v hv
  cases v
  case ss S =>
    obtain ⟨x, hx⟩ := S.2
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hv
    have hA := hlit "A" _ (setAt_elem (c := denote α (.literal .string "A")) ha x hx)
    cases hb : Adm α (.set (.literal .string "B")) (.strSet S) with
    | false => rfl
    | true =>
      obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.mp hb
      have hB := hlit "B" _ (setAt_elem (c := denote α (.literal .string "B")) hb' x hx)
      exact absurd (hA.symm.trans hB) (by simp)
  -- the other two wire families are refused element by element, and `℘⁺fin` supplies the
  -- element
  case ns S =>
    obtain ⟨x, hx⟩ := S.2
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hv
    exact absurd (hlit "A" _ (setAt_elem (c := denote α (.literal .string "A")) ha x hx))
      (by simp)
  case bs S =>
    obtain ⟨x, hx⟩ := S.2
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hv
    exact absurd (hlit "A" _ (setAt_elem (c := denote α (.literal .string "A")) ha x hx))
      (by simp)
  all_goals simp [Adm_rows, setCodec, orient_rows] at hv

/-- …and the contrast that shows what the non-emptiness is doing: the *array* pair does not
    separate, because both options admit `[]`. This is §5's empty-container argument in its
    correct scope — it is a fact about `array`, `record` and `object`, not about `set`. -/
theorem not_sepJV_array_literals :
    ¬ SepJV α (.array (.literal .string "A")) (.array (.literal .string "B")) := by
  intro h
  exact absurd (h (.arr []) (Adm_array_nil _)) (by rw [Adm_array_nil]; exact fun hc => nomatch hc)

/-! ### What `set` is, structurally

Three readings are worth separating. The third is a fact about the type, and the theorems
below are its witnesses.

**Not a `union`.** A union is a choice among *codecs*, lawful by pairwise compatibility; a
set's elements all go through **one** codec, so no obligation between codecs arises. That is
why `set` needs no compatibility premise and `union` does.

**Not `array` with a wrapper.** `array` traverses a `List Value`, and `set` images a
`Finset`. The two share the *element* codec and nothing else.

**"Order does not matter" is true of the model.** §1 types `SS` as `℘⁺fin(String)`, and the
reference says the order of a set's values is not preserved and each value is unique. The
three theorems below state it: an ordering is not a distinction a `Finset` can make, and a
repeat is not an inhabitant it can hold. -/

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
    model. -/
theorem set_no_duplicates :
    (Value.strSet (.of "a" {"a"})) = (Value.strSet (.of "a" ∅)) :=
  congrArg Value.strSet (Subtype.ext (Finset.ext fun x => by
    simp only [NEFinset.of, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false]
    exact ⟨fun h => h.elim id id, fun h => Or.inl h⟩))

/-! ### What (R) forces on a list carrier for a set

(R) makes `e` injective, so a list-carried set codec cannot normalise: two spellings of one set
that write one attribute owe that attribute two readings. (R) does not rule out a canonical form.
A list carrier with a decidable total order on `Value` is lawful when `e` accepts only the
canonical spelling and refuses the rest, and `p` returns the canonical spelling. The cost is the
refusal: every set codec refuses a non-canonical spelling, so the carrier holds values that no set
codec writes.

`Finset` has one representative per set *as a type*, so there is nothing for `e` to refuse and
nothing for `p` to choose, and `ker p` is equality at `setCodec`. The kernel refuses the generic
carrier (a nested `Finset`, `Multiset` or `Quot` of the datatype being declared), which is why the
three concrete set carriers stay.

No canonical form and no order is on the set path or on the map path. The quotient the kernel
refuses is `Finset (Name × Attr)`, and `M` does not need it, as the next section shows. -/

/-! ### The reference, checked against the model

`docs/dynamo-datatypes.md` is the official datatype reference. Most of §1 survives it
exactly — `Numeral.WF`'s 38 digits and `-130 … 125` exponent range are the documented
bounds; binary compares unsigned; empty strings and empty binary are permitted, empty lists
and maps are permitted, empty sets are not, and the model already refuses the last.

Two statements of the reference are about order and uniqueness, and the type carries both.

**`SS`/`NS`/`BS`**: *"Each value within a set must be unique. The order of the values within
a set is not preserved."* The section above states it.

**`M`**: *"A map type attribute can store an **unordered** collection of name-value
pairs."* The three theorems below state it.

**A map is repaired by typing.** `Finset (Name × Attr)` is rejected by the kernel, exactly as
`Finset Value` is, because the element type is the one under declaration. That does not send
`M` to a well-formedness premise. The pair need not be the element: §1's `M` is a finite
*partial function*, so the names go in a `Finset` over the concrete type `Name` and the
attributes go in a function's codomain, a strictly positive position that the kernel accepts:

    | m (keys : Finset Name) (f : {k // k ∈ keys} → Attr)

Unordered, unique-keyed and total-on-its-keys are facts about the type. No canonical order
exists, and `e` has nothing to choose between. -/

/-- Two "orderings" of one map's names are one name set — there is nothing to quotient. -/
theorem mapKeys_order_irrelevant : ({"a", "b"} : Finset Name) = {"b", "a"} :=
  Finset.ext fun x => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e),
           fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e)⟩

/-- …so the codec has one answer. Equal key sets and pointwise-equal entries are one
    attribute (`MapOf.ext`), and one attribute is one reading, so no reading depends on an
    order. -/
theorem record_p_order_irrelevant
    (g : {k // k ∈ ({"a", "b"} : Finset Name)} → Attr)
    (g' : {k // k ∈ ({"b", "a"} : Finset Name)} → Attr)
    (h : ∀ k (h₁ : k ∈ ({"a", "b"} : Finset Name)) (h₂ : k ∈ ({"b", "a"} : Finset Name)),
      g ⟨k, h₁⟩ = g' ⟨k, h₂⟩) :
    (recordCodec (baseCodec .string)).p (.m {"a", "b"} g)
      = (recordCodec (baseCodec .string)).p (.m {"b", "a"} g') :=
  congrArg (fun p : MapOf Attr => (recordCodec (baseCodec .string)).p (.m p.1 p.2))
    (MapOf.ext (p := ⟨{"a", "b"}, g⟩) (q := ⟨{"b", "a"}, g'⟩) mapKeys_order_irrelevant h)

/-- A repeated key is not an inhabitant: the map that was supposed to carry `"a"` twice is
    the map that carries it once. -/
theorem mapKeys_no_duplicates : ({"a", "a"} : Finset Name) = {"a"} :=
  Finset.ext fun x => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim id id, fun h => Or.inr h⟩

end



end Calculus
