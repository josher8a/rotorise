import Calculus.Soundness

/-!
# §5 — the discharges of (U) that no phase of `Orth` reaches

What is left here after the four tables went: the discharges whose premise no syntactic
certificate can supply, the refutations that bound them, and the handful of utilities both
need.

**The four tables are gone.** The per-aspect kind, decides-its-own-membership and
admissible-set recursions were §5's
approximations, transcribed here clause for clause while the section stated them. The
section states its discharger on option admission and occupancy now, `ExactV.lean` and
`ExactA.lean` prove
`Adm`/`AdmA` exact at every constructor, and `Orthogonality.lean` decides the pairs a
declaration can decide. A transcription of an analysis nothing states and nothing consumes
is a description with nothing keeping it honest, so it went.

**The per-aspect separation layer went before them**, at `f5fc4a6`: ~~SepV~~, ~~SepA~~,
their footprint definitions, the discharger stated on them, and the hand discharges phrased
in that vocabulary. What that layer proved by hand in phases *slot* and *alternatives*,
`Orth` reaches by `decide`.

So the discharges that remain are the ones no phase reaches: an arbitrary `q` inside a
`refine`, a union of numeric literals at a base whose `DecidableEq` is axiomatized,
`opaque`, whose (U) is a theorem one level below the term language, and
`uAtAct_array_literals`, which holds where `UAtCan` is outright false.

§5's (D) is not among them, and `not_uAtCan_literal_held` is why: held sets are sets of
values, (U)'s readable side quantifies over attributes, and `held`'s adapter relabels
between them. Two options can hold disjoint sets and read one attribute. (D) is a
well-formedness condition on the `T` index and lives there — `DIncomp`, a premise of
`Typed.union` (`Typing.lean`). `DDisj` below is the *stronger* reading §5 considered and
withdrew, kept only to be refuted.

The two counterexamples that repaired §5's discharger are at the foot of the file. §5 keeps
both, and
they are the machine-checked half of a correction the document has already made.
-/

namespace Calculus

/-! ## Two utilities the discharges below need

    `allTags` pools a `discriminatedUnion`'s tags, and `refineReads` is `refine`'s
    read-side test: decode with the base, then ask `q` of the result. Both were rows of the
    retired tables before they were anything else, and both survive because the discharges
    at the foot of this file use them. -/

/-- The tags a `(dunion)`'s options answer to, pooled. Spelled out rather than a
    `flatMap` so the membership lemma is one induction. -/
def allTags (d : Name) : List Term → Finset String
  | [] => ∅
  | t :: ts => tagsOf d t ∪ allTags d ts

theorem mem_allTags {d : Name} {ts : List Term} {t tag} (ht : t ∈ ts)
    (htag : tag ∈ tagsOf d t) : tag ∈ allTags d ts := by
  induction ts with
  | nil => exact absurd ht (by simp)
  | cons t₀ ts ih =>
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact Finset.mem_union.mpr (Or.inl htag)
    · exact Finset.mem_union.mpr (Or.inr (ih ht'))



/-- **`refine`'s read-side gate**: decode with the base, then apply `q` to what comes out.

    The row this replaces was `admA (.refine t q) = admA t` — the predicate dropped — and
    the reason on record was that `q` tests the value a read *produces*, so no *syntactic*
    set of attributes bounds it. The premise is true and the conclusion does not follow, in
    exactly the way `number`'s and `opaq`'s `⊤`s did not follow: a row is not confined to
    syntax. It may call the denotation, and the denotation is what produces the value `q`
    tests. `(denote t).p a` is that value, or `none`; the gate is `q` of it.

    `AdmA`'s `refine` row is this function, which is why the row survived the retirement of
    the per-aspect tables it was first written for. -/
noncomputable def refineReads (t : Term) (q : Value → Bool) (a : Attr) : Bool :=
  match (denote t).p a with
  | some v => q v
  | none => false

/-- The gate, unfolded at a successful read. -/
theorem refineReads_some {t : Term} {q : Value → Bool} {a : Attr} {v : Value}
    (h : (denote t).p a = some v) : refineReads t q a = q v := by
  simp [refineReads, h]

/-- …and at a failed one. -/
theorem refineReads_none {t : Term} {q : Value → Bool} {a : Attr}
    (h : (denote t).p a = none) : refineReads t q a = false := by
  simp [refineReads, h]


/-! ## Admission is guarded -/


/-- Any option's attribute admission is member-guarded: with a lawful pair and a
    named member, an admitted attribute carries that member — §5's read-side (W),
    doing (D)'s job through the member index. -/
theorem admitA_member (t : Term) {μ a}
    (hμ : μSyn t = some μ) (hlaw : Lawful (denote t))
    (h : (optionSemOf (denote t) (specOf t)).admitA a = true) :
    a.member = μ := by
  cases hs : specOf t with
  | none =>
    rw [hs] at h
    replace h : ((denote t).p a).isSome = true := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    refine hlaw.reads ?_ hv
    rw [denote_μ]
    exact hμ
  | some spec =>
    rw [hs] at h
    cases t
    case object body =>
      replace hμ : some Member.M = some μ := hμ
      cases hμ
      cases a <;> first
        | rfl
        | exact nomatch h
    all_goals exact nomatch hs

/-! ## Options admit their own canonical pairs -/

/-- Only `optional` denotes to `opt`, which is what the value-side guard needs of a
    non-`optional` field. Stated where every argument is a variable — at the use site
    the field is `ff k`, and eliminating a function application in place is more
    trouble than naming the fact. -/
theorem fieldSem_ne_opt {fd : Field}
    (h : (match fd with | Field.optional _ => false | _ => true) = true) :
    ∀ c, fieldSem fd ≠ FieldSem.opt c := by
  cases fd <;> simp_all [fieldSem]

/-- Name admission from names alone: everything present is declared, everything
    required is present.

    Two hypotheses in, `keysOk` out — literally. `keysOk` is now a pair of quantifiers
    over the declared names, so this is `⟨hsub, hreq⟩` where the row form needed a
    `List.any` witness built by hand and a `List.all` over the mapped row. -/
theorem keysOk_of_names {fields : Finset Name} {ff : {k // k ∈ fields} → Field}
    {keys : Finset Name}
    (hsub : ∀ k ∈ keys, k ∈ fields)
    (hreq : ∀ k : {k // k ∈ fields},
      (match ff k with | Field.optional _ => false | _ => true) = true → k.1 ∈ keys) :
    keysOk ⟨fields, fun k => match ff k with | Field.optional _ => false | _ => true⟩
      keys = true := by
  simp only [keysOk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hsub, hreq⟩

/-- Object-encode under a closed rest policy stamps name admission: every written name
    is declared and every non-`opt` name is written.

    **One statement where there were two.** The list representation had a value row and
    an attribute row, and the second half of this lemma was the first transported along
    `traverse_fst`. `M`'s payload is a key set with a function on it, and encoding does
    not touch the key set — so the value side's admission *is* the attribute side's, and
    there is nothing to transport. -/
theorem keysOk_of_encode {fields : Finset Name} {ff : {k // k ∈ fields} → Field}
    {keys : Finset Name}
    {f : {k // k ∈ keys} → Value} {g : {k // k ∈ keys} → Attr}
    (hval : valPresentB ⟨fields, fun k => fieldSem (ff k)⟩ keys = true)
    (hfi : funImage (fun k : {k // k ∈ keys} =>
        (entryCodec ⟨fields, fun k => fieldSem (ff k)⟩ none k.1).bind
          (fun c => c.e (f k))) = some g) :
    keysOk ⟨fields, fun k => match ff k with | Field.optional _ => false | _ => true⟩
      keys = true := by
  refine keysOk_of_names (fun k hk => ?_) (fun k hb => ?_)
  · -- a name the entry function is defined at is declared: `rc?` is `none`, so
    -- `entryCodec` succeeds only through the field table
    by_contra hnk
    have hw := funImage_some hfi ⟨k, hk⟩
    rw [show entryCodec (⟨fields, fun k => fieldSem (ff k)⟩ : MapOf FieldSem) none k
        = none from by simp only [entryCodec, MapOf.at, dif_neg hnk]] at hw
    exact nomatch hw
  · exact valPresentB_spec hval (MapOf.at_of_mem (m := ⟨fields, _⟩) k)
      (fieldSem_ne_opt hb)

/-- A closed option admits its own canonical pairs, on both sides. An *open* object —
    a rest codec — is excluded, as §5 demands: an undeclared name disqualifies the
    option even where its rest codec would hold it. -/
theorem optionSem_self_admit (t : Term)
    (hcl : t.isOpenObject = false)
    (hlaw : Lawful (denote t)) {v a}
    (he : (denote t).e v = some a) :
    (optionSemOf (denote t) (specOf t)).admitV v = true ∧
    (optionSemOf (denote t) (specOf t)).admitA a = true := by
  cases hs : specOf t with
  | none =>
    constructor
    · show ((denote t).e v).isSome = true
      rw [he]; rfl
    · show ((denote t).p a).isSome = true
      rw [hlaw.retract he]; rfl
  | some spec =>
    cases t
    case object body =>
      cases body with | mk fields ff rest =>
      replace hs : some (⟨fields, fun k =>
        match ff k with | Field.optional _ => false | _ => true⟩ : MapOf Bool) =
        some spec := hs
      cases hs
      have hrc : rcOf (restSem rest) = none := by
        cases rest with
        | drop => rfl
        | refuse => rfl
        | codec tr =>
          exact absurd rfl
            (Term.isOpenObject_eq_false.mp hcl (.mk fields ff (.codec tr)) tr rfl)
      replace he : (objectCodecCore
          ⟨fields, fun k => fieldSem (ff k)⟩
          (rcOf (restSem rest))
          (keepB (restSem rest)
            ⟨fields, fun k => fieldSem (ff k)⟩)).e v =
        some a := he
      obtain ⟨keys, fv, g, rfl, rfl, hval, hfi⟩ := objectCodecCore_e_inv he
      rw [hrc] at hfi
      -- both halves are the same `keysOk`, at the key set the two payloads share
      exact ⟨keysOk_of_encode hval hfi, keysOk_of_encode hval hfi⟩
    all_goals exact nomatch hs



/-! ## The discharger -/

/-- `Pairwise`, upgraded with membership. -/
theorem pairwise_imp_mem {α : Type} {R S : α → α → Prop} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, R x y → S x y) → List.Pairwise R l →
      List.Pairwise S l
  | [], _, _ => .nil
  | a :: l, h, hp => by
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
      refine List.Pairwise.cons (fun y hy =>
          h a (List.mem_cons_self) y (List.mem_cons_of_mem a hy) (hhead y hy)) ?_
      exact pairwise_imp_mem
        (fun x hx y hy => h x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy))
        htail

/-! ### A term that admits nothing, and is derivable

    Disjointness of admissible sets is not on its own a discharge, and the reason is a term
    whose set is *empty*: it is disjoint from everything, including from itself, so it would
    separate from options the discharger refuses. `discriminatedUnion(d)` with no options is
    that term,
    and `(dunion)`'s premises are quantified over the option list, so it is derivable. -/


/-- And it is derivable — `(dunion)`'s premises are quantified over the key set, so the empty
    table satisfies both vacuously and the held set is `False`, which is what a variant table
    with no variants holds. -/
theorem typed_dunion_nil (d : Name) :
    Typed (.dunion d ⟨∅, fun k => nomatch k.2⟩)
      (HVariants ⟨∅, fun k => nomatch k.2⟩ (fun k => nomatch k.2)) (some .M) :=
  .dunion (fun k => nomatch k.2) (fun k => nomatch k.2)


/-- **The pair reading of the same fact**, and it is not superseded: it discharges the whole
    `UAtCan` for an `n`-ary family in one step, where the retired per-aspect route separated a
    pair at a time.
    Two refinements of one base read an attribute to the **same** value, so at most one
    predicate accepts it, and the readable side separates for the same reason the writable
    side does.

    The condition is *relational* — it is about options sharing a base, not about any one
    option's admissible set — which is why it is a discharger of its own as well as a row.
    `uniqueAdmission_of_disjoint` takes the two families as arbitrary predicates, so nothing
    here has to be syntactic: the attribute family is `∃ v, base.p a = some v ∧ q v`, which
    is exactly what `refineReads` computes, and disjointness is the base reading `a` to one
    value. -/
theorem uAtCan_of_refine_disjoint {base : Term} {ps : List Pred}
    (hlaw : LawfulCore (denote base))
    (hdisj : List.Pairwise (fun p p' => ∀ v, p.eval v = true → p'.eval v = false) ps) :
    UAtCan (ps.map (fun p => Term.refine base p)) := by
  show UniqueAdmission (semsOf (ps.map (fun p => Term.refine base p)))
  refine uniqueAdmission_of_disjoint
    (SVs := ps.map (fun p v => p.eval v = true))
    (SAs := ps.map (fun p a => ∃ v, (denote base).p a = some v ∧ p.eval v = true))
    ?_ ?_ ?_ ?_ ?_
  · rw [semsOf, List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun q _ v hv => ?_
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hv
    exact (restrict_e.mp hw).1
  · rw [semsOf, List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun q _ a ha => ?_
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨hp, hq⟩ := restrict_p.mp hw
    exact ⟨w, hp, hq⟩
  · rw [List.pairwise_map]
    refine hdisj.imp fun h v hv hv' => ?_
    simp only at hv hv'
    rw [h v hv] at hv'; exact nomatch hv'
  · rw [List.pairwise_map]
    refine hdisj.imp fun h a hx hy => ?_
    obtain ⟨v, hv, hqv⟩ := hx
    obtain ⟨v', hv', hqv'⟩ := hy
    rw [hv] at hv'; cases hv'
    rw [h v hqv] at hqv'; exact nomatch hqv'
  · rw [semsOf, List.map_map]
    refine forall_mem_map fun p _ t a he => ?_
    simp only [Function.comp_apply] at he ⊢
    rw [optionSemOf_c] at he
    obtain ⟨hq, hb⟩ := restrict_e.mp he
    refine ⟨?_, ?_⟩
    · show ((denote (.refine base p)).e t).isSome = true
      rw [show (denote (.refine base p)).e t = some a from he]; rfl
    · show ((denote (.refine base p)).p a).isSome = true
      rw [show (denote (.refine base p)).p a = some t from
        restrict_p.mpr ⟨hlaw.retract hb, hq⟩]
      rfl

/-- **Literals over any base, in one theorem.** Drop the lawfulness side-condition by
    taking it from soundness, and what is left is the whole result: for *any derivable
    term* as base, a union of refinements with pairwise disjoint predicates admits uniquely
    on both sides.

    §3's `(literal-S)` and `(literal-N)` are two instantiations — `string` and the ungated
    double codec, at `∈ ℓ`. `boolean` and `binary` are two more, for which §3 writes no
    rule. And the base need not be ground at all: a union of disjoint refinements of one
    `object`, or of one `union`, discharges by the same theorem. There was never a
    per-member argument to make. -/
theorem uAtCan_of_refine_disjoint_of_typed {base : Term} {T μ}
    {ps : List Pred} (h : Typed base T μ) (hob : Obligations base)
    (hdisj : List.Pairwise (fun p p' => ∀ v, p.eval v = true → p'.eval v = false) ps) :
    UAtCan (ps.map (fun p => Term.refine base p)) :=
  uAtCan_of_refine_disjoint (soundness_both h hob).1 hdisj

/-! ### Literals over a primitive §3 gives no `literal` rule for

    §3 names two `literal` rules, at `S` and at `N`. Nothing makes those two special: a
    literal over any ground term is `refine(base, ∈ ℓ)`, which is derivable already, and
    since refinements of one base separate on both sides, such a union discharges exactly as
    a string literal's does. The two rules are the two someone
    bothered to name, not the two that are possible. -/

/-- A boolean "literal", as the refinement it is. -/
def isTrueV : Value → Bool := fun v => match v with | .bool b => b | _ => false

/-- …and its complement. -/
def isFalseV : Value → Bool := fun v => match v with | .bool b => !b | _ => false

/-- It is derivable, with the member the base names — no rule of its own. -/
theorem typed_boolLiteral : ∃ T, Typed (.refine .boolean (.closure isTrueV)) T (some .BOOL) :=
  ⟨_, Typed.refine Typed.boolean⟩

/-- A base that is not ground at all, to show the theorem does not care. Two disjoint
    refinements of one `array(string)` separate exactly as two literals over `string` do —
    "literal" was never the operative word, "one base, disjoint predicates" was. -/
theorem uAtCan_refine_container {p p' : Pred}
    (hd : List.Pairwise (fun a b => ∀ v, a.eval v = true → b.eval v = false) [p, p']) :
    UAtCan [Term.refine (.array .string) p, Term.refine (.array .string) p'] :=
  uAtCan_of_refine_disjoint_of_typed (Typed.array Typed.string)
    trivial hd

/-- And a union of two discharges on **both** sides, by the same shared-base argument that
    settles numeric literals — a primitive §3 never wrote a `literal` rule for. -/
theorem uAtCan_boolLiterals :
    UAtCan [Term.refine .boolean (.closure isTrueV), Term.refine .boolean (.closure isFalseV)] := by
  have h : ∀ v, isTrueV v = true → isFalseV v = false := by
    intro v hv; cases v <;> simp_all [isTrueV, isFalseV]
  exact uAtCan_of_refine_disjoint (ps := [.closure isTrueV, .closure isFalseV])
    lawful_booleanCodec.core (by simpa [Pred.eval] using h)

/-! ### What the unified `literal` carries

    At arity one `literal(v)` and `refine(g, · = v)` denote the same pair, so it is fair to
    ask why the constructor exists. The writable side is the same either way. The readable
    side is not: `ℓ` is data the *term* owns, so it can be tested against the stored
    attribute, where `refine`'s `q` is a value predicate and cannot be pushed there. That is
    the whole of it, and it holds at every base but one. -/







/-- **A union of numeric literals discharges on both sides — in one step, for any arity.**
    This used to be advertised as the *only* route, on the ground that a numeric literal's
    readable side went to `⊤` and no row could therefore tell two of them apart. The second
    half of that was wrong — the row asks the codec and tells two literals apart — and the
    correction does not cost
    this theorem anything: read from the *pair*, the options are refinements of a single
    `numberCodec` with disjoint predicates, and `uniqueAdmission_of_sharedBase` settles an
    `n`-ary family and both sides at once, where the table settles a pair at a time.

    Which is the honest reading of what a numeric literal set *is*: options told apart by
    the value a read produces, never by the text the store holds. That reading is now
    available to the table as well, because the table's row asks the same codec. -/
theorem uAtCan_of_literalN_disjoint {lss : List (NEFinset WFDouble)}
    (hdisj : List.Pairwise (fun ls ls' => ∀ d ∈ ls.1, d ∉ ls'.1) lss) :
    UAtCan (lss.map (Term.literal .number)) := by
  show UniqueAdmission (semsOf (lss.map (Term.literal .number)))
  have hs : semsOf (lss.map (Term.literal .number))
      = (lss.map (literalCodec .number)).map OptionSem.byAttempt := by
    simp [semsOf, List.map_map, specOf, optionSemOf, denote]
  rw [hs]
  refine uniqueAdmission_of_sharedBase (base := numberCodec) (qs := lss.map (inL .number))
    lawful_numberCodec.core ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun ls _ =>
      ⟨literalCodec_e_restrict .number ls, literalCodec_p_restrict .number ls⟩
  · rw [List.pairwise_map]
    refine hdisj.imp fun h v hv => ?_
    cases v
    case num d =>
      -- the gate is now inside `inL`'s `number` row, so the split names the subtype
      cases hw : Numeral.WF d.toDec with
      | false => simp [inL, hw] at hv
      | true =>
        simp only [inL, hw, dite_true, decide_eq_true_eq] at hv
        simp only [inL, hw, dite_true, decide_eq_false_iff_not]
        exact h ⟨d, hw⟩ hv
    all_goals exact Bool.noConfusion hv

/-! ## The other two rows of §5's table

    §5's discharger table has four rows, and until now a reviewer checking it changed
    vocabulary halfway across: two rows are about `UAtCan opts` — a list of
    **terms** — and two are about `UniqueAdmission os`, a list of `OptionSem`. Worse,
    `(dunion)`'s row was never stated at all: it appeared only inside
    ~~lawful_dunionCodec~~, where it is an argument rather than a claim.

    `(dunion)`'s row moves to term level here, so three of the four are one vocabulary.
    The fourth cannot follow, and the reason is worth stating rather than working
    around: `denote` gives `(opaque)` the **fuel-free** `opaqCodecω`, which budgets each
    input by its own depth and is not `altCodec` over any one list of options. Its (U)
    is therefore a statement about `opaqCodec` at a fuel, one level below the term
    language. That is a fact about `opaque`, not a gap in the table. -/

/-! **Row three is gone, and that is the row's answer.** §5 called `(dunion)` "the one union
whose (U) is discharged by the rule itself", and the discharge was ~~uAtCan_dunion~~ over
~~semsOfD~~, the option list `denote`'s dunion case used to build. There is no option list now:
the variants are a table keyed by tag and the denotation is a lookup, so at most one variant is
reached by construction and there is no unique-admission statement left to make. ~~uAtCan_dunion~~,
~~UAtCanD~~ and ~~semsOfD~~ are deleted rather than restated, which is the strongest form the row's
claim can take. -/

/-- **Row four: `(opaque)`'s (U), unconditionally.** `uniqueAdmission_opaque` asks for the
    recursive option's lawfulness; `lawful_opaqCodec` supplies it, so the row has no
    premises at all. It is stated about `opaqCodec` at a fuel rather than about the term
    `opaque` for the reason given above — `denote` of `opaque` is not a sum over one
    list. -/
theorem uAtCan_opaque {fuel : Nat} (lossy : Bool) :
    UniqueAdmission (opaqOptions lossy (opaqCodec fuel lossy)) :=
  uniqueAdmission_opaque fuel lossy (lawful_opaqCodec fuel lossy)

/-! ## Premises checked at a pair

    Two helpers for instantiating a discharger's `∀ t ∈ opts` and `Pairwise` premises at a
    two-option union. They outlived the discharger they were written for: `Orthogonality.lean`
    uses both, which is why they are here rather than deleted with it. -/

/-- A premise of the form `∀ t ∈ [x, y], P t`, checked at the two options. -/
theorem forall_mem_pair {α : Type} {P : α → Prop} {x y : α} (hx : P x) (hy : P y) :
    ∀ z ∈ [x, y], P z := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hx
  · rcases List.mem_cons.mp hz with rfl | hz
    · exact hy
    · exact absurd hz (by simp)

/-- A pairwise premise over two options, checked at the single unordered pair. -/
theorem pairwise_pair {α : Type} {R : α → α → Prop} {x y : α} (h : R x y) :
    List.Pairwise R [x, y] := by
  refine List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil)
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact h
  · exact absurd hz (by simp)

/-! ## Why "one option decides its own membership" was never an exemption

    An earlier §5 stated its writable-side discharger as a disjunction over whether an option
    *decides its own membership* — a `literal` does, a bare `string` does not — and called it sufficient for
    (U). It is not, and the two counterexamples below are why no discharger here or in
    `Orthogonality.lean` carries that disjunct. §5 keeps both counterexamples and states the
    discharger on the admissible sets themselves, so what follows is the machine-checked half of a
    correction the document has already made, not a live disagreement with it.

    The withdrawn rule was right about what deciding buys: attempted admission on a
    `literal` is evidence, where attempted admission on `string` is not. What it dropped is
    that evidence only *resolves* a pair when it is available on **both** sides and the two
    admissible sets are **disjoint**. §5's own worked example,
    `union(literal("A"), literal("B"))`, has both; the rule offered in support of it demanded
    neither. -/

/-- A helper: two options of a two-element union that both admit one value refute (U).
    `hne` separates the options at some other value, so the singleton filter fails. -/
theorem not_uAtCan_pair {t₁ t₂ : Term} {v w : Value} {a : Attr}
    (he : (denote t₁).e v = some a)
    (h₂ : (optionSemOf (denote t₂) (specOf t₂)).admitV v = true)
    (hne : (optionSemOf (denote t₁) (specOf t₁)).admitV w ≠
      (optionSemOf (denote t₂) (specOf t₂)).admitV w) :
    ¬ UAtCan [t₁, t₂] := by
  intro h
  have ho : optionSemOf (denote t₁) (specOf t₁) ∈ semsOf [t₁, t₂] :=
    List.mem_cons_self
  have hfilt := (h _ ho v a (by rw [optionSemOf_c]; exact he)).2
  -- the second option survives the filter too, so the filter cannot be `[o₁]`
  have hmem : optionSemOf (denote t₂) (specOf t₂) ∈
      [optionSemOf (denote t₁) (specOf t₁)] := by
    rw [← hfilt]
    exact List.mem_filter.mpr
      ⟨List.mem_cons_of_mem _ (List.mem_cons_self), h₂⟩
  rcases List.mem_cons.mp hmem with heq | hnil
  · exact hne (congrArg (fun o => OptionSem.admitV o w) heq.symm)
  · exact absurd hnil (by simp)

/-- **One option deciding its own membership does not discharge (U).**
    `union(literal("A"), string)` passes the exemption §5 withdrew — the literal decides —
    and violates (U) at the value `"A"`, which both options admit. `literal`'s attempt *is*
    evidence; `string`'s is not, and one honest answer does not resolve a pair. -/
theorem not_uAtCan_literal_string :
    ¬ UAtCan [Term.literal .string (.of "A" ∅), Term.string] := by
  have hA : (denote (Term.literal .string (.of "A" ∅))).e (Value.str "A") = some (Attr.s "A") := by
    show (if "A" ∈ ["A"] then some (Attr.s "A") else none) = some (Attr.s "A")
    rw [if_pos (List.mem_cons_self)]
  have hB : (denote (Term.literal .string (.of "A" ∅))).e (Value.str "B") = none := by
    show (if "B" ∈ ["A"] then some (Attr.s "B") else none) = none
    rw [if_neg (by simp)]
  refine not_uAtCan_pair (v := .str "A") (a := Attr.s "A") (w := .str "B") hA rfl ?_
  · show ((denote (Term.literal .string (.of "A" ∅))).e (Value.str "B")).isSome ≠
      ((denote Term.string).e (Value.str "B")).isSome
    rw [hB]
    exact fun h => nomatch h

/-- **Both options deciding does not discharge (U) either.** Deciding propagates through
    `array`, so `union(array(literal("A")), array(literal("B")))` has it on both sides — and
    both options admit the empty array, which neither literal ever sees. Propagating the
    property through a container does not propagate disjointness of the admissible sets:
    every container admits its empty case. -/
theorem not_uAtCan_array_literals :
    ¬ UAtCan [Term.array (.literal .string (.of "A" ∅)), Term.array (.literal .string (.of "B" ∅))] := by
  refine not_uAtCan_pair (v := .arr []) (a := Attr.l []) (w := .arr [.str "A"])
    rfl rfl ?_
  -- separated one fuel down, where the element codecs are live: `["A"]` is written by
  -- the first option and refused by the second
  show ((match (if "A" ∈ ["A"] then some (Attr.s "A") else none),
      some ([] : List Attr) with
      | some y, some ys => some (y :: ys) | _, _ => none).map Attr.l).isSome ≠
    ((match (if "A" ∈ ["B"] then some (Attr.s "A") else none),
      some ([] : List Attr) with
      | some y, some ys => some (y :: ys) | _, _ => none).map Attr.l).isSome
  rw [if_pos (List.mem_cons_self), if_neg (by simp)]
  exact fun h => nomatch h

/-! ### …and the same union meets the residue the laws actually carry

    `not_uAtCan_array_literals` refutes `UAtCan` at `[]` — a canonical pair of *each*
    option, and one the union never writes, since both admit it and `altCodec` declines
    what it cannot resolve. `UAtAct` (§5, `Soundness.lean`) asks only where the union
    acts, and the same term meets it: every value the union does write is read back by
    the option that wrote it.

    So the two residues are not the same condition, and the gap is not a curiosity — it
    holds `union(array(literal "A"), array(literal "B"))`, which is a schema people write.
    What carries it is that a `literal`'s two halves test one set, so an element the
    neighbouring option declines to *write* is one it declines to *read*. That is exactly
    what `held` breaks (`not_uAtCan_literal_held`), which is why the argument is about
    literals and not about containers in general. -/

/-! `literalCodec` at the string base, in the shape the four lemmas below need.

Named rather than unfolded. ~~literalSCodec~~ used to be a hand-written pair, so `simp
[literalSCodec]` was one step; the unified codec is `Codec.restrict` over `baseCodec`, and
unfolding that inside a `simp_all` with two hypotheses in play runs out of heartbeats — the
`whnf` reaches for `numberCodec`'s `dite` on `Numeral.WF`, which is a string parser. The fix is
the one the other three numeric sites use: state the consequence once, and rewrite with it. -/

theorem literalCodec_string_e (ls : NEFinset String) : ∀ v : Value,
    (literalCodec .string ls).e v
      = (match v with | .str s => if s ∈ ls.1 then some (Attr.s s) else none | _ => none)
  | .str _ => by simp [literalCodec, baseCodec, Codec.restrict, inL, stringCodec]
  | .num _ | .bool _ | .bin _ | .null | .strSet _ | .numSet _ | .binSet _
  | .arr _ | .map _ _ => rfl

theorem literalCodec_string_p (ls : NEFinset String) : ∀ a : Attr,
    (literalCodec .string ls).p a
      = (match a with | .s s => if s ∈ ls.1 then some (Value.str s) else none | _ => none)
  | .s _ => by simp [literalCodec, baseCodec, Codec.restrict, inL, stringCodec]
  | .n _ | .bool _ | .b _ | .null | .ss _ | .ns _ | .bs _ | .l _ | .m _ _ => rfl

/-- §3 `(literal-S)`'s two halves test one set, so a `literal` declines to read the
    attribute it declines to write. -/
theorem literalS_p_none {ls ls' : NEFinset String} {t : Value} {a : Attr}
    (he : (literalCodec .string ls).e t = some a) (hne : (literalCodec .string ls').e t = none) :
    (literalCodec .string ls').p a = none := by
  rw [literalCodec_string_e] at he hne
  cases t <;> simp_all
  obtain ⟨-, rfl⟩ := he
  rw [literalCodec_string_p]
  simp [hne]

/-- …the reading half of the same §3 `(literal-S)` fact. -/
theorem literalS_e_none {ls ls' : NEFinset String} {t : Value} {a : Attr}
    (hp : (literalCodec .string ls).p a = some t) (hne : (literalCodec .string ls').p a = none) :
    (literalCodec .string ls').e t = none := by
  rw [literalCodec_string_p] at hp hne
  cases a <;> simp_all
  obtain ⟨-, rfl⟩ := hp
  rw [literalCodec_string_e]
  simp [hne]

/-- §3 `(array)`'s traversal inherits it: an element the neighbour refuses makes the
    whole list unreadable, at the position the writing traversal already fixed. -/
theorem traverse_literalS_p_none {ls ls' : NEFinset String} {vs : List Value} {as : List Attr}
    (he : traverse (literalCodec .string ls).e vs = some as)
    (hne : traverse (literalCodec .string ls').e vs = none) :
    traverse (literalCodec .string ls').p as = none := by
  cases hres : traverse (literalCodec .string ls').p as with
  | none => rfl
  | some ws =>
    exfalso
    have hall : ∀ v ∈ vs, ((literalCodec .string ls').e v).isSome := by
      intro v hv
      obtain ⟨a, ha, hea⟩ := (traverse_eq_some.mp he).mem_left hv
      obtain ⟨w, -, hpw⟩ := (traverse_eq_some.mp hres).mem_left ha
      cases hev : (literalCodec .string ls').e v with
      | none => rw [literalS_p_none hea hev] at hpw; exact nomatch hpw
      | some _ => rfl
    have hs := traverse_isSome_of_all hall
    rw [hne] at hs
    exact nomatch hs

/-- …and dually, at §3 `(array)`. -/
theorem traverse_literalS_e_none {ls ls' : NEFinset String} {as : List Attr} {vs : List Value}
    (hp : traverse (literalCodec .string ls).p as = some vs)
    (hne : traverse (literalCodec .string ls').p as = none) :
    traverse (literalCodec .string ls').e vs = none := by
  cases hres : traverse (literalCodec .string ls').e vs with
  | none => rfl
  | some ws =>
    exfalso
    have hall : ∀ a ∈ as, ((literalCodec .string ls').p a).isSome := by
      intro a ha
      obtain ⟨v, hv, hpv⟩ := (traverse_eq_some.mp hp).mem_left ha
      obtain ⟨w, -, hew⟩ := (traverse_eq_some.mp hres).mem_left hv
      cases hpa : (literalCodec .string ls').p a with
      | none => rw [literalS_e_none hpv hpa] at hew; exact nomatch hew
      | some _ => rfl
    have hs := traverse_isSome_of_all hall
    rw [hne] at hs
    exact nomatch hs

/-- §3 `(array)` over §3 `(literal-S)`: it refuses on the attribute side whatever it
    refuses on the value side, at the attribute its neighbour wrote. -/
theorem arrayLiteral_p_none {ls ls' : NEFinset String} {t : Value} {a : Attr}
    (he : (arrayCodec (literalCodec .string ls)).e t = some a)
    (hne : (arrayCodec (literalCodec .string ls')).e t = none) :
    (arrayCodec (literalCodec .string ls')).p a = none := by
  cases t with
  | arr vs =>
    simp only [arrayCodec, Option.map_eq_some_iff] at he
    obtain ⟨as, has, rfl⟩ := he
    simp only [arrayCodec] at hne ⊢
    cases h2 : traverse (literalCodec .string ls').e vs with
    | some _ => rw [h2] at hne; exact nomatch hne
    | none => rw [traverse_literalS_p_none has h2]; rfl
  | _ => exact nomatch he

/-- …and dually, the same §3 pair. -/
theorem arrayLiteral_e_none {ls ls' : NEFinset String} {t : Value} {a : Attr}
    (hp : (arrayCodec (literalCodec .string ls)).p a = some t)
    (hne : (arrayCodec (literalCodec .string ls')).p a = none) :
    (arrayCodec (literalCodec .string ls')).e t = none := by
  cases a with
  | l as =>
    simp only [arrayCodec, Option.map_eq_some_iff] at hp
    obtain ⟨vs, hvs, rfl⟩ := hp
    simp only [arrayCodec] at hne ⊢
    cases h2 : traverse (literalCodec .string ls').p as with
    | some _ => rw [h2] at hne; exact nomatch hne
    | none => rw [traverse_literalS_e_none hvs h2]; rfl
  | _ => exact nomatch hp

/-- The two §5 options are distinct — needed only to read a singleton filter back. -/
theorem optionSem_arrayLiterals_ne :
    OptionSem.byAttempt (arrayCodec (literalCodec .string (.of "A" ∅))) ≠
      OptionSem.byAttempt (arrayCodec (literalCodec .string (.of "B" ∅))) := by
  intro h
  have := congrArg (fun o => o.admitV (.arr [.str "A"])) h
  simp [OptionSem.byAttempt, arrayCodec, traverse, literalCodec, baseCodec, Codec.restrict, inL, stringCodec] at this

/-- **§5's two residues, separated at a schema people write.**
    `union(array(literal "A"), array(literal "B"))` fails `UAtCan`
    (`not_uAtCan_array_literals`) and meets `UAtAct` — so the soundness theorem covers it
    once (U) is asked where the union acts rather than at every option's canonicals. The
    union declines the empty array, and every value it does write round-trips through the
    option that wrote it. -/
theorem uAtAct_array_literals :
    UAtAct [Term.array (.literal .string (.of "A" ∅)), Term.array (.literal .string (.of "B" ∅))] := by
  show UniqueBothWays [OptionSem.byAttempt (arrayCodec (literalCodec .string (.of "A" ∅))),
    OptionSem.byAttempt (arrayCodec (literalCodec .string (.of "B" ∅)))]
  have lawA : LawfulCore (arrayCodec (literalCodec .string (.of "A" ∅))) :=
    lawfulCore_arrayCodec (lawful_literalCodec _ _).core
  have lawB : LawfulCore (arrayCodec (literalCodec .string (.of "B" ∅))) :=
    lawfulCore_arrayCodec (lawful_literalCodec _ _).core
  refine ⟨?_, ?_⟩
  · intro o ho t a hf he
    rcases List.mem_cons.mp ho with rfl | ho'
    · obtain ⟨-, hB⟩ := filter_pair_left_inv optionSem_arrayLiterals_ne hf
      rw [OptionSem.byAttempt_admitV] at hB
      have hBe : (arrayCodec (literalCodec .string (.of "B" ∅))).e t = none := by
        cases h : (arrayCodec (literalCodec .string (.of "B" ∅))).e t with
        | none => rfl
        | some _ => rw [h] at hB; exact nomatch hB
      refine filter_pair_left ?_ ?_
      · rw [OptionSem.byAttempt_admitA, lawA.retract he]; rfl
      · rw [OptionSem.byAttempt_admitA, arrayLiteral_p_none he hBe]; rfl
    · rcases List.mem_singleton.mp ho' with rfl
      obtain ⟨hA, -⟩ := filter_pair_right_inv optionSem_arrayLiterals_ne hf
      rw [OptionSem.byAttempt_admitV] at hA
      have hAe : (arrayCodec (literalCodec .string (.of "A" ∅))).e t = none := by
        cases h : (arrayCodec (literalCodec .string (.of "A" ∅))).e t with
        | none => rfl
        | some _ => rw [h] at hA; exact nomatch hA
      refine filter_pair_right ?_ ?_
      · rw [OptionSem.byAttempt_admitA, arrayLiteral_p_none he hAe]; rfl
      · rw [OptionSem.byAttempt_admitA, lawB.retract he]; rfl
  · intro o ho a t a' hf hp he
    rcases List.mem_cons.mp ho with rfl | ho'
    · obtain ⟨-, hB⟩ := filter_pair_left_inv optionSem_arrayLiterals_ne hf
      rw [OptionSem.byAttempt_admitA] at hB
      have hBp : (arrayCodec (literalCodec .string (.of "B" ∅))).p a = none := by
        cases h : (arrayCodec (literalCodec .string (.of "B" ∅))).p a with
        | none => rfl
        | some _ => rw [h] at hB; exact nomatch hB
      have h' : (arrayCodec (literalCodec .string (.of "A" ∅))).e t = some a' := he
      refine filter_pair_left ?_ ?_
      · rw [OptionSem.byAttempt_admitV, h']; rfl
      · rw [OptionSem.byAttempt_admitV, arrayLiteral_e_none hp hBp]; rfl
    · rcases List.mem_singleton.mp ho' with rfl
      obtain ⟨hA, -⟩ := filter_pair_right_inv optionSem_arrayLiterals_ne hf
      rw [OptionSem.byAttempt_admitA] at hA
      have hAp : (arrayCodec (literalCodec .string (.of "A" ∅))).p a = none := by
        cases h : (arrayCodec (literalCodec .string (.of "A" ∅))).p a with
        | none => rfl
        | some _ => rw [h] at hA; exact nomatch hA
      have h' : (arrayCodec (literalCodec .string (.of "B" ∅))).e t = some a' := he
      refine filter_pair_right ?_ ?_
      · rw [OptionSem.byAttempt_admitV, arrayLiteral_e_none hp hAp]; rfl
      · rw [OptionSem.byAttempt_admitV, h']; rfl

/-! ## Why (D) does not discharge the readable side either

    An earlier §5 listed **(D)** — incomparable held sets — as a discharger of (U)'s
    readable side, and held that stating it as genuine *disjointness* would be sound
    though needlessly strict. Disjointness is not sound either: held sets are sets of
    **values**, (U)'s readable side quantifies over **attributes**, and `held` is exactly
    the term that separates the two. Its adapter relabels, so two options can hold
    disjoint sets of values and still read one attribute — each to its own value. §5 now
    says this, and (D) is a well-formedness condition on the `T` index rather than a
    discharger; the witness below is what settled it.

    That witness is `union(literal("A"), held(literal("A"), f, g))` with `f` and `g`
    swapping `"B"` for `"A"`. Its held sets are `{"A"}` and `{"B"}` — disjoint, so (D)
    passes in the strongest form ever proposed for it — and both options read the
    attribute `S "A"`, the first to `"A"` and the second to `"B"`. What decides the
    readable side is a condition on stored attributes: distinct members, or disjoint
    readable-side admission. -/

/-- (D) in its held-set form, as the disjointness §5 proposes: no value is held by two
    options. Stated so the counterexample below can be about it.

    This is *not* the rule's premise: `(union)` carries `DIncomp` (`Typing.lean`), §5's
    incomparability. `DDisj` is the strictly stronger reading §5 considered and withdrew,
    and it is here only to be refuted — the witness below satisfies it and still fails
    (U). -/
def DDisj (Tx Ty : Held) : Prop := ∀ v, Tx v → ¬ Ty v

/-- The relabelling adapter: `"B"` on the outside is `"A"` on the inside. -/
def fRel : Value → Value := fun v => match v with | .str "B" => .str "A" | _ => .null

/-- Its inverse on the carriers. -/
def gRel : Value → Value := fun v => match v with | .str "A" => .str "B" | _ => .null

/-- `held(literal("A"), fRel, gRel)` — holds `{"B"}`, stores it as `S "A"`. -/
def tRel : Term := .held (.literal .string (.of "A" ∅)) fRel gRel

/-- The attribute-side twin of `not_uAtCan_pair`. -/
theorem not_uAtCan_pair_A {t₁ t₂ : Term} {v w : Value} {a : Attr}
    (he : (denote t₁).e v = some a)
    (h₂ : (optionSemOf (denote t₂) (specOf t₂)).admitA a = true)
    (hne : (optionSemOf (denote t₁) (specOf t₁)).admitV w ≠
      (optionSemOf (denote t₂) (specOf t₂)).admitV w) :
    ¬ UAtCan [t₁, t₂] := by
  intro h
  have ho : optionSemOf (denote t₁) (specOf t₁) ∈ semsOf [t₁, t₂] :=
    List.mem_cons_self
  have hfilt := (h _ ho v a (by rw [optionSemOf_c]; exact he)).1
  have hmem : optionSemOf (denote t₂) (specOf t₂) ∈
      [optionSemOf (denote t₁) (specOf t₁)] := by
    rw [← hfilt]
    exact List.mem_filter.mpr
      ⟨List.mem_cons_of_mem _ (List.mem_cons_self), h₂⟩
  rcases List.mem_cons.mp hmem with heq | hnil
  · exact hne (congrArg (fun o => OptionSem.admitV o w) heq.symm)
  · exact absurd hnil (by simp)

/-- Both options are derivable, and their held sets are disjoint — so this really is a
    union (D) admits, in the disjointness form §5 once proposed and withdrew. -/
theorem typed_tRel :
    Typed tRel (fun v => ∃ s, s ∈ ["A"] ∧ fRel v = .str s) (some .S) := by
  refine Typed.held (I := fun w => ∃ s, s ∈ ["A"] ∧ w = .str s) ?_
  have h := Typed.literal .string (.of "A" ∅)
  have hT : HLit .string (.of "A" ∅) = fun w => ∃ s, s ∈ ["A"] ∧ w = Value.str s := by
    funext w; simp [HLit, NEFinset.of]
  rw [hT] at h
  exact h

theorem dDisj_tRel :
    DDisj (fun v => ∃ s, s ∈ ["A"] ∧ v = .str s)
      (fun v => ∃ s, s ∈ ["A"] ∧ fRel v = .str s) := by
  rintro v ⟨s, hs, rfl⟩ ⟨s', hs', hf⟩
  -- `v = "A"`, so `fRel v = null`, which is no string
  have : s = "A" := by simpa using hs
  subst this
  exact nomatch hf

/-- **(D) does not discharge the readable side.** Disjoint held sets, and both options
    admit the attribute `S "A"` — the first reading it to `"A"`, the second to `"B"`. -/
theorem not_uAtCan_literal_held :
    ¬ UAtCan [Term.literal .string (.of "A" ∅), tRel] := by
  have hA : (denote (Term.literal .string (.of "A" ∅))).e (Value.str "A") = some (Attr.s "A") := by
    show (if "A" ∈ ["A"] then some (Attr.s "A") else none) = some (Attr.s "A")
    rw [if_pos (List.mem_cons_self)]
  refine not_uAtCan_pair_A (v := .str "A") (a := Attr.s "A") (w := .str "A") hA ?_ ?_
  · show (((if "A" ∈ ["A"] then some (Value.str "A") else none).map gRel)).isSome = true
    rw [if_pos (List.mem_cons_self)]
    rfl
  · show ((denote (Term.literal .string (.of "A" ∅))).e (Value.str "A")).isSome ≠
      ((denote (Term.literal .string (.of "A" ∅))).e (fRel (Value.str "A"))).isSome
    rw [hA]
    show true ≠ ((denote (Term.literal .string (.of "A" ∅))).e Value.null).isSome
    exact fun h => nomatch h


end Calculus
