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
and `opaque`, whose (U) is a theorem one level below the term language.
`uAtAct_array_literals`, which holds where `UAtCan` is outright false, needs no hand proof:
the pair is held-free, and `uAtAct_of_HF` (`Confluence.lean`) discharges it.

§5's (D) is not among them, and `not_uAtCan_literal_held` is why: held sets are sets of
values, (U)'s readable side quantifies over attributes, and `held`'s adapter relabels
between them. Two options can hold disjoint sets and read one attribute. (D) is a
well-formedness condition on the `T` index and lives there — `DIncomp`, a premise of
`Typed.union` (`Typing.lean`), which asks `HDisj` of every pair. As a discharger of (U),
`HDisj` of every pair is refuted below.

The two counterexamples that repaired §5's discharger are at the foot of the file. §5 keeps
both, and
they are the machine-checked half of a correction the document has already made.
-/

namespace Calculus

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
  replace h : ((denote t).p a).isSome = true := h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  refine hlaw.reads ?_ hv
  rw [denote_μ]
  exact hμ

/-! ## Options admit their own canonical pairs -/

/-- Only `optional` denotes to `opt`, which is what the value-side guard needs of a
    non-`optional` field. Stated where every argument is a variable — at the use site
    the field is `ff k`, and eliminating a function application in place is more
    trouble than naming the fact. -/
theorem fieldSem_ne_opt {fd : ObjectSlot}
    (h : (match fd with | ObjectSlot.optional _ => false | _ => true) = true) :
    ∀ c, fieldSem fd ≠ FieldSem.opt c := by
  cases fd with
  | req t => simp_all [fieldSem]
  | optional t => simp_all

/-- **Name admission, from the three facts `keysOk` reads.** The first premise is the body's
    claim on a present name: an open block claims every name, and a closed body claims the
    names it declares. The two that follow are the declared names' own presence bits. -/
theorem keysOk_of_names {fields : Finset Name} {ff : {k // k ∈ fields} → ObjectSlot}
    {wild : Option Term} {keys : Finset Name}
    (hclaims : wild.isSome = true ∨ ∀ k ∈ keys, k ∈ fields)
    (hreq : ∀ k : {k // k ∈ fields},
      (ff k).presence.2 = false → k.1 ∈ keys)
    (hforbid : ∀ k : {k // k ∈ fields},
      (ff k).presence.1 = false → k.1 ∉ keys) :
    keysOk (Body.spec (.mk fields ff wild))
      keys = true := by
  simp only [keysOk, Body.spec, Bool.and_eq_true]
  refine ⟨?_, decide_eq_true hreq, decide_eq_true hforbid⟩
  rcases hclaims with hw | hsub
  · cases wild with
    | none => exact absurd hw (by simp)
    | some _ => simp
  · simp only [Bool.or_eq_true]
    exact Or.inr (decide_eq_true hsub)

/-- Object-encode under a closed rest policy stamps name admission: every written name
    is declared and every non-`opt` name is written.

    **One statement where there were two.** The list representation had a value row and
    an attribute row, and the second half of this lemma was the first transported along
    `traverse_fst`. `M`'s payload is a key set with a function on it, and encoding does
    not touch the key set — so the value side's admission *is* the attribute side's, and
    there is nothing to transport. -/
theorem keysOk_of_encode {fields : Finset Name} {ff : {k // k ∈ fields} → ObjectSlot}
    {wild : Option Term} {keys : Finset Name}
    {f : {k // k ∈ keys} → Value} {g : {k // k ∈ keys} → Attr}
    (hval : valPresentB ⟨fields, fun k => fieldSem (ff k)⟩ keys = true)
    (hfi : funImage (fun k : {k // k ∈ keys} =>
        (entryCodec ⟨fields, fun k => fieldSem (ff k)⟩ (rcOf (wildSem wild)) k.1).bind
          (fun c => c.e (f k))) = some g) :
    keysOk (Body.spec (.mk fields ff wild))
      keys = true := by
  refine keysOk_of_names ?_ (fun k hb => ?_) (fun k hb hk => ?_)
  · -- an open block claims every name; a closed body claims only what it declares, and
    -- there `entryCodec` succeeds through the field table alone
    cases hwild : wild with
    | some _ => exact Or.inl rfl
    | none =>
      refine Or.inr (fun k hk => ?_)
      apply Decidable.byContradiction
      intro hnk
      have hw := funImage_some hfi ⟨k, hk⟩
      rw [hwild] at hw
      rw [show entryCodec (⟨fields, fun k => fieldSem (ff k)⟩ : MapOf FieldSem)
            (rcOf (wildSem none)) k
          = none from by simp only [rcOf, wildSem, entryCodec, MapOf.at, dif_neg hnk]] at hw
      exact nomatch hw
  · apply valPresentB_spec hval (MapOf.at_of_mem (m := ⟨fields, _⟩) k)
    apply fieldSem_ne_opt
    cases hfd : ff k with
    | req t => simp
    | optional t => cases t <;> simp [ObjectSlot.presence, Term.isNever, hfd] at hb
  · have hw := funImage_some hfi ⟨k.1, hk⟩
    have he : (fieldSem (ff k)).codec.e (f ⟨k.1, hk⟩) = some (g ⟨k.1, hk⟩) := by
      rw [show entryCodec (⟨fields, fun k => fieldSem (ff k)⟩ : MapOf FieldSem)
            (rcOf (wildSem wild)) k.1
          = some (fieldSem (ff k)).codec by
            simp only [entryCodec, MapOf.at, dif_pos k.2]] at hw
      simpa using hw
    cases hfd : ff k with
    | req t =>
      cases t <;> simp [ObjectSlot.presence, ObjectSlot.isReq, Term.isNever, hfd] at hb
      case never =>
        rw [hfd] at he
        change none = some _ at he
        cases he
    | optional t =>
      cases t <;> simp [ObjectSlot.presence, Term.isNever, hfd] at hb
      case never =>
        rw [hfd] at he
        change none = some _ at he
        cases he

/-- A field whose term is a literal writes only that literal's alternatives, whatever the
    slot's presence marker: `fieldSem` carries the same codec through both marks, and
    `altsOfField` reads the same. -/
theorem litOkV_of_field_e : ∀ {fd : ObjectSlot} {v a}, (fieldSem fd).codec.e v = some a →
    altsOkV (altsOfField fd) v = true
  | .req t, _, _, he  | .optional t, _, _, he => by
      cases t <;> first
        | rfl
        | exact inL_of_literalCodec_e (by simpa [fieldSem, FieldSem.codec, denote] using he)

/-- …and the attribute it wrote is one the same codec reads back, which is `retract` at the
    field's own codec rather than at the object's. -/
theorem litOkA_of_field_e : ∀ {fd : ObjectSlot} {v a}, (fieldSem fd).codec.e v = some a →
    altsOkA (altsOfField fd) a = true
  | .req t, _, _, he  | .optional t, _, _, he => by
      cases t <;> first
        | rfl
        | exact Option.isSome_iff_exists.mpr ⟨_, (lawful_literalCodec _ _).retract
            (by simpa [fieldSem, FieldSem.codec, denote] using he)⟩

/-- …and the same fact at the term level, which the open block needs: the block carries a
    term, so the alternatives are `altsOfTerm`'s and the codec is the term's own. -/
theorem altsOkV_of_term_e : ∀ {t : Term} {v a}, (denote t).e v = some a →
    altsOkV (altsOfTerm t) v = true
  | t, _, _, he => by
      cases t <;> first
        | rfl
        | exact inL_of_literalCodec_e (by simpa [denote] using he)

/-- …and the read side of the same, at the attribute the block's codec wrote. -/
theorem altsOkA_of_term_e : ∀ {t : Term} {v a}, Lawful (denote t) → (denote t).e v = some a →
    altsOkA (altsOfTerm t) a = true
  | t, _, _, hlaw, he => by
      cases t <;> first
        | rfl
        | exact Option.isSome_iff_exists.mpr ⟨_, (lawful_literalCodec _ _).retract
            (by simpa [denote] using he)⟩

/-- Object-encode stamps content admission too: every written name whose field is a literal
    carries one of that literal's alternatives.

    `keysOk_of_encode`'s twin, on the other half of the structural test. The quantifier runs
    over the *written* key set, which is what makes an `optional` literal field harmless: a
    name the encode did not write is `keysOk`'s business and never reaches here. -/
theorem literalsOk_of_encode {fields : Finset Name} {ff : {k // k ∈ fields} → ObjectSlot}
    {wild : Option Term}
    {keys : Finset Name} {f : {k // k ∈ keys} → Value} {g : {k // k ∈ keys} → Attr}
    (hfi : funImage (fun k : {k // k ∈ keys} =>
        (entryCodec ⟨fields, fun k => fieldSem (ff k)⟩ (rcOf (wildSem wild)) k.1).bind
          (fun c => c.e (f k))) = some g) :
    literalsOk (Body.spec (.mk fields ff wild))
      keys f = true := by
  simp only [literalsOk, decide_eq_true_eq]
  intro k
  have hw := funImage_some hfi k
  cases hm : decide ((k : Name) ∈ fields) with
  | false =>
      have hk : (k : Name) ∉ fields := of_decide_eq_false hm
      show litOkV (Body.spec (.mk fields ff wild)) k.1 (f k) = true
      rw [litOkV, show (Body.spec (.mk fields ff wild)).names.at k.1 = none from dif_neg hk]
      -- an undeclared name: a closed body never wrote it, and an open block wrote it
      -- through the block's own codec, so the block's alternatives hold
      cases hwild : wild with
      | none => rfl
      | some w =>
        rw [hwild] at hw
        rw [show entryCodec (⟨fields, fun k => fieldSem (ff k)⟩ : MapOf FieldSem)
              (rcOf (wildSem (some w))) k.1 = some (denote w) from by
              simp only [rcOf, wildSem, entryCodec, MapOf.at, dif_neg hk]] at hw
        exact altsOkV_of_term_e (by simpa using hw)
  | true =>
      have hk : (k : Name) ∈ fields := of_decide_eq_true hm
      rw [litOkV, show (Body.spec (.mk fields ff wild)).names.at k.1
          = some ⟨_, altsOfField (ff ⟨k.1, hk⟩)⟩ from dif_pos hk]
      rw [show entryCodec (⟨fields, fun k => fieldSem (ff k)⟩ : MapOf FieldSem)
            (rcOf (wildSem wild)) k.1
          = some (fieldSem (ff ⟨k.1, hk⟩)).codec from by
            simp only [entryCodec, MapOf.at, dif_pos hk]] at hw
      exact litOkV_of_field_e (by simpa using hw)

/-- …and the read side, at the attribute the same encode produced. -/
theorem literalsOkA_of_encode {fields : Finset Name} {ff : {k // k ∈ fields} → ObjectSlot}
    {wild : Option Term} (hlaw : ∀ w : Term, wild = some w → Lawful (denote w))
    {keys : Finset Name} {f : {k // k ∈ keys} → Value} {g : {k // k ∈ keys} → Attr}
    (hfi : funImage (fun k : {k // k ∈ keys} =>
        (entryCodec ⟨fields, fun k => fieldSem (ff k)⟩ (rcOf (wildSem wild)) k.1).bind
          (fun c => c.e (f k))) = some g) :
    literalsOkA (Body.spec (.mk fields ff wild))
      keys g = true := by
  simp only [literalsOkA, decide_eq_true_eq]
  intro k
  have hw := funImage_some hfi k
  cases hm : decide ((k : Name) ∈ fields) with
  | false =>
      have hk : (k : Name) ∉ fields := of_decide_eq_false hm
      show litOkA (Body.spec (.mk fields ff wild)) k.1 (g k) = true
      rw [litOkA, show (Body.spec (.mk fields ff wild)).names.at k.1 = none from dif_neg hk]
      -- the open block's codec wrote this attribute, so the block reads it back
      cases hwild : wild with
      | none => rfl
      | some w =>
        rw [hwild] at hw
        rw [show entryCodec (⟨fields, fun k => fieldSem (ff k)⟩ : MapOf FieldSem)
              (rcOf (wildSem (some w))) k.1 = some (denote w) from by
              simp only [rcOf, wildSem, entryCodec, MapOf.at, dif_neg hk]] at hw
        exact altsOkA_of_term_e (hlaw w hwild) (by simpa using hw)
  | true =>
      have hk : (k : Name) ∈ fields := of_decide_eq_true hm
      rw [litOkA, show (Body.spec (.mk fields ff wild)).names.at k.1
          = some ⟨_, altsOfField (ff ⟨k.1, hk⟩)⟩ from dif_pos hk]
      rw [show entryCodec (⟨fields, fun k => fieldSem (ff k)⟩ : MapOf FieldSem)
            (rcOf (wildSem wild)) k.1
          = some (fieldSem (ff ⟨k.1, hk⟩)).codec from by
            simp only [entryCodec, MapOf.at, dif_pos hk]] at hw
      exact litOkA_of_field_e (by simpa using hw)

/-- A closed option admits its own canonical pairs, on both sides. An *open* object —
    a rest codec — is excluded, as §5 demands: an undeclared name disqualifies the
    option even where its rest codec would hold it. -/
theorem optionSem_self_admit (t : Term)
    (hlawBlock : ∀ fields ff wild, t = .object (.mk fields ff wild) →
      ∀ w : Term, wild = some w → Lawful (denote w))
    (hlaw : Lawful (denote t)) {v a}
    (he : (denote t).e v = some a) :
    (optionSemOf (denote t) (specOf t)).admitV v = true ∧
    (optionSemOf (denote t) (specOf t)).admitA a = true := by
  constructor
  · show ((denote t).e v).isSome = true
    rw [he]; rfl
  · show ((denote t).p a).isSome = true
    rw [hlaw.retract he]; rfl



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

/-! ### A term that admits nothing

    Disjointness of admissible sets is not on its own a discharge, and the reason is a term
    whose set is *empty*: it is disjoint from everything, including from itself, so it would
    separate from options the discharger refuses. `never` is that term. -/


/-- `HNever` holds nothing: it is `False` at every value. -/
theorem hnever_false (v : Value) : ¬ HNever v := id

/-- …so the bottom is disjoint from every held set, and that is how (D) admits it. -/
theorem hdisj_never_left (T : Held) : HDisj HNever T := fun v hv => absurd hv (hnever_false v)

/-- …and on the other side, where the bottom is what the pair is disjoint from. -/
theorem hdisj_never_right (T : Held) : HDisj T HNever := fun v _ hn => hnever_false v hn

/-- **(D) holds against the bottom, on emptiness.** `union([X, never])` is `Typed`: the bottom
    contributes nothing to `HUnion`, so it cannot make the union ambiguous.

    `src/` refuses the pair all the same, and the two sides are not in conflict. The model says
    the union is *well formed*; `src/` says it is *useless*, because an option that admits
    nothing can never be selected, and refuses it as a lint. `.separations.lean` carries that
    divergence as a theorem rather than as prose. -/
theorem dincomp_never_right (T : Held) : DIncomp [T, HNever] :=
  List.pairwise_cons.mpr
    ⟨fun _ hb => by rw [List.mem_singleton] at hb; subst hb; exact hdisj_never_right T,
     List.pairwise_singleton _ _⟩

/-- The same on the other side, where the bottom is the one the disjunct names. -/
theorem dincomp_never_left (T : Held) : DIncomp [HNever, T] :=
  List.pairwise_cons.mpr
    ⟨fun _ hb => by rw [List.mem_singleton] at hb; subst hb; exact hdisj_never_left _,
     List.pairwise_singleton _ _⟩


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
    refine List.forall_mem_map.mpr fun p _ t a he => ?_
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
    ⟨trivial, trivial, trivial⟩ hd

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
theorem uAtCan_of_literalN_disjoint {xs : List WFNumeral}
    (hdisj : List.Pairwise (fun x y => x ≠ y) xs) :
    UAtCan (xs.map (Term.literal .number)) := by
  show UniqueAdmission (semsOf (xs.map (Term.literal .number)))
  have hs : semsOf (xs.map (Term.literal .number))
      = (xs.map (literalCodec .number)).map OptionSem.byAttempt := by
    simp [semsOf, List.map_map, specOf, optionSemOf, denote]
  rw [hs]
  refine uniqueAdmission_of_sharedBase (base := numberCodec) (qs := xs.map (inL .number))
    lawful_numberCodec.core ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun x _ =>
      ⟨literalCodec_e_restrict .number x, literalCodec_p_restrict .number x⟩
  · rw [List.pairwise_map]
    refine hdisj.imp fun h v hv => ?_
    cases v
    case num d =>
      -- `inL`'s `number` row is ungated now, so there is no split: the payload IS the
      -- alternative and the row reads like `string`'s beside it
      simp only [inL, decide_eq_true_eq] at hv
      simp only [inL, decide_eq_false_iff_not]
      exact fun hy => h (hv ▸ hy ▸ rfl)
    all_goals exact Bool.noConfusion hv

/-! ## The other two rows of §5's table

    §5's discharger table has four rows, and until now a reviewer checking it changed
    vocabulary halfway across: two rows are about `UAtCan opts` — a list of
    **terms** — and two are about `UniqueAdmission os`, a list of `OptionSem`.

    The discriminated union's row is gone with its constructor. `(opaque)`'s cannot follow the
    other two, and the reason is worth stating rather than working around: `denote` gives
    `(opaque)` the **fuel-free** `opaqCodecω`, which budgets each input by its own depth and is
    not `altCodec` over any one list of options. Its (U) is therefore a statement about
    `opaqCodec` at a fuel, one level below the term language. That is a fact about `opaque`, not
    a gap in the table. -/

/-! **Row three is gone, and that is the row's answer.** §5 called the discriminated union "the
one union whose (U) is discharged by the rule itself", and the discharge was ~~uAtCan_dunion~~ over
~~semsOfD~~, the option list that rule's denotation used to build. There is no such rule now: a
dissection is a certified `union`, its members are separated by phase *literals* of `Orth`, and
(U) at a sub-selection is `uAtAct_extract`'s premise rather than a row of this table.
~~uAtCan_dunion~~, ~~UAtCanD~~ and ~~semsOfD~~ are deleted rather than restated, which is the
strongest form the row's claim can take. -/

/-- **Row four: `(opaque)`'s (U), unconditionally.** `uniqueAdmission_opaque` asks for the
    recursive option's lawfulness; `lawful_opaqCodec` supplies it, so the row has no
    premises at all. It is stated about `opaqCodec` at a fuel rather than about the term
    `opaque` for the reason given above — `denote` of `opaque` is not a sum over one
    list. -/
theorem uAtCan_opaque {fuel : Nat} :
    UniqueAdmission (opaqOptions (opaqCodec fuel)) :=
  uniqueAdmission_opaque fuel (lawful_opaqCodec fuel)

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
    ¬ UAtCan [Term.literal .string "A", Term.string] := by
  have hA : (denote (Term.literal .string "A")).e (Value.str "A") = some (Attr.s "A") := by
    show (if "A" ∈ ["A"] then some (Attr.s "A") else none) = some (Attr.s "A")
    rw [if_pos (List.mem_cons_self)]
  have hB : (denote (Term.literal .string "A")).e (Value.str "B") = none := by
    show (if "B" ∈ ["A"] then some (Attr.s "B") else none) = none
    rw [if_neg (by simp)]
  refine not_uAtCan_pair (v := .str "A") (a := Attr.s "A") (w := .str "B") hA rfl ?_
  · show ((denote (Term.literal .string "A")).e (Value.str "B")).isSome ≠
      ((denote Term.string).e (Value.str "B")).isSome
    rw [hB]
    exact fun h => nomatch h

/-- **Both options deciding does not discharge (U) either.** Deciding propagates through
    `array`, so `union(array(literal("A")), array(literal("B")))` has it on both sides — and
    both options admit the empty array, which neither literal ever sees. Propagating the
    property through a container does not propagate disjointness of the admissible sets:
    every container admits its empty case. -/
theorem not_uAtCan_array_literals :
    ¬ UAtCan [Term.array (.literal .string "A"), Term.array (.literal .string "B")] := by
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

/-! ### (D) in its held-set form, as the disjointness §5 proposed

`HDisj` (`Typing.lean`) is that predicate: no value is held by two options. `(union)` carries
`DIncomp`, which asks `HDisj` of every pair, as a well-formedness condition. As a discharger of
(U) it is refuted below: the witness satisfies it and still fails (U). One predicate in two
roles, so it is named once. -/

/-- The relabelling adapter: `"B"` on the outside is `"A"` on the inside. -/
def fRel : Value → Value := fun v => match v with | .str "B" => .str "A" | _ => .null

/-- Its inverse on the carriers. -/
def gRel : Value → Value := fun v => match v with | .str "A" => .str "B" | _ => .null

/-- `held(literal("A"), fRel, gRel)` — holds `{"B"}`, stores it as `S "A"`. -/
def tRel : Term := .held (.literal .string "A") fRel gRel

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
  have h := Typed.literal .string "A"
  have hT : HLit .string "A" = fun w => ∃ s, s ∈ ["A"] ∧ w = Value.str s := by
    funext w; simp [HLit]
  rw [hT] at h
  exact h

theorem dDisj_tRel :
    HDisj (fun v => ∃ s, s ∈ ["A"] ∧ v = .str s)
      (fun v => ∃ s, s ∈ ["A"] ∧ fRel v = .str s) := by
  rintro v ⟨s, hs, rfl⟩ ⟨s', hs', hf⟩
  -- `v = "A"`, so `fRel v = null`, which is no string
  have : s = "A" := by simpa using hs
  subst this
  exact nomatch hf

/-- **(D) does not discharge the readable side.** Disjoint held sets, and both options
    admit the attribute `S "A"` — the first reading it to `"A"`, the second to `"B"`. -/
theorem not_uAtCan_literal_held :
    ¬ UAtCan [Term.literal .string "A", tRel] := by
  have hA : (denote (Term.literal .string "A")).e (Value.str "A") = some (Attr.s "A") := by
    show (if "A" ∈ ["A"] then some (Attr.s "A") else none) = some (Attr.s "A")
    rw [if_pos (List.mem_cons_self)]
  refine not_uAtCan_pair_A (v := .str "A") (a := Attr.s "A") (w := .str "A") hA ?_ ?_
  · show (((if "A" ∈ ["A"] then some (Value.str "A") else none).map gRel)).isSome = true
    rw [if_pos (List.mem_cons_self)]
    rfl
  · show ((denote (Term.literal .string "A")).e (Value.str "A")).isSome ≠
      ((denote (Term.literal .string "A")).e (fRel (Value.str "A"))).isSome
    rw [hA]
    show true ≠ ((denote (Term.literal .string "A")).e Value.null).isSome
    exact fun h => nomatch h


end Calculus
