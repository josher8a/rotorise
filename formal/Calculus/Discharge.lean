import Calculus.Soundness

/-!
# Admission lemmas shared by the exactness proofs

`refine`'s read-side gate, and the lemmas that show an option admits its own canonical pairs.
`ExactV.lean` and `ExactA.lean` read them.
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
    named member, an admitted attribute carries that member — §5's read-side (W). -/
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

/-- A premise of the form `∀ t ∈ [x, y], P t`, checked at the two options. -/
theorem forall_mem_pair {α : Type} {P : α → Prop} {x y : α} (hx : P x) (hy : P y) :
    ∀ z ∈ [x, y], P z := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hx
  · rcases List.mem_cons.mp hz with rfl | hz
    · exact hy
    · exact absurd hz (by simp)

end Calculus
