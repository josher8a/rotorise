import Calculus.Meet

/-!
# A `held` over a finite base

A finite base writes a finite enumeration of values. Two bases have this form: `literal k x`,
and `refine t (members k ls)` over a ground `t`. `finAlts` gives the enumeration, and
`Adm_iff_finAlts` states that the base admits exactly the enumeration.

`Adm (held t P f g) v = Adm t (f v) && Adm P v`, so a `held` over a finite base writes the
image under `g` of the enumeration, cut by the caller-side term `P`. The premise is `IsoCancels (denote t) f g`, the premise that
`Obligations` carries at a `held`. The two halves of the premise do different work:

* The first half, `g (f v) = v` where `t` writes `f v`, puts each written value in the image
  (`held_mem_image`).
* The second half, `f (g w) = w` where `t` writes `w`, puts each image in the write domain
  (`Adm_held_of_mem_image`), where `P` admits the image.

`AdmA (held t P f g) a` implies `AdmA t a`, so the read side of a `held` lies inside the read
side of its base.

`heldFinSep` is a decidable separation test for a `held` over a finite base against any term.
The test sends each image and each alternative to the literal that holds that value, and asks
`certPair` of the literal and the other term. `separates_of_heldFinSep` and
`hdisj_of_heldFinSep` state that the test is sound under the first half of the premise.
A value with no literal, such as a list or a map, fails the test. No certificate reads the test.
-/

namespace Calculus

/-- The base of a ground term, and `none` at each other term. -/
def Term.groundKind : Term → Option GroundKind
  | .string => some .string
  | .number => some .number
  | .boolean => some .boolean
  | .binary => some .binary
  | .null => some .null
  | _ => none

/-- **The alternatives of a finite base.** `literal k x` has one alternative. A `refine` of a
    ground base by `members k ls` has the alternatives `ls` when the two bases agree, and no
    alternative when they differ. Each other term answers `none`. -/
def finAlts : Term → Option (Multiset Value)
  | .literal k x => some {k.toValue x}
  | .refine t (.members k ls) =>
      match t.groundKind with
      | some k' => some (if k' = k then ls.1.val.map k.toValue else 0)
      | none => none
  | _ => none

/-- `inL k x` holds exactly the value of the alternative `x`. -/
theorem inL_iff (k : GroundKind) (x : k.Carrier) (w : Value) :
    inL k x w = true ↔ w = k.toValue x := by
  cases k <;> cases w <;> simp [inL, eq_comm]

/-- The value of an alternative is of the base of the alternative. -/
theorem inBase_toValue (k : GroundKind) (x : k.Carrier) : inBase k (k.toValue x) = true := by
  cases k <;> rfl

/-- The value of an alternative is of no other base. -/
theorem inBase_toValue_ne {k k' : GroundKind} (hk : k' ≠ k) (x : k.Carrier) :
    inBase k' (k.toValue x) = false := by
  cases k <;> cases k' <;> first | rfl | exact absurd rfl hk

/-- A ground term admits exactly the values of its base. -/
theorem Adm_ground {t : Term} {k : GroundKind} (h : t.groundKind = some k) (w : Value) :
    Adm t w = inBase k w := by
  cases t <;> simp [Term.groundKind] at h <;> subst h <;> cases w <;> rfl

/-- A member of a set of alternatives is of the base of the set. -/
theorem inBase_of_inLs {k : GroundKind} {ls : NEFinset k.Carrier} {w : Value}
    (h : inLs k ls w = true) : inBase k w = true := by
  obtain ⟨x, _, hx⟩ := of_decide_eq_true h
  rw [(inL_iff k x w).mp hx]; exact inBase_toValue k x

/-- `inLs k ls` holds exactly the values of the alternatives `ls`. -/
theorem inLs_iff (k : GroundKind) (ls : NEFinset k.Carrier) (w : Value) :
    inLs k ls w = true ↔ w ∈ ls.1.val.map k.toValue := by
  rw [Multiset.mem_map]
  constructor
  · intro h
    obtain ⟨x, hx, hw⟩ := of_decide_eq_true h
    exact ⟨x, hx, ((inL_iff k x w).mp hw).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact decide_eq_true ⟨x, hx, (inL_iff k x _).mpr rfl⟩

/-- **A finite base admits exactly its alternatives.** -/
theorem Adm_iff_finAlts {t : Term} {A : Multiset Value} (h : finAlts t = some A) (w : Value) :
    Adm t w = true ↔ w ∈ A := by
  match t, h with
  | .literal k x, h =>
    simp only [finAlts, Option.some.injEq] at h; subst h
    simp only [Adm, AdmLit, Multiset.mem_singleton]
    exact inL_iff k x w
  | .refine t (.members k ls), h =>
    simp only [finAlts] at h
    cases hg : t.groundKind with
    | none => rw [hg] at h; exact nomatch h
    | some k' =>
      rw [hg] at h
      simp only [Option.some.injEq] at h; subst h
      simp only [Adm, Pred.eval, Adm_ground hg, Bool.and_eq_true]
      cases hk : decide (k' = k) with
      | true =>
        have hk' := of_decide_eq_true hk; subst hk'
        rw [if_pos rfl, ← inLs_iff]
        exact ⟨fun h => h.2, fun h => ⟨inBase_of_inLs h, h⟩⟩
      | false =>
        have hk' := of_decide_eq_false hk
        rw [if_neg hk']
        refine ⟨fun ⟨hb, hl⟩ => ?_, fun h0 => absurd h0 (Multiset.notMem_zero w)⟩
        obtain ⟨x, _, hx⟩ := of_decide_eq_true hl
        rw [(inL_iff k x w).mp hx, inBase_toValue_ne hk'] at hb
        exact nomatch hb

/-! ## The write domain of a `held` over a finite base -/

/-- **Each value that the `held` writes is `g` of an alternative.** The proof uses the first
    half of `IsoCancels` only: `g (f v) = v` where the base writes `f v`. -/
theorem held_mem_image {t : Term} {A : Multiset Value} (h : finAlts t = some A)
    {f g : Value → Value} (h1 : ∀ v, ((denote t).e (f v)).isSome → g (f v) = v) {v : Value}
    {P : Term} (hv : Adm (.held t P f g) v = true) : v ∈ A.map g := by
  have ha : Adm t (f v) = true := (Bool.and_eq_true_iff.mp hv).1
  rw [← h1 v ((Adm_exact t (f v)).mp ha)]
  exact Multiset.mem_map_of_mem g ((Adm_iff_finAlts h (f v)).mp ha)

/-- **Under the first half of `IsoCancels`, the write domain is the image filtered by
    admission.** No other half of the premise is read. -/
theorem Adm_held_iff_filter {t : Term} {A : Multiset Value} (h : finAlts t = some A)
    {P : Term} {f g : Value → Value} (h1 : ∀ v, ((denote t).e (f v)).isSome → g (f v) = v)
    (v : Value) :
    Adm (.held t P f g) v = true ↔ v ∈ (A.map g).filter (fun w => Adm (.held t P f g) w = true) := by
  rw [Multiset.mem_filter]
  exact ⟨fun hv => ⟨held_mem_image h h1 hv, hv⟩, fun hv => hv.2⟩

/-- **Each image of an alternative that `P` admits is a value that the `held` writes.** The
    proof uses the second half of `IsoCancels` only: `f (g w) = w` where the base writes `w`. -/
theorem Adm_held_of_mem_image {t : Term} {A : Multiset Value} (h : finAlts t = some A)
    {P : Term} {f g : Value → Value} (h2 : ∀ w, ((denote t).e w).isSome → f (g w) = w)
    {v : Value} (hv : v ∈ A.map g) (hP : Adm P v = true) : Adm (.held t P f g) v = true := by
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hv
  have ha : Adm t w = true := (Adm_iff_finAlts h w).mpr hw
  have hb : Adm t (f (g w)) = true := by rw [h2 w ((Adm_exact t w).mp ha)]; exact ha
  exact Bool.and_eq_true_iff.mpr ⟨hb, hP⟩

/-- **Under `IsoCancels`, the write domain of the `held` is the image of the alternatives,
    cut by `P`.** The filter of `Adm_held_iff_filter` keeps each image that `P` admits, by the
    second half. -/
theorem Adm_held_iff_image {t : Term} {A : Multiset Value} (h : finAlts t = some A)
    {P : Term} {f g : Value → Value} (hi : IsoCancels (denote t) f g) (v : Value) :
    Adm (.held t P f g) v = true ↔ v ∈ A.map g ∧ Adm P v = true :=
  ⟨fun hv => ⟨held_mem_image h hi.1 hv, (Bool.and_eq_true_iff.mp hv).2⟩,
   fun hv => Adm_held_of_mem_image h hi.2 hv.1 hv.2⟩

/-! ## Disjointness on each side -/

/-- No value is written by both terms. -/
def WDisj (x y : Term) : Prop := ∀ v, Adm x v = true → Adm y v = false

/-- No attribute is read by both terms. -/
def RDisj (x y : Term) : Prop := ∀ a, AdmA x a = true → AdmA y a = false

/-- **Disjointness on both sides is the separation that the union row consumes.** -/
theorem separates_of_disj {x y : Term} (hw : WDisj x y) (hr : RDisj x y) : Separates x y :=
  ⟨fun v hx hy => absurd hy.2 (by show ¬ Adm y v = true; rw [hw v hx.2]; exact Bool.false_ne_true),
   fun a hx hy => absurd hy.2 (by show ¬ AdmA y a = true; rw [hr a hx.2]; exact Bool.false_ne_true)⟩

/-- **Write disjointness is disjointness of the held sets**, because the held set of a
    derivable term is its admission (`typed_T_adm`). -/
theorem hdisj_of_wdisj {x y : Term} {Tx Ty : Held} {μx μy : Option Member} (hw : WDisj x y)
    (hx : Typed x Tx μx) (hy : Typed y Ty μy) : HDisj Tx Ty := fun v hvx hvy => by
  have := hw v ((typed_T_adm hx v).mp hvx)
  rw [(typed_T_adm hy v).mp hvy] at this
  exact nomatch this

/-- Separation gives read disjointness, because a read attribute has an occupied member. -/
theorem rdisj_of_separates {x y : Term} (h : Separates x y) : RDisj x y := by
  intro a hx
  cases hy : AdmA y a with
  | false => rfl
  | true => exact absurd ⟨occA_sound y a hy, hy⟩ (h.2 a ⟨occA_sound x a hx, hx⟩)

/-! ## The witness: `union(held(literal "A", P, f, g), literal "B")` -/

/-- The string literal. -/
abbrev litS (s : String) : Term := .literal .string s

/-- **The write sides are disjoint exactly when `g` sends `"A"` to a value other than
    `"B"`.** The forward direction uses the second half of `IsoCancels` and `P` at `g "A"`,
    because the `held` must write `g "A"`. The backward direction uses the first half, because
    each value that the `held` writes must be `g "A"`. -/
theorem witness_wdisj_iff {P : Term} {f g : Value → Value}
    (hi : IsoCancels (denote (litS "A")) f g) (hP : Adm P (g (.str "A")) = true) :
    WDisj (.held (litS "A") P f g) (litS "B") ↔ g (.str "A") ≠ .str "B" := by
  have hA : finAlts (litS "A") = some {.str "A"} := rfl
  have hB : finAlts (litS "B") = some {.str "B"} := rfl
  constructor
  · intro hw he
    have h1 := Adm_held_of_mem_image hA hi.2 (v := g (.str "A")) (by simp) hP
    have h2 := hw _ h1
    rw [he] at h2
    have h3 := (Adm_iff_finAlts hB (.str "B")).mpr (Multiset.mem_singleton_self _)
    rw [h2] at h3; exact nomatch h3
  · intro hne v hv
    have hv' := held_mem_image hA hi.1 hv
    simp only [Multiset.map_singleton, Multiset.mem_singleton] at hv'
    subst hv'
    cases hb : Adm (litS "B") (g (.str "A")) with
    | false => rfl
    | true =>
      have := (Adm_iff_finAlts hB _).mp hb
      exact absurd (Multiset.mem_singleton.mp this) hne

/-- **The read sides are disjoint for every `P`, `f` and `g`.** The `held` reads `S "A"`, and
    the literal reads `S "B"`. No premise is read. -/
theorem witness_rdisj (P : Term) (f g : Value → Value) :
    RDisj (.held (litS "A") P f g) (litS "B") := by
  intro a ha
  have ha' := (Bool.and_eq_true_iff.mp ha).1
  cases a <;> simp_all [AdmA, AdmALit]

/-- The identity pair cancels on every codec. -/
theorem isoCancels_id (c : Codec) : IsoCancels c id id := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- **With `P = literal "A"` and `f = g = id`, the witness is separated on both sides.** -/
theorem witness_id_separates : Separates (.held (litS "A") (litS "A") id id) (litS "B") :=
  separates_of_disj
    ((witness_wdisj_iff (isoCancels_id _) (by simp [Adm, AdmLit])).mpr (by simp))
    (witness_rdisj _ id id)

/-- **A constant `f` violates `IsoCancels`.** The first half makes `g "A"` equal to every
    value, so the premise excludes the ambiguous `held`, and no certificate needs to. -/
theorem not_isoCancels_const (g : Value → Value) :
    ¬ IsoCancels (denote (litS "A")) (fun _ => .str "A") g := by
  intro hi
  have he : ((denote (litS "A")).e (.str "A")).isSome :=
    (Adm_exact (litS "A") (.str "A")).mp (by simp [Adm, AdmLit])
  have h1 := hi.1 .null he
  have h2 := hi.1 (.bool true) he
  rw [h1] at h2; exact nomatch h2

/-- **The current certificate refuses the witness**, because the two options write the slot
    `str` and read the member `S`, and the meet of a `held` answers `none`. -/
theorem unionOk_witness_id : unionOk [.held (litS "A") (litS "A") id id, litS "B"] = false := by
  decide

/-! ## A decidable separation test -/

/-- **The literal that holds one ground value**, and `none` at a value of no ground base. -/
def litOf : Value → Option Term
  | .str s => some (.literal .string s)
  | .num d => some (.literal .number d)
  | .bool b => some (.literal .boolean b)
  | .bin b => some (.literal .binary b)
  | .null => some (.literal .null ())
  | _ => none

/-- The literal of the value of an alternative is the literal of the alternative. -/
theorem litOf_toValue (k : GroundKind) (x : k.Carrier) :
    litOf (k.toValue x) = some (.literal k x) := by
  cases k <;> rfl

/-- The literal of a value admits the value. -/
theorem Adm_litOf {v : Value} {l : Term} (h : litOf v = some l) : Adm l v = true := by
  cases v <;> simp only [litOf, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [Adm, AdmLit]

/-- **`certPair` separates the literal of `v` from `y`.** A value of no ground base fails. -/
def refusesImage (y : Term) (v : Value) : Bool :=
  match litOf v with
  | some l => certPair l y
  | none => false

/-- **A term that refuses the literal of `v` does not write `v`.** -/
theorem Adm_false_of_refusesImage {y : Term} {v : Value} (h : refusesImage y v = true) :
    Adm y v = false := by
  unfold refusesImage at h
  cases hl : litOf v with
  | none => rw [hl] at h; exact nomatch h
  | some l =>
    rw [hl] at h
    have hs := (separates_of_certPair h).1 v
    have hlv := Adm_litOf hl
    cases hy : Adm y v with
    | false => rfl
    | true => exact absurd ⟨occV_sound y v hy, hy⟩ (hs ⟨occV_sound l v hlv, hlv⟩)

/-- **A term that refuses the literal of `v` reads no attribute that the literal reads.** -/
theorem AdmA_false_of_refusesImage {y : Term} {v : Value} {l : Term} (hl : litOf v = some l)
    (h : refusesImage y v = true) {a : Attr} (ha : AdmA l a = true) : AdmA y a = false := by
  unfold refusesImage at h
  rw [hl] at h
  exact rdisj_of_separates (separates_of_certPair h) a ha

/-- A ground term reads each attribute to a value of its base, and the literal of that value
    reads the attribute. -/
theorem ground_read {t : Term} {k' : GroundKind} (hg : t.groundKind = some k') {a : Attr}
    {v : Value} (hp : (denote t).p a = some v) :
    inBase k' v = true ∧ ∀ (k : GroundKind) (x : k.Carrier), v = k.toValue x →
      AdmALit k x a = true := by
  cases t <;> simp only [Term.groundKind, Option.some.injEq, reduceCtorEq] at hg <;> subst hg <;>
    cases a <;>
    simp only [denote, stringCodec, numberCodec, booleanCodec, binaryCodec, nullCodec,
      Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    refine ⟨rfl, fun k x hx => ?_⟩ <;> cases k <;> simp_all [AdmALit]

/-- **A finite base reads only the attributes of its alternatives.** Each attribute that the
    base reads, the literal of some alternative reads. -/
theorem AdmA_finAlts {t : Term} {A : Multiset Value} (h : finAlts t = some A) {a : Attr}
    (ha : AdmA t a = true) : ∃ w ∈ A, ∃ l, litOf w = some l ∧ AdmA l a = true := by
  match t, h with
  | .literal k x, h =>
    simp only [finAlts, Option.some.injEq] at h; subst h
    exact ⟨_, Multiset.mem_singleton_self _, _, litOf_toValue k x, ha⟩
  | .refine t (.members k ls), h =>
    simp only [finAlts] at h
    cases hg : t.groundKind with
    | none => rw [hg] at h; exact nomatch h
    | some k' =>
      rw [hg] at h
      simp only [Option.some.injEq] at h; subst h
      have hr := (Bool.and_eq_true_iff.mp ha).2
      cases hp : (denote t).p a with
      | none => rw [refineReads_none hp] at hr; exact nomatch hr
      | some v =>
        rw [refineReads_some hp] at hr
        obtain ⟨x, hx, hv⟩ := of_decide_eq_true hr
        have hv' := (inL_iff k x v).mp hv
        obtain ⟨hb, hl⟩ := ground_read hg hp
        cases hk : decide (k' = k) with
        | false =>
          rw [hv', inBase_toValue_ne (of_decide_eq_false hk)] at hb; exact nomatch hb
        | true =>
          have hk' := of_decide_eq_true hk; subst hk'
          rw [if_pos rfl]
          exact ⟨_, Multiset.mem_map_of_mem _ hx, _, litOf_toValue _ x, hl _ x hv'⟩

/-- **The test on a finite base, its image and `y`.** `y` refuses the literal of each image
    `g w`, for the write side, and the literal of each alternative `w`, for the read side.
    A base that is not finite fails. -/
def heldImageSep (t : Term) (g : Value → Value) (y : Term) : Bool :=
  match finAlts t with
  | some A => decide (∀ w ∈ A, refusesImage y (g w) = true ∧ refusesImage y w = true)
  | none => false

/-- **The decidable separation test for a `held` against any term.** Each term other than a
    `held` fails. -/
def heldFinSep : Term → Term → Bool
  | .held t _ _ g, y => heldImageSep t g y
  | _, _ => false

/-- **The test gives write disjointness**, under the first half of `IsoCancels`. -/
theorem wdisj_of_heldFinSep {t y P : Term} {f g : Value → Value}
    (h1 : ∀ v, ((denote t).e (f v)).isSome → g (f v) = v)
    (h : heldFinSep (.held t P f g) y = true) : WDisj (.held t P f g) y := by
  change heldImageSep t g y = true at h
  unfold heldImageSep at h
  cases hA : finAlts t with
  | none => rw [hA] at h; exact nomatch h
  | some A =>
    rw [hA] at h
    have hall := of_decide_eq_true h
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp (held_mem_image hA h1 hv)
    exact Adm_false_of_refusesImage (hall w hw).1

/-- **The test gives read disjointness**, with no premise. The `held` reads what its base
    reads, and the base reads only the attributes of its alternatives. -/
theorem rdisj_of_heldFinSep {t y P : Term} {f g : Value → Value}
    (h : heldFinSep (.held t P f g) y = true) : RDisj (.held t P f g) y := by
  change heldImageSep t g y = true at h
  unfold heldImageSep at h
  cases hA : finAlts t with
  | none => rw [hA] at h; exact nomatch h
  | some A =>
    rw [hA] at h
    have hall := of_decide_eq_true h
    intro a ha
    obtain ⟨w, hw, l, hl, hla⟩ := AdmA_finAlts hA (a := a) (Bool.and_eq_true_iff.mp ha).1
    exact AdmA_false_of_refusesImage hl (hall w hw).2 hla

/-- **The test is sound for the union row**, under the first half of `IsoCancels`. -/
theorem separates_of_heldFinSep {t y P : Term} {f g : Value → Value}
    (h1 : ∀ v, ((denote t).e (f v)).isSome → g (f v) = v)
    (h : heldFinSep (.held t P f g) y = true) : Separates (.held t P f g) y :=
  separates_of_disj (wdisj_of_heldFinSep h1 h) (rdisj_of_heldFinSep h)

/-- **The test gives disjoint held sets**, under the first half of `IsoCancels`. -/
theorem hdisj_of_heldFinSep {t y P : Term} {f g : Value → Value} {Tx Ty : Held}
    {μx μy : Option Member} (h1 : ∀ v, ((denote t).e (f v)).isSome → g (f v) = v)
    (h : heldFinSep (.held t P f g) y = true)
    (hx : Typed (.held t P f g) Tx μx) (hy : Typed y Ty μy) : HDisj Tx Ty :=
  hdisj_of_wdisj (wdisj_of_heldFinSep h1 h) hx hy

/-- **The kernel decides the test on the witness.** The test accepts the witness that
    `unionOk` refuses. -/
theorem heldFinSep_witness_id :
    heldFinSep (.held (litS "A") (litS "A") id id) (litS "B") = true := by
  decide

/-- **The test refuses an overlap**: `held(literal "A", literal "A", id, id)` against
    `literal "A"`. -/
theorem heldFinSep_overlap :
    heldFinSep (.held (litS "A") (litS "A") id id) (litS "A") = false := by
  decide

end Calculus
