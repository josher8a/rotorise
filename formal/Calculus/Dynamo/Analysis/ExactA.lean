import Calculus.Dynamo.Analysis.ExactV

/-!
# §5 — exactness on the attribute side

`Adm` is the value half. `AdmA` is the attribute half, and it has no `Adm`-shaped
counterpart, which is the first reason the analysis tables could not simply be tightened.
-/

namespace Calculus

noncomputable section
/-! ## The attribute side

`Adm` is the value half. `AdmA` is the attribute half, and it has no
`Adm`-shaped counterpart — which is the first reason the analysis tables cannot simply be
renamed onto `Adm`. `AdmA` below is that counterpart's definition and its soundness proof.

The mirror is not symmetric, and the asymmetry that remains is §1's rather than this
file's: the numeric rows went through the host's decimal reader, and `refine` narrows a read.
was listed here as a third — "cannot narrow a read" — and is not one: the row decodes and
then applies `q`. Each is a row here rather than a remark. -/

/-! ### The attribute side's rows, and the three that are not the value side's

The attribute side reads the combinators of the value side at the carrier `Attr`. `objRead`
still filters the *stored* names through `keepB`, and the row carries no filter to match it:
`keepB` is the constant `true` at every body, because `drop` was the one policy that dropped a
name and an open block is a codec or nothing. `keepB_wild` states that, and it is what the object proof
spends on the filter. -/

/-- An attribute-side row, once the subterms' rows are known. -/
abbrev AP := Attr → Bool

/-- The current-schema reader has the same required-name guard as the writer. -/
def reqPresentT (fields : Finset Name) (fld : {k // k ∈ fields} → ObjectSlot)
    (keys : Finset Name) : Bool :=
  decide (∀ k : {k // k ∈ fields},
    (match fld k with | .req _ => decide (k.1 ∈ keys) | _ => true) = true)


/-- What the literal codec **reads**, exactly.

    Each row is membership. `N` is carried exactly, so the `number` row compares the payload
    with the literal, as the `string` row does. -/
noncomputable def AdmALit : (k : GroundKind) → k.Carrier → Attr → Bool
  | .string,  y, .s s    => decide (s = y)
  | .boolean, y, .bool b => decide (b = y)
  | .binary,  y, .b b    => decide (b = y)
  | .null,    _, .null   => true
  -- `N` is carried exactly on both sides, so the attribute payload IS the alternative and
  -- this row reads like `string`'s beside it.
  | .number,  y, .n x    => decide (x = y)
  | _, _, _ => false

/-- Whether an attribute is of one ground base's member. -/
def inBaseA : GroundKind → Attr → Bool
  | .string, .s _ | .number, .n _ | .boolean, .bool _ | .binary, .b _ | .null, .null => true
  | _, _ => false

mutual

/-- **The joint admission predicate, attribute side.** The mirror of `Adm` across §1's
    asymmetry, and it is not a symmetric mirror: one row differs in kind, not degree.

    * `refine` **does** narrow here, and the row that said it could not was wrong. "`q` tests the value a read *produces*, and no
      syntactic set of attributes bounds that" is true of syntax and says nothing about a
      row, which may decode and then ask `q` (`refineReads`). Sound, and exact whenever the
      subterm's row is: `dom((c.restrict q).p)` is precisely `{a | ∃ v, c.p a = some v ∧ q v}`.
    An alternate reader is `Codec.extendRead`, outside `Term`, so this table has no
    alternate-reader row. -/
noncomputable def AdmA : Term → Attr → Bool
  | .base k   => inBaseA k
  | .literal k ls => AdmALit k ls
  -- the bottom reads nothing back, and the row is that sentence
  | .never => fun _ => false
  -- the read side of the caller-side restriction: decode, transform, then ask `P`'s row
  | .held t P _ g => fun a => AdmA t a && refineReads t (fun w => Adm P (g w)) a
  | .refine t p => fun a => AdmA t a && refineReads t p.eval a
  -- hatch
  -- the read side of the same disjunction; every option, object included, is admitted by attempt
  | .union opts => fun a => anyP (AdmAList opts) a
  -- **`set` asks its own codec**, for the reason the value side gives: a read over the
  -- elements alone is exact only where the element reads injectively and at one member
  | .set t    => fun a => ((setCodec (denote t)).p a).isSome
  -- **One row**, for the reason the value side gives: `array` and `tuple` were two rows
  -- computing different things on what is now one shape.
  | .list pre sp suf => fun a =>
      match a with
      | .l as => alignPL (AdmAList pre) (AdmAOptT sp) (AdmAList suf) as
      | _ => false
  | .object b => AdmABody b
  -- the read side of the same deferral; see the `Adm` row and `ExactA_opaq`
  | .opaq => fun a => ((muCodec opaqStep).p a).isSome
  -- a closed variable is the bottom, and `mu` asks its own codec, as `opaq` does
  | .var _ => fun _ => false
  | .mu b => fun a => ((denote (.mu b)).p a).isSome

/-- The read side's payload row; `AdmBody`'s mirror. -/
noncomputable def AdmABody : Body → AP
  | .mk fields fld wild => fun a =>
      match a with
      | .m keys g =>
          reqPresentT fields fld keys &&
          objAdmV ⟨fields, fun k => AdmAField (fld k)⟩ (AdmAWild wild) keys g
      | _ => false

noncomputable def AdmAField : ObjectSlot → AP
  | .req t => AdmA t
  | .optional t => AdmA t

noncomputable def AdmAWild : Option Term → Option AP
  | none => none
  | some t => some (AdmA t)

noncomputable def AdmAList : List Term → List AP
  | [] => []
  | t :: ts => AdmA t :: AdmAList ts

noncomputable def AdmAOptT : Option Term → Option AP
  | none => none
  | some t => some (AdmA t)



end

@[simp] theorem AdmAList_eq : ∀ ts : List Term, AdmAList ts = ts.map AdmA
  | [] => rfl
  | t :: ts => by simp only [AdmAList, List.map]; rw [AdmAList_eq ts]



/-- `⋁` of `AdmA` over a union's options; sound, and inexact for the reason the value side
    gives. -/
noncomputable def AdmAAny (ts : List Term) (a : Attr) : Bool := anyP (AdmAList ts) a

@[simp] theorem AdmAAny_nil (a : Attr) : AdmAAny [] a = false := rfl

@[simp] theorem AdmAAny_cons (t : Term) (ts : List Term) (a : Attr) :
    AdmAAny (t :: ts) a = (AdmA t a || AdmAAny ts a) := rfl

theorem AdmA_union (opts : List Term) (a : Attr) :
    AdmA (.union opts) a = AdmAAny opts a := rfl

/-- An option that admits makes the disjunction true. -/
theorem AdmAAny_of_mem {t : Term} {ts : List Term} {a : Attr} (ht : t ∈ ts)
    (h : AdmA t a = true) : AdmAAny ts a = true := by
  induction ts with
  | nil => exact absurd ht (by simp)
  | cons t0 ts ih =>
    rcases List.mem_cons.mp ht with rfl | h'
    · simp [AdmAAny_cons, h]
    · simp [AdmAAny_cons, ih h']

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

/-- `AdmA`'s literal row, named — for the reason `Adm_literal` gives. -/
@[simp] theorem AdmA_literal (k : GroundKind) (x : k.Carrier) (a : Attr) :
    AdmA (.literal k x) a = AdmALit k x a := by unfold AdmA; rfl

/-! The four bases whose stored attribute *is* the value, stated as standalone lemmas with
their carriers written out.

`GroundKind.Carrier` is reducible, so `k.Carrier` at a *constructor* `k` is the same type as
`Bytes` — but it is not the same *expression*, and `simp` inside the goal
re-derives that on every rewrite. At `binary` (`List UInt8`) and `null` (`Unit`) that was
enough to exhaust the heartbeat budget. Taking the carrier as a plain type in the statement
does the reduction once, at elaboration.

`string` and `boolean` are here for the same reason and not because they failed: inline in
`AdmA_exact` they were re-derived inside a twenty-case fan, and the row each one needs is a
statement about *one* base. `AdmA_exact` cites all four and unfolds none. -/

theorem AdmALit_binary_exact (y : Bytes) (a : Attr) :
    AdmA (.literal .binary y) a = true ↔ ((denote (Term.literal .binary y)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          binaryCodec]

theorem AdmALit_null_exact (y : Unit) (a : Attr) :
    AdmA (.literal .null y) a = true ↔ ((denote (Term.literal .null y)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          nullCodec]

/-- `(literal)` at `string`, read side. `String` and not `k.Carrier`: the carrier reduces once
    here instead of on every rewrite. -/
theorem AdmALit_string_exact (y : String) (a : Attr) :
    AdmA (.literal .string y) a = true ↔ ((denote (Term.literal .string y)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          stringCodec]

/-- `(literal)` at `boolean`, read side. Same shape as `AdmALit_string_exact`, and the two
    cannot share a `simp` set — one of them would have to name the other's codec. -/
theorem AdmALit_boolean_exact (y : Bool) (a : Attr) :
    AdmA (.literal .boolean y) a = true ↔ ((denote (Term.literal .boolean y)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          booleanCodec]


/-- The converse direction on the attribute side: the row is `dom(p)`, not a bound on it. -/
def ExactA (t : Term) : Prop := ∀ a, AdmA t a = true ↔ ((denote t).p a).isSome

/-- The read-side agreement, option by option — `isSome_e_eq_Adm`'s twin. -/
theorem isSome_p_eq_AdmA {t : Term} (h : ExactA t) (a : Attr) :
    ((denote t).p a).isSome = AdmA t a := by
  exact Bool.coe_iff_coe.mp (by simpa using (h a).symm)

/-- `select`'s filter is the term list's, mapped — `filter_AdmList`'s twin. -/
theorem filter_AdmAList {opts : List Term} (h : ∀ t ∈ opts, ExactA t) (a : Attr) :
    (denoteList opts).filter (fun c => (c.p a).isSome)
      = (opts.filter (fun t => AdmA t a)).map denote := by
  induction opts with
  | nil => rfl
  | cons t ts ih =>
    have ht : ExactA t := h t (by simp)
    have hts : ∀ t' ∈ ts, ExactA t' := fun t' h' => h t' (by simp [h'])
    simp only [denoteList, List.filter_cons, isSome_p_eq_AdmA ht, ih hts]
    cases hb : AdmA t a <;> simp []

/-- **A union reads exactly where one of its options reads.** -/
theorem select_isSome_attemptA (os : List Codec) (a : Attr) :
    (select os (·.p) a).isSome = true ↔ ∃ o ∈ os, (o.p a).isSome = true := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨o, ho, -, hp⟩ := select_admits hv
    exact ⟨o, ho, by rw [hp]; rfl⟩
  · rintro ⟨o, ho, hp⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨o', hf⟩ := find?_attempt_A ho hv
    unfold select; rw [hf]; exact acts_of_find?_A hf

/-- **`union` reads exactly what its row says** — `ExactV_union` on the other side of the
    pair. -/
theorem ExactA_union {opts : List Term} (h : ∀ t ∈ opts, ExactA t) : ExactA (.union opts) := by
  intro a
  rw [denote_union_sems]
  show AdmAAny opts a = true ↔ (select (denoteList opts) (·.p) a).isSome
  rw [select_isSome_attemptA, denoteList_eq]
  simp only [List.mem_map, exists_exists_and_eq_and]
  constructor
  · intro ha
    induction opts with
    | nil => exact absurd ha (by simp)
    | cons t ts ih =>
      rw [AdmAAny_cons, Bool.or_eq_true] at ha
      rcases ha with ha | ha
      · exact ⟨t, List.mem_cons_self, (h t List.mem_cons_self a).mp ha⟩
      · obtain ⟨t', ht', hp⟩ := ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) ha
        exact ⟨t', List.mem_cons_of_mem _ ht', hp⟩
  · rintro ⟨t, ht, hp⟩
    exact AdmAAny_of_mem ht ((h t ht a).mpr hp)

/-- **`set` reads exactly what its row says**, because the row asks the set's codec. -/
theorem ExactA_set (t : Term) : ExactA (.set t) := fun _ => Iff.rfl

theorem alignPA_iff (tail : Option Term) (htl : ∀ t ∈ tail, ExactA t) :
    ∀ (ts : List Term) (as : List Attr), (∀ t ∈ ts, ExactA t) →
      (alignP (AdmAList ts) (AdmAOptT tail) as = true ↔
        ((align (denoteList ts) (denoteOpt tail) as).bind
          (traverse fun ca => ca.1.p ca.2)).isSome = true)
  | [], [], _ => by
      cases tail <;> simp [alignP, AdmAList, AdmAOptT, align, denoteList, denoteOpt, traverse]
  | [], a :: as, _ => by
      cases htail : tail with
      | none => simp [alignP, AdmAList, AdmAOptT, align, denoteList, denoteOpt]
      | some t =>
        have ht : ExactA t := htl t (by simp [htail])
        have ih := alignPA_iff tail htl [] as (by simp)
        rw [htail] at ih
        simp only [AdmAList, AdmAOptT, denoteList, denoteOpt] at ih
        simp only [alignP, AdmAList, AdmAOptT, align, denoteList, denoteOpt,
          Bool.and_eq_true]
        cases hal : align [] (some (denote t)) as with
        | none =>
          rw [hal] at ih
          simp at ih
          simp [ih]
        | some ps =>
          rw [hal] at ih
          simp only [Option.map_some, Option.bind_some] at ih ⊢
          rw [traverse_cons_isSome, Bool.and_eq_true, ← ht a, ← ih]
  | t :: ts, [], _ => by
      cases tail <;> simp [alignP, AdmAList, AdmAOptT, align, denoteList, denoteOpt]
  | t :: ts, a :: as, h => by
      have ht : ExactA t := h t (by simp)
      have ih := alignPA_iff tail htl ts as (fun t' ht' => h t' (by simp [ht']))
      simp only [alignP, AdmAList, align, denoteList, Bool.and_eq_true]
      cases hal : align (denoteList ts) (denoteOpt tail) as with
      | none =>
        simp only [hal, Option.map_none, Option.bind_none, Option.isSome_none] at ih ⊢
        simp at ih
        simp [ih]
      | some ps =>
        simp only [hal, Option.map_some, Option.bind_some] at ih ⊢
        rw [traverse_cons_isSome, Bool.and_eq_true, ← ht a, ← ih]

/-- The suffix's row, transported across its positions' exactness. The length premise is
    load bearing for the reason `zipP_iff`'s is: `List.zip` truncates. -/
theorem zipPA_iff : ∀ (suf : List Term), (∀ t ∈ suf, ExactA t) → ∀ (back : List Attr),
    back.length = suf.length →
    (zipP (AdmAList suf) back = true ↔
      (traverse (fun ca : Codec × Attr => ca.1.p ca.2)
        ((denoteList suf).zip back)).isSome = true)
  | [], _, [], _ => by simp [zipP, AdmAList, denoteList]
  | [], _, _ :: _, h => by
      exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _, _, [], h => by
      exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | t :: ts, h, a :: as, hlen => by
      simp only [AdmAList, denoteList, zipP, List.zip_cons_cons, Bool.and_eq_true,
        traverse_cons_isSome]
      rw [zipPA_iff ts (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) as
          (by simp only [List.length_cons] at hlen; omega),
        h t List.mem_cons_self a]

/-- **`alignPL` is `alignL`'s row on the read side.** -/
theorem alignPAL_iff (pre : List Term) (sp : Option Term) (suf : List Term)
    (hpre : ∀ t ∈ pre, ExactA t) (hsp : ∀ t ∈ sp, ExactA t) (hsuf : ∀ t ∈ suf, ExactA t)
    (as : List Attr) :
    alignPL (AdmAList pre) (AdmAOptT sp) (AdmAList suf) as = true ↔
      ((alignL (denoteList pre) (denoteOpt sp) (denoteList suf) as).bind
        (traverse fun ca => ca.1.p ca.2)).isSome = true := by
  have hlenA : (AdmAList suf).length = suf.length := by simp
  have hlenD : (denoteList suf).length = suf.length := by simp
  unfold alignPL
  rw [hlenA]
  rcases Nat.lt_or_ge as.length suf.length with hlt | hge
  · rw [alignL_short _ _ _ _ (by omega)]
    have h0 : as.length - suf.length = 0 := by omega
    rw [h0, List.drop_zero]
    refine ⟨fun hc => ?_, fun hc => nomatch hc⟩
    have := zipP_length _ _ (Bool.and_eq_true .. ▸ hc |>.2)
    rw [hlenA] at this
    omega
  · rw [alignL_eq_split _ _ _ _ (by omega), hlenD]
    rw [Bool.and_eq_true, alignPA_iff sp hsp pre (as.take (as.length - suf.length)) hpre,
      zipPA_iff suf hsuf _ (by simp; omega)]
    cases hal : align (denoteList pre) (denoteOpt sp) (as.take (as.length - suf.length)) with
    | none => simp
    | some ps => simp [traverse_append_isSome]

/-- **`list` reads exactly** once its three parts do. -/
theorem ExactA_list {pre : List Term} {sp : Option Term} {suf : List Term}
    (hpre : ∀ t ∈ pre, ExactA t) (hsp : ∀ t ∈ sp, ExactA t) (hsuf : ∀ t ∈ suf, ExactA t) :
    ExactA (.list pre sp suf) := by
  intro a
  cases a
  case l as =>
    show alignPL (AdmAList pre) (AdmAOptT sp) (AdmAList suf) as = true ↔
      (((alignL (denoteList pre) (denoteOpt sp) (denoteList suf) as).bind
        (traverse fun ca => ca.1.p ca.2)).map Value.arr).isSome = true
    rw [alignPAL_iff pre sp suf hpre hsp hsuf as]
    cases (alignL (denoteList pre) (denoteOpt sp) (denoteList suf) as).bind
      (traverse fun ca => ca.1.p ca.2) <;> simp
  all_goals simp [AdmA, denote, listCodec, Alg.listCodec, carriedCodec, arrV, lA]

theorem ExactA_tuple {ts : List Term} {tail : Option Term}
    (h : ∀ t ∈ ts, ExactA t) (htl : ∀ t ∈ tail, ExactA t) : ExactA (.tuple ts tail) :=
  ExactA_list h htl (by simp)

/-- **`array` reads exactly** once its element does. -/
theorem ExactA_array {c : Term} (hc : ExactA c) : ExactA (.array c) :=
  ExactA_list (by simp) (by simpa using hc) (by simp)

def ExactAField (fd : ObjectSlot) : Prop :=
  ∀ a, AdmAField fd a = true ↔ (((fieldSem fd).codec).p a).isSome

theorem reqPresentT_eq (fields : Finset Name) (fld : {k // k ∈ fields} → ObjectSlot)
    (keys : Finset Name) :
    reqPresentT fields fld keys = reqPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys := by
  simp only [reqPresentT, reqPresentB]
  congr 1
  apply propext
  constructor <;> intro h k <;> have := h k <;>
    (cases hfd : fld k with
      | req t => simp_all [reqPresentAt, fieldSem]
      | optional t => simp_all [reqPresentAt, fieldSem])

/-- **The read side keeps every stored name.** `drop` was the one policy that dropped one,
    and it is gone, so `objRead`'s filter is the identity on the key set and the row owes it
    nothing. -/
theorem keepB_wild (wild : Option Term) (sems : MapOf FieldSem) (k : Name) {ρ : List Codec} :
    keepB (wildSem wild ρ) sems k = true := by
  cases wild with
  | none => rfl
  | some pt => rfl

theorem entryA_iff {fields : Finset Name} {fld : {k // k ∈ fields} → ObjectSlot}
    {wild : Option Term}
    (hf : ∀ k : {k // k ∈ fields}, ExactAField (fld k))
    (hr : ∀ t, wild = some t → ExactA t) (k : Name) (a : Attr) :
    (entryP ⟨fields, fun k => AdmAField (fld k)⟩ (AdmAWild wild) k).any (· a) = true ↔
    ((entryCodec ⟨fields, fun k => fieldSem (fld k)⟩ (rcOf (wildSem wild)) k).bind
      (fun c => c.p a)).isSome = true := by
  simp only [entryP, entryCodec, MapOf.at]
  by_cases hk : k ∈ fields
  · rw [dif_pos hk, dif_pos hk]
    simpa using hf ⟨k, hk⟩ a
  · rw [dif_neg hk, dif_neg hk]
    cases wild with
    | none => simp [AdmAWild, wildSem, rcOf]
    | some pt => simpa [AdmAWild, wildSem, rcOf] using hr pt rfl a

theorem ExactA_object {fields : Finset Name} {fld : {k // k ∈ fields} → ObjectSlot}
    {wild : Option Term}
    (hf : ∀ k : {k // k ∈ fields}, ExactAField (fld k))
    (hr : ∀ t, wild = some t → ExactA t) :
    ExactA (.object (.mk fields fld wild)) := by
  intro a
  cases a
  case m keys g =>
    show (reqPresentT fields fld keys &&
        objAdmV ⟨fields, fun k => AdmAField (fld k)⟩ (AdmAWild wild) keys g) = true ↔
      ((objectCodec ⟨fields, fun k => fieldSem (fld k)⟩ (wildSem wild)).p (.m keys g)).isSome
        = true
    rw [reqPresentT_eq]
    simp only [objectCodec, Alg.objectCodec, Alg.objectCodecCore, carriedCodec, mA, objRead,
      objAdmV, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_map,
      Option.bind_some]
    by_cases hv : reqPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys = true
    · rw [if_pos hv]
      simp only [hv, true_and, Option.isSome_map, funImage_isSome_iff]
      constructor
      · intro h k
        exact (entryA_iff hf hr k.1 _).mp (h ⟨k.1, (Finset.mem_filter.mp k.2).1⟩)
      · intro h k
        refine (entryA_iff hf hr k.1 (g k)).mpr ?_
        have hmem : k.1 ∈ keys.filter (keepB (wildSem wild) ⟨fields, fun k => fieldSem (fld k)⟩ ·) :=
          Finset.mem_filter.mpr ⟨k.2, keepB_wild wild _ k.1⟩
        exact h ⟨k.1, hmem⟩
    · rw [if_neg hv]
      simp [hv]
  all_goals
    simp [AdmA, AdmABody, denote, bodySem, objectCodec, Alg.objectCodec, Alg.objectCodecCore,
        carriedCodec, mA]

/-- **`opaque` reads exactly what its row says**, definitionally, and for the reason
    `ExactV_opaq` gives at length: `p := (muCodec opaqStep).p`, so the row and `dom(p)` are
    one function. ~~AdmOpaqA_iff~~ — a second induction, this one carrying an injectivity
    clause about the host's decimal reader that `decSet` needs — is deleted rather than moved. The
    clause was true and is still true; it is now the codec's business, where it was always
    stated (`decSet`, `Products.lean`), instead of being restated here in a form that had
    to be kept in step by hand. -/
theorem ExactA_opaq : ExactA .opaq := fun _ => Iff.rfl


def ExactAL : List Term → Prop
  | [] => True
  | t :: ts => ExactA t ∧ ExactAL ts

def ExactAO : Option Term → Prop
  | none => True
  | some t => ExactA t

def ExactAW : Option Term → Prop
  | none => True
  | some t => ExactA t

theorem exactAL_mem : ∀ (ts : List Term), ExactAL ts → ∀ t ∈ ts, ExactA t
  | [], _, t, ht => absurd ht (by simp)
  | t0 :: ts, h, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact h.1
      · exact exactAL_mem ts h.2 t ht'

theorem exactAO_mem : ∀ (tail : Option Term), ExactAO tail → ∀ t ∈ tail, ExactA t
  | none, _, t, ht => absurd ht (by simp)
  | some t0, h, t, ht => by
      have heq : t0 = t := by simpa using ht
      subst heq; exact h

theorem exactAW_codec : ∀ (wild : Option Term), ExactAW wild →
    ∀ t, wild = some t → ExactA t
  | none, _, t, h => nomatch h
  | some t0, h, t, hc => by
      simp only [Option.some.injEq] at hc
      exact hc ▸ h

/-- `allP` transported across the entry's exactness. -/
theorem AdmAAll_iff {c : Term} (h : ExactA c) : ∀ as : List Attr,
    allP (AdmA c) as = true ↔ ∀ a ∈ as, ((denote c).p a).isSome = true := by
  intro as; induction as with
  | nil => simp [allP]
  | cons a as ih => simp [allP, ih, h a]

mutual
/-- **Every attribute row is exact** — all twenty-one, as on the value side, and nothing
    declines on either. `refine` was the last difference between
    the two sides and is exact now: its row decodes and then applies `q`.
    which used to be the other half of that asymmetry, is exact here because its row is the
    union of the two channels it reads on.

    The numeric rows are the interesting ones: they reach `dom(p)` through the host's decimal reader,
    which is axiomatized, and are exact anyway — a row may *call* an axiomatized function
    even though no finite set of numerals describes its domain. §5 wrote `⊤` there. -/
theorem AdmA_exact : ∀ (t : Term), ExactA t
  -- the rows §5 excused on this side too
  | .list pre sp suf =>
      ExactA_list (exactAL_mem pre (AdmA_exactL pre)) (exactAO_mem sp (AdmA_exactO sp))
        (exactAL_mem suf (AdmA_exactL suf))
  | .object b => AdmA_exactB b
  | .opaq => ExactA_opaq
  -- both sides are empty, so the equivalence is `False ↔ False`
  | .never => fun _ => Iff.rfl
  | .var _ => fun _ => Iff.rfl
  | .mu _ => fun _ => Iff.rfl
  -- exact because the constructor narrowed, not because the row sharpened
  | .set t => ExactA_set t
  -- see `ExactA_union`
  | .union opts => ExactA_union (exactAL_mem opts (AdmA_exactL opts))

  | .base k => by
      intro a; cases k <;> cases a <;> simp [AdmA, inBaseA, denote, stringCodec, numberCodec,
        booleanCodec, binaryCodec, nullCodec]
  -- Three rows into one, and `number`'s no longer needs the host lookup that used to make it
  -- the awkward one: both numeric bases now read the attribute payload directly.
  | .literal k ls => by
      intro a
      cases k
      case number =>
        cases a
        case n x =>
          -- `numberCodec.p` is a constructor wrapper now, so the host's decimal reader bind and the
          -- `Numeral.WF` gate this used to walk through are both gone and the row is the
          -- payload comparison on both sides
          rw [show (denote (Term.literal .number ls)).p (.n x)
                 = (literalCodec .number ls).p (.n x) from rfl,
             literalNCodec_p_n, numberCodec_p_n]
          simp [AdmALit, inL]
        -- for every other attribute the base's own read is `none` by a match, so this is
        -- `rfl` once `AdmA`'s recursion is unfolded
        all_goals (simp only [AdmA_literal, AdmALit]; rfl)
      -- the four bases whose stored attribute *is* the value, one tight simp set each: a
      -- shared set has to mention every base's codec, and one of those is `number`
      case string => exact AdmALit_string_exact ls a
      case boolean => exact AdmALit_boolean_exact ls a
      case binary => exact AdmALit_binary_exact ls a
      case null => exact AdmALit_null_exact ls a
  | .held c P f g => by
      have hc := AdmA_exact c
      have hP := Adm_exact P
      intro a
      simp only [AdmA, refineReads, denote_held, Alg.Codec.restrict, Alg.Codec.through,
        Bool.and_eq_true, hc a]
      cases (denote c).p a with
      | none => simp
      | some w => simpa using Bool.eq_iff_iff.mpr (hP (g w))
  -- **the row this file said could not exist.** `restrict`'s `p` is the base's `bind`ed
  -- through `q`, so `dom(p)` is `dom` of the base's intersected with `q` of what it decodes
  -- to — and that is what the row computes, term for term.
  | .refine c p => by
      have hc := AdmA_exact c
      intro a
      simp only [AdmA, refineReads, denote_refine, Alg.Codec.restrict, Bool.and_eq_true, hc a]
      cases hx : (denote c).p a <;> simp []

/-- …and its read-side twin, for the reason the write side gives. -/
theorem AdmA_exactB : ∀ (b : Body), ExactA (.object b)
  | .mk _ fld wild =>
      ExactA_object (fun k => AdmA_exactF (fld k)) (exactAW_codec wild (AdmA_exactW wild))

theorem AdmA_exactL : ∀ (ts : List Term), ExactAL ts
  | [] => trivial
  | t0 :: ts => ⟨AdmA_exact t0, AdmA_exactL ts⟩

theorem AdmA_exactO : ∀ (tail : Option Term), ExactAO tail
  | none => trivial
  | some t0 => AdmA_exact t0

/-- Each current-schema slot reads exactly through its carried term. -/
theorem AdmA_exactF : ∀ (fd : ObjectSlot), ExactAField fd
  | .req t0 => fun a => AdmA_exact t0 a
  | .optional t0 => fun a => AdmA_exact t0 a

theorem AdmA_exactW : ∀ (wild : Option Term), ExactAW wild
  | none => trivial
  | some t0 => AdmA_exact t0
end

/-! ### The same equation on the read side

The value side needs only `AdmWild`, which is `none` exactly where the body declares no open
block. The read side reads the block the same way: an undeclared name under a closed body is
refused, and each name's own presence pair handles a declared absent name. -/

/-- `AdmABody` at a map, unfolded. -/
theorem AdmABody_map {b : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Attr} :
    AdmABody b (.m keys g)
      = (reqPresentT b.fields b.at keys &&
         objAdmV ⟨b.fields, fun k => AdmAField (b.at k)⟩ (AdmAWild b.wild) keys g) := by
  cases b; rfl

/-- One entry of the read-side object row — `objAdmV_row`'s twin. It took a keep filter as a
    hypothesis while `drop` made the two sides' filters differ; they do not differ now. -/
theorem objAdmA_row {c : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hB : objAdmV ⟨c.fields, fun k => AdmAField (c.at k)⟩ (AdmAWild c.wild) keys g = true)
    {k : Name} (hk : k ∈ keys) (hc : k ∈ c.fields) :
    AdmAField (c.at ⟨k, hc⟩) (g ⟨k, hk⟩) = true := by
  unfold objAdmV at hB
  have hh := of_decide_eq_true hB ⟨k, hk⟩
  rwa [entryP, MapOf.at, dif_pos hc] at hh

/-- A present name the body does not declare goes through the open block, on the read side.
    `objAdmV_wild`'s twin. -/
theorem objAdmA_wild {c : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hB : objAdmV ⟨c.fields, fun k => AdmAField (c.at k)⟩ (AdmAWild c.wild) keys g = true)
    {k : Name} (hk : k ∈ keys) (hnc : k ∉ c.fields) {w : Term}
    (hw : c.wild = some w) : AdmA w (g ⟨k, hk⟩) = true := by
  unfold objAdmV at hB
  have hh := of_decide_eq_true hB ⟨k, hk⟩
  rwa [entryP, MapOf.at, dif_neg hnc, hw, AdmAWild] at hh

/-- Soundness of every attribute row — a corollary, as on the value side. The
    hundred-and-thirty-line depth recursion this was, and the ~~SoundA~~ scaffolding it needed,
    are deleted: `AdmA_exact` carries no hypothesis, so the weaker half comes free. -/
theorem AdmA_sound (t : Term) {a v} (hp : (denote t).p a = some v) : AdmA t a = true :=
  (AdmA_exact t a).mpr (by rw [hp]; rfl)

/-- **The witness that is now a theorem the other way.** `refine(string, ⊥)` reads nothing,
    and `AdmA` says so: the row decodes with `stringCodec` and applies `⊥`. This used to be
    ~~not_ExactA_refine~~, stated as "`AdmA` cannot see it". -/
theorem AdmA_refine_bot (a : Attr) : AdmA (.refine .string (.closure (fun _ => false))) a = false := by
  simp [AdmA, refineReads, Pred.eval]
  cases a <;> simp [denote, stringCodec]

end

end Calculus
