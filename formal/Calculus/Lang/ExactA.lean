import Calculus.Lang.ExactV

/-!
# Exactness on the attribute side, over a universe signature

`AdmA` is the attribute half of `Adm`: a row per constructor that equals `dom(p)` of
`denote t`. `refine` and `held` decode and then ask the predicate or the caller-side row of what
the read produces (`refineReads`). A universe supplies the row of each primitive and its
exactness (`PrimAdmA`), and nothing else.
-/

namespace Calculus.Alg

/-- **The attribute-side row of each primitive**, and its exactness. -/
class PrimAdmA (S : Syn) [Sem S] where
  /-- The attributes that a primitive reads. -/
  admA : S.Ground → Sem.A S → Bool
  /-- The row is the read domain of the primitive's codec. -/
  admA_exact : ∀ g a, admA g a = true ↔ ((Sem.ground g).p a).isSome = true

variable {S : Syn} {α : Table S}

/-- **A sum reads exactly where one of its options reads.** -/
theorem select_isSome_attemptA {V A M : Type} (os : List (Codec V A M)) (a : A) :
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

variable [Sem S]

variable (α) in
/-- **`refine`'s read-side gate**: decode with the base, then apply `q` to what comes out. -/
noncomputable def refineReads (t : Term S) (ρ : List S.C) (q : S.V → Bool) (a : Sem.A S) :
    Bool :=
  match (denote α t ρ).p a with
  | some v => q v
  | none => false

theorem valPresentT_eq_reqPresentB (fields : Finset String) (fld : {k // k ∈ fields} → ObjectSlot S)
    (keys : Finset String) {ρ : List S.C} :
    valPresentT fields fld keys = reqPresentB ⟨fields, fun k => fieldSem α (fld k) ρ⟩ keys := by
  simp only [valPresentT, reqPresentB]
  congr 1
  apply propext
  constructor <;> intro h k <;> have := h k <;>
    (cases hfd : fld k with
      | req t => simp_all [valPresentAt, fieldSem]
      | optional t => simp_all [valPresentAt, fieldSem])

/-- **The read side keeps every stored name.** An open block is a codec or nothing, so
    `objRead`'s filter is the identity on the key set, and the row owes it nothing. -/
theorem keepB_wild (wild : Option (Term S)) (sems : MapOf (FieldSem S.V (Sem.A S) (Sem.M S)))
    (k : String) {ρ : List S.C} : keepB (wildSem α wild ρ) sems k = true := by
  cases wild with
  | none => rfl
  | some pt => rfl

variable [PrimAdm S] [PrimAdmA S]

noncomputable section

variable (α) in
mutual

/-- **The joint admission predicate, attribute side**, under an environment `ρ`, as `Adm`.
    `refine` and `held` decode and then ask what the read produces. -/
def AdmA : Term S → List S.C → Sem.A S → Bool
  | .prim g, _ => PrimAdmA.admA g
  | .never, _ => fun _ => false
  | .held t P k, ρ => fun a => AdmA t ρ a && refineReads α t ρ (fun w => Adm α P ρ ((α.word k).2 w)) a
  | .refine t p, ρ => fun a => AdmA t ρ a && refineReads α t ρ (Sem.eval p) a
  | .union opts, ρ => fun a => anyP (AdmAList opts ρ) a
  | .set t, ρ => fun a => ((denote α (.set t) ρ).p a).isSome
  | .list pre sp suf, ρ => fun a =>
      match Sem.list (S := S) with
      | some L =>
          match L.pA.out a with
          | some as => alignPL (AdmAList pre ρ) (AdmAOptT sp ρ) (AdmAList suf ρ) as
          | none => false
      | none => false
  | .object b, ρ => AdmABody b ρ
  | .opaq, _ => fun a => ((Sem.top (S := S)).p a).isSome
  | .var i, ρ => fun a => ((envAt ρ i).p a).isSome
  | .mu b, ρ => fun a => ((denote α (.mu b) ρ).p a).isSome

/-- The read side's payload row; `AdmBody`'s mirror. -/
def AdmABody : Body S → List S.C → Sem.A S → Bool
  | .mk fields fld wild, ρ => fun a =>
      match Sem.map (S := S) with
      | some F =>
          match F.mA.out a with
          | some m =>
              valPresentT fields fld m.keys &&
              objAdmV ⟨fields, fun k => AdmAField (fld k) ρ⟩ (AdmAWild wild ρ) m.keys m.get
          | none => false
      | none => false

def AdmAField : ObjectSlot S → List S.C → Sem.A S → Bool
  | .req t, ρ => AdmA t ρ
  | .optional t, ρ => AdmA t ρ

def AdmAWild : Option (Term S) → List S.C → Option (Sem.A S → Bool)
  | none, _ => none
  | some t, ρ => some (AdmA t ρ)

def AdmAList : List (Term S) → List S.C → List (Sem.A S → Bool)
  | [], _ => []
  | t :: ts, ρ => AdmA t ρ :: AdmAList ts ρ

def AdmAOptT : Option (Term S) → List S.C → Option (Sem.A S → Bool)
  | none, _ => none
  | some t, ρ => some (AdmA t ρ)

end

@[simp] theorem AdmAList_eq (ρ : List S.C) :
    ∀ ts : List (Term S), AdmAList α ts ρ = ts.map (AdmA α · ρ)
  | [] => rfl
  | t :: ts => by simp only [AdmAList, List.map]; rw [AdmAList_eq ρ ts]

variable (α) in
/-- The row is `dom(p)`, not a bound on it, under the environment `ρ`. -/
def ExactA (t : Term S) (ρ : List S.C) : Prop :=
  ∀ a, AdmA α t ρ a = true ↔ ((denote α t ρ).p a).isSome

variable {ρ : List S.C}

theorem alignPA_iff (tail : Option (Term S)) (htl : ∀ t ∈ tail, ExactA α t ρ) :
    ∀ (ts : List (Term S)) (as : List (Sem.A S)), (∀ t ∈ ts, ExactA α t ρ) →
      (alignP (AdmAList α ts ρ) (AdmAOptT α tail ρ) as = true ↔
        ((align (denoteList α ts ρ) (denoteOpt α tail ρ) as).bind
          (traverse fun ca => ca.1.p ca.2)).isSome = true)
  | [], [], _ => by
      cases tail <;> simp [alignP, AdmAList, AdmAOptT, align, denoteList, denoteOpt, traverse]
  | [], a :: as, _ => by
      cases htail : tail with
      | none => simp [alignP, AdmAList, AdmAOptT, align, denoteList, denoteOpt]
      | some t =>
        have ht : ExactA α t ρ := htl t (by simp [htail])
        have ih := alignPA_iff tail htl [] as (by simp)
        rw [htail] at ih
        simp only [AdmAList, AdmAOptT, denoteList, denoteOpt] at ih
        simp only [alignP, AdmAList, AdmAOptT, align, denoteList, denoteOpt,
          Bool.and_eq_true]
        cases hal : align [] (some (denote α t ρ)) as with
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
      have ht : ExactA α t ρ := h t (by simp)
      have ih := alignPA_iff tail htl ts as (fun t' ht' => h t' (by simp [ht']))
      simp only [alignP, AdmAList, align, denoteList, Bool.and_eq_true]
      cases hal : align (denoteList α ts ρ) (denoteOpt α tail ρ) as with
      | none =>
        simp only [hal, Option.map_none, Option.bind_none, Option.isSome_none] at ih ⊢
        simp at ih
        simp [ih]
      | some ps =>
        simp only [hal, Option.map_some, Option.bind_some] at ih ⊢
        rw [traverse_cons_isSome, Bool.and_eq_true, ← ht a, ← ih]

/-- The suffix's row, transported across its positions' exactness. The length premise is
    load bearing for the reason `zipP_iff`'s is: `List.zip` truncates. -/
theorem zipPA_iff : ∀ (suf : List (Term S)), (∀ t ∈ suf, ExactA α t ρ) → ∀ (back : List (Sem.A S)),
    back.length = suf.length →
    (zipP (AdmAList α suf ρ) back = true ↔
      (traverse (fun ca : S.C × Sem.A S => ca.1.p ca.2)
        ((denoteList α suf ρ).zip back)).isSome = true)
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
theorem alignPAL_iff (pre : List (Term S)) (sp : Option (Term S)) (suf : List (Term S))
    (hpre : ∀ t ∈ pre, ExactA α t ρ) (hsp : ∀ t ∈ sp, ExactA α t ρ) (hsuf : ∀ t ∈ suf, ExactA α t ρ)
    (as : List (Sem.A S)) :
    alignPL (AdmAList α pre ρ) (AdmAOptT α sp ρ) (AdmAList α suf ρ) as = true ↔
      ((alignL (denoteList α pre ρ) (denoteOpt α sp ρ) (denoteList α suf ρ) as).bind
        (traverse fun ca => ca.1.p ca.2)).isSome = true := by
  have hlenA : (AdmAList α suf ρ).length = suf.length := by simp
  have hlenD : (denoteList α suf ρ).length = suf.length := by simp
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
    cases hal : align (denoteList α pre ρ) (denoteOpt α sp ρ) (as.take (as.length - suf.length)) with
    | none => simp
    | some ps => simp [traverse_append_isSome]

/-- **`list` reads exactly** once its three parts do. -/
theorem ExactA_list {pre : List (Term S)} {sp : Option (Term S)} {suf : List (Term S)}
    (hpre : ∀ t ∈ pre, ExactA α t ρ) (hsp : ∀ t ∈ sp, ExactA α t ρ) (hsuf : ∀ t ∈ suf, ExactA α t ρ) :
    ExactA α (.list pre sp suf) ρ := by
  intro a
  simp only [AdmA, denote]
  cases Sem.list (S := S) with
  | none => simp [Codec.empty]
  | some L =>
    simp only [listCodec, carriedCodec]
    cases L.pA.out a with
    | none => simp
    | some as =>
      simp only [Option.bind_some, Option.isSome_map]
      exact alignPAL_iff pre sp suf hpre hsp hsuf as

variable (α) in
def ExactAField (fd : ObjectSlot S) (ρ : List S.C) : Prop :=
  ∀ a, AdmAField α fd ρ a = true ↔ (((fieldSem α fd ρ).codec).p a).isSome

theorem entryA_iff {fields : Finset String} {fld : {k // k ∈ fields} → ObjectSlot S}
    {wild : Option (Term S)}
    (hf : ∀ k : {k // k ∈ fields}, ExactAField α (fld k) ρ)
    (hr : ∀ t, wild = some t → ExactA α t ρ) (k : String) (a : Sem.A S) :
    (entryP ⟨fields, fun k => AdmAField α (fld k) ρ⟩ (AdmAWild α wild ρ) k).any (· a) = true ↔
    ((entryCodec ⟨fields, fun k => fieldSem α (fld k) ρ⟩ (rcOf (wildSem α wild ρ)) k).bind
      (fun c => c.p a)).isSome = true := by
  simp only [entryP, entryCodec, MapOf.at]
  by_cases hk : k ∈ fields
  · rw [dif_pos hk, dif_pos hk]
    simpa using hf ⟨k, hk⟩ a
  · rw [dif_neg hk, dif_neg hk]
    cases wild with
    | none => simp [AdmAWild, wildSem, rcOf]
    | some pt => simpa [AdmAWild, wildSem, rcOf] using hr pt rfl a

theorem ExactA_object {fields : Finset String} {fld : {k // k ∈ fields} → ObjectSlot S}
    {wild : Option (Term S)}
    (hf : ∀ k : {k // k ∈ fields}, ExactAField α (fld k) ρ)
    (hr : ∀ t, wild = some t → ExactA α t ρ) :
    ExactA α (.object (.mk fields fld wild)) ρ := by
  intro a
  simp only [AdmA, AdmABody, denote, bodySem]
  cases Sem.map (S := S) with
  | none => simp [Codec.empty]
  | some F =>
    simp only [objectCodec, objectCodecCore, carriedCodec]
    cases F.mA.out a with
    | none => simp
    | some m =>
      simp only [Option.bind_some, Option.isSome_map]
      rw [valPresentT_eq_reqPresentB (α := α) (ρ := ρ)]
      simp only [objRead, objAdmV, Bool.and_eq_true, decide_eq_true_eq]
      by_cases hv : reqPresentB ⟨fields, fun k => fieldSem α (fld k) ρ⟩ m.keys = true
      · rw [if_pos hv]
        simp only [hv, true_and, Option.isSome_map, funImage_isSome_iff]
        constructor
        · intro h k
          exact (entryA_iff hf hr k.1 _).mp (h ⟨k.1, (Finset.mem_filter.mp k.2).1⟩)
        · intro h k
          refine (entryA_iff hf hr k.1 (m.get k)).mpr ?_
          have hmem : k.1 ∈ m.keys.filter
              (keepB (wildSem α wild ρ) ⟨fields, fun k => fieldSem α (fld k) ρ⟩ ·) :=
            Finset.mem_filter.mpr ⟨k.2, keepB_wild wild _ k.1⟩
          exact h ⟨k.1, hmem⟩
      · rw [if_neg hv]
        simp [hv]

/-- **`union` reads exactly what its row says**. -/
theorem ExactA_union {opts : List (Term S)} (h : ∀ t ∈ opts, ExactA α t ρ) :
    ExactA α (.union opts) ρ := by
  intro a
  show anyP (AdmAList α opts ρ) a = true ↔ (select (denoteList α opts ρ) (·.p) a).isSome = true
  rw [select_isSome_attemptA]
  induction opts with
  | nil => simp [anyP, AdmAList, denoteList]
  | cons t ts ih =>
    simp only [AdmAList, anyP, denoteList, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
    rw [h t List.mem_cons_self a, ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]

variable (α) in
def ExactAL (ρ : List S.C) : List (Term S) → Prop
  | [] => True
  | t :: ts => ExactA α t ρ ∧ ExactAL ρ ts

variable (α) in
def ExactAO (ρ : List S.C) : Option (Term S) → Prop
  | none => True
  | some t => ExactA α t ρ

theorem exactAL_mem : ∀ (ts : List (Term S)), ExactAL α ρ ts → ∀ t ∈ ts, ExactA α t ρ
  | [], _, _, ht => nomatch ht
  | _ :: ts, h, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact h.1
      · exact exactAL_mem ts h.2 t ht'

theorem exactAO_mem : ∀ (tail : Option (Term S)), ExactAO α ρ tail → ∀ t ∈ tail, ExactA α t ρ
  | none, _, _, ht => nomatch ht
  | some _, h, _, ht => by cases ht; exact h

mutual
/-- **Every attribute row is exact**, at every universe, from the exactness of the primitive
    rows alone. `refine` and `held` are exact because the row decodes and then asks. -/
theorem AdmA_exact : ∀ (t : Term S) (ρ : List S.C), ExactA α t ρ
  | .prim g, _ => PrimAdmA.admA_exact g
  | .list pre sp suf, ρ =>
      ExactA_list (exactAL_mem pre (AdmA_exactL pre ρ)) (exactAO_mem sp (AdmA_exactO sp ρ))
        (exactAL_mem suf (AdmA_exactL suf ρ))
  | .object b, ρ => AdmA_exactB b ρ
  | .union opts, ρ => ExactA_union (exactAL_mem opts (AdmA_exactL opts ρ))
  | .set _, _ | .opaq, _ | .mu _, _ | .never, _ | .var _, _ => fun _ => Iff.rfl
  | .held c P k, ρ => by
      have hc := AdmA_exact c ρ
      have hP := Adm_exact (α := α) P ρ
      intro a
      simp only [AdmA, refineReads, denote, Codec.restrict, Codec.through, Bool.and_eq_true, hc a]
      cases (denote α c ρ).p a with
      | none => simp
      | some w => simpa using Bool.eq_iff_iff.mpr (hP ((α.word k).2 w))
  | .refine c p, ρ => by
      have hc := AdmA_exact c ρ
      intro a
      simp only [AdmA, refineReads, denote, Codec.restrict, Bool.and_eq_true, hc a]
      cases (denote α c ρ).p a <;> simp []

theorem AdmA_exactB : ∀ (b : Body S) (ρ : List S.C), ExactA α (.object b) ρ
  | .mk _ fld wild, ρ => ExactA_object (fun k => AdmA_exactF (fld k) ρ) (fun _ h => by
      have hw := AdmA_exactO wild ρ
      rw [h] at hw
      exact hw)

theorem AdmA_exactL : ∀ (ts : List (Term S)) (ρ : List S.C), ExactAL α ρ ts
  | [], _ => trivial
  | t0 :: ts, ρ => ⟨AdmA_exact t0 ρ, AdmA_exactL ts ρ⟩

theorem AdmA_exactO : ∀ (tail : Option (Term S)) (ρ : List S.C), ExactAO α ρ tail
  | none, _ => trivial
  | some t0, ρ => AdmA_exact t0 ρ

/-- Each slot reads exactly through its carried term. -/
theorem AdmA_exactF : ∀ (fd : ObjectSlot S) (ρ : List S.C), ExactAField α fd ρ
  | .req t0, ρ => fun a => AdmA_exact t0 ρ a
  | .optional t0, ρ => fun a => AdmA_exact t0 ρ a
end

/-- The row, read as a Boolean: the read domain of the denotation. -/
theorem AdmA_eq_isSome (t : Term S) (ρ : List S.C) (a : Sem.A S) :
    AdmA α t ρ a = ((denote α t ρ).p a).isSome :=
  Bool.eq_iff_iff.mpr (AdmA_exact t ρ a)

/-- **A term with no variable reads one set of attributes under every environment.** -/
theorem AdmA_closed (t : Term S) (h : t.hasVar = false) (ρ ρ' : List S.C) :
    AdmA α t ρ = AdmA α t ρ' := by
  funext a
  rw [AdmA_eq_isSome, AdmA_eq_isSome, denote_closed t h ρ ρ']

end

end Calculus.Alg
