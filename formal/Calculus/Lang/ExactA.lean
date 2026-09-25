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

variable {S : Syn}

/-- The current-schema reader has the same required-name guard as the writer. -/
def reqPresentT (fields : Finset String) (fld : {k // k ∈ fields} → ObjectSlot S)
    (keys : Finset String) : Bool :=
  decide (∀ k : {k // k ∈ fields},
    (match fld k with | .req _ => decide (k.1 ∈ keys) | _ => true) = true)

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

/-- **`refine`'s read-side gate**: decode with the base, then apply `q` to what comes out. -/
noncomputable def refineReads (t : Term S) (q : S.V → Bool) (a : Sem.A S) : Bool :=
  match (denote t).p a with
  | some v => q v
  | none => false

theorem reqPresentT_eq (fields : Finset String) (fld : {k // k ∈ fields} → ObjectSlot S)
    (keys : Finset String) :
    reqPresentT fields fld keys = reqPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys := by
  simp only [reqPresentT, reqPresentB]
  congr 1
  apply propext
  constructor <;> intro h k <;> have := h k <;>
    (cases hfd : fld k with
      | req t => simp_all [reqPresentAt, fieldSem]
      | optional t => simp_all [reqPresentAt, fieldSem])

/-- **The read side keeps every stored name.** An open block is a codec or nothing, so
    `objRead`'s filter is the identity on the key set, and the row owes it nothing. -/
theorem keepB_wild (wild : Option (Term S)) (sems : MapOf (FieldSem S.V (Sem.A S) (Sem.M S)))
    (k : String) {ρ : List S.C} : keepB (wildSem wild ρ) sems k = true := by
  cases wild with
  | none => rfl
  | some pt => rfl

variable [PrimAdm S] [PrimAdmA S]

noncomputable section

mutual

/-- **The joint admission predicate, attribute side.** `refine` and `held` decode and then ask
    what the read produces. -/
def AdmA : Term S → Sem.A S → Bool
  | .prim g => PrimAdmA.admA g
  | .never => fun _ => false
  | .held t P _ g => fun a => AdmA t a && refineReads t (fun w => Adm P (g w)) a
  | .refine t p => fun a => AdmA t a && refineReads t (Sem.eval p) a
  | .union opts => fun a => anyP (AdmAList opts) a
  | .set t => fun a => ((denote (.set t)).p a).isSome
  | .list pre sp suf => fun a =>
      match Sem.list (S := S) with
      | some L =>
          match L.pA.out a with
          | some as => alignPL (AdmAList pre) (AdmAOptT sp) (AdmAList suf) as
          | none => false
      | none => false
  | .object b => AdmABody b
  | .opaq => fun a => ((Sem.top (S := S)).p a).isSome
  | .var _ => fun _ => false
  | .mu b => fun a => ((denote (.mu b)).p a).isSome

/-- The read side's payload row; `AdmBody`'s mirror. -/
def AdmABody : Body S → Sem.A S → Bool
  | .mk fields fld wild => fun a =>
      match Sem.map (S := S) with
      | some F =>
          match F.mA.out a with
          | some m =>
              reqPresentT fields fld m.keys &&
              objAdmV ⟨fields, fun k => AdmAField (fld k)⟩ (AdmAWild wild) m.keys m.get
          | none => false
      | none => false

def AdmAField : ObjectSlot S → Sem.A S → Bool
  | .req t => AdmA t
  | .optional t => AdmA t

def AdmAWild : Option (Term S) → Option (Sem.A S → Bool)
  | none => none
  | some t => some (AdmA t)

def AdmAList : List (Term S) → List (Sem.A S → Bool)
  | [] => []
  | t :: ts => AdmA t :: AdmAList ts

def AdmAOptT : Option (Term S) → Option (Sem.A S → Bool)
  | none => none
  | some t => some (AdmA t)

end

@[simp] theorem AdmAList_eq : ∀ ts : List (Term S), AdmAList ts = ts.map AdmA
  | [] => rfl
  | t :: ts => by simp only [AdmAList, List.map]; rw [AdmAList_eq ts]

/-- The row is `dom(p)`, not a bound on it. -/
def ExactA (t : Term S) : Prop := ∀ a, AdmA t a = true ↔ ((denote t).p a).isSome

theorem alignPA_iff (tail : Option (Term S)) (htl : ∀ t ∈ tail, ExactA t) :
    ∀ (ts : List (Term S)) (as : List (Sem.A S)), (∀ t ∈ ts, ExactA t) →
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
theorem zipPA_iff : ∀ (suf : List (Term S)), (∀ t ∈ suf, ExactA t) → ∀ (back : List (Sem.A S)),
    back.length = suf.length →
    (zipP (AdmAList suf) back = true ↔
      (traverse (fun ca : S.C × Sem.A S => ca.1.p ca.2)
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
theorem alignPAL_iff (pre : List (Term S)) (sp : Option (Term S)) (suf : List (Term S))
    (hpre : ∀ t ∈ pre, ExactA t) (hsp : ∀ t ∈ sp, ExactA t) (hsuf : ∀ t ∈ suf, ExactA t)
    (as : List (Sem.A S)) :
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
theorem ExactA_list {pre : List (Term S)} {sp : Option (Term S)} {suf : List (Term S)}
    (hpre : ∀ t ∈ pre, ExactA t) (hsp : ∀ t ∈ sp, ExactA t) (hsuf : ∀ t ∈ suf, ExactA t) :
    ExactA (.list pre sp suf) := by
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

def ExactAField (fd : ObjectSlot S) : Prop :=
  ∀ a, AdmAField fd a = true ↔ (((fieldSem fd).codec).p a).isSome

theorem entryA_iff {fields : Finset String} {fld : {k // k ∈ fields} → ObjectSlot S}
    {wild : Option (Term S)}
    (hf : ∀ k : {k // k ∈ fields}, ExactAField (fld k))
    (hr : ∀ t, wild = some t → ExactA t) (k : String) (a : Sem.A S) :
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

theorem ExactA_object {fields : Finset String} {fld : {k // k ∈ fields} → ObjectSlot S}
    {wild : Option (Term S)}
    (hf : ∀ k : {k // k ∈ fields}, ExactAField (fld k))
    (hr : ∀ t, wild = some t → ExactA t) :
    ExactA (.object (.mk fields fld wild)) := by
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
      rw [reqPresentT_eq]
      simp only [objRead, objAdmV, Bool.and_eq_true, decide_eq_true_eq]
      by_cases hv : reqPresentB ⟨fields, fun k => fieldSem (fld k)⟩ m.keys = true
      · rw [if_pos hv]
        simp only [hv, true_and, Option.isSome_map, funImage_isSome_iff]
        constructor
        · intro h k
          exact (entryA_iff hf hr k.1 _).mp (h ⟨k.1, (Finset.mem_filter.mp k.2).1⟩)
        · intro h k
          refine (entryA_iff hf hr k.1 (m.get k)).mpr ?_
          have hmem : k.1 ∈ m.keys.filter
              (keepB (wildSem wild) ⟨fields, fun k => fieldSem (fld k)⟩ ·) :=
            Finset.mem_filter.mpr ⟨k.2, keepB_wild wild _ k.1⟩
          exact h ⟨k.1, hmem⟩
      · rw [if_neg hv]
        simp [hv]

/-- **`union` reads exactly what its row says**. -/
theorem ExactA_union {opts : List (Term S)} (h : ∀ t ∈ opts, ExactA t) :
    ExactA (.union opts) := by
  intro a
  show anyP (AdmAList opts) a = true ↔ (select (denoteList opts) (·.p) a).isSome = true
  rw [select_isSome_attemptA]
  induction opts with
  | nil => simp [anyP, AdmAList, denoteList]
  | cons t ts ih =>
    simp only [AdmAList, anyP, denoteList, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
    rw [h t List.mem_cons_self a, ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]

def ExactAL : List (Term S) → Prop
  | [] => True
  | t :: ts => ExactA t ∧ ExactAL ts

def ExactAO : Option (Term S) → Prop
  | none => True
  | some t => ExactA t

theorem exactAL_mem : ∀ (ts : List (Term S)), ExactAL ts → ∀ t ∈ ts, ExactA t
  | [], _, _, ht => nomatch ht
  | _ :: ts, h, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact h.1
      · exact exactAL_mem ts h.2 t ht'

theorem exactAO_mem : ∀ (tail : Option (Term S)), ExactAO tail → ∀ t ∈ tail, ExactA t
  | none, _, _, ht => nomatch ht
  | some _, h, _, ht => by cases ht; exact h

mutual
/-- **Every attribute row is exact**, at every universe, from the exactness of the primitive
    rows alone. `refine` and `held` are exact because the row decodes and then asks. -/
theorem AdmA_exact : ∀ (t : Term S), ExactA t
  | .prim g => PrimAdmA.admA_exact g
  | .list pre sp suf =>
      ExactA_list (exactAL_mem pre (AdmA_exactL pre)) (exactAO_mem sp (AdmA_exactO sp))
        (exactAL_mem suf (AdmA_exactL suf))
  | .object b => AdmA_exactB b
  | .union opts => ExactA_union (exactAL_mem opts (AdmA_exactL opts))
  | .set _ | .opaq | .mu _ | .never | .var _ => fun _ => Iff.rfl
  | .held c P f g => by
      have hc := AdmA_exact c
      have hP := Adm_exact P
      intro a
      simp only [AdmA, refineReads, denote, Codec.restrict, Codec.through, Bool.and_eq_true, hc a]
      cases (denote c).p a with
      | none => simp
      | some w => simpa using Bool.eq_iff_iff.mpr (hP (g w))
  | .refine c p => by
      have hc := AdmA_exact c
      intro a
      simp only [AdmA, refineReads, denote, Codec.restrict, Bool.and_eq_true, hc a]
      cases (denote c).p a <;> simp []

theorem AdmA_exactB : ∀ (b : Body S), ExactA (.object b)
  | .mk _ fld wild => ExactA_object (fun k => AdmA_exactF (fld k)) (fun _ h => by
      have hw := AdmA_exactO wild
      rw [h] at hw
      exact hw)

theorem AdmA_exactL : ∀ (ts : List (Term S)), ExactAL ts
  | [] => trivial
  | t0 :: ts => ⟨AdmA_exact t0, AdmA_exactL ts⟩

theorem AdmA_exactO : ∀ (tail : Option (Term S)), ExactAO tail
  | none => trivial
  | some t0 => AdmA_exact t0

/-- Each slot reads exactly through its carried term. -/
theorem AdmA_exactF : ∀ (fd : ObjectSlot S), ExactAField fd
  | .req t0 => fun a => AdmA_exact t0 a
  | .optional t0 => fun a => AdmA_exact t0 a
end

end

end Calculus.Alg
