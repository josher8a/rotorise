import Calculus.Lang.Sound
import Calculus.Alg.Rows

/-!
# Exactness on the value side, over a universe signature

`Adm t` is admission as a *domain*: a row per constructor that equals `dom(e)` of `denote t`.
Every row except the primitive row is a combinator on the rows of the subterms, or asks its own
codec. So the structure is proved here one time, for every universe.

A universe supplies the row of each primitive and the exactness of that row (`PrimAdm`). That is
the only fact of a universe that the value side reads. A universe can state the primitive row
syntactically, so that a verdict reduces without the codec, and the law pins the row to the
codec.
-/

namespace Calculus

/-- `entryCodec`'s row: the slot a name declares, or else the open block's. `none` is an
    undeclared name in a body that declares no open block, and both sides refuse it. -/
def entryP {α : Type} (fs : MapOf (α → Bool)) (rp : Option (α → Bool)) (k : String) :
    Option (α → Bool) :=
  match fs.at k with | some P => some P | none => rp

/-- `objWrite`'s traversal and `objRead`'s traversal, as a row: every entry goes through the
    codec its name names. -/
def objAdmV {α : Type} (fs : MapOf (α → Bool)) (rp : Option (α → Bool)) (keys : Finset String)
    (g : {k // k ∈ keys} → α) : Bool :=
  decide (∀ k : {k // k ∈ keys}, (entryP fs rp k.1).any (· (g k)) = true)

end Calculus

namespace Calculus.Alg

/-- **The value-side row of each primitive**, and its exactness. A universe supplies this class;
    the rest of `Adm` and of its exactness is the term language's. -/
class PrimAdm (S : Syn) [Sem S] where
  /-- The values that a primitive writes. -/
  admV : S.Ground → S.V → Bool
  /-- The row is the write domain of the primitive's codec. -/
  admV_exact : ∀ g v, admV g v = true ↔ ((Sem.ground g).e v).isSome = true

variable {S : Syn} {α : Table S}

/-- The guard of `valPresentB` and of `reqPresentB`, read off the *term*'s field table: only
    `optional` may be absent. -/
def valPresentT (fields : Finset String) (fld : {k // k ∈ fields} → ObjectSlot S)
    (keys : Finset String) : Bool :=
  decide (∀ k : {k // k ∈ fields},
    (match fld k with | .optional _ => true | _ => decide (k.1 ∈ keys)) = true)

/-- A traversal succeeds at a cons exactly when the head and the tail do. -/
theorem traverse_cons_isSome {α β : Type} (f : α → Option β) (x : α) (xs : List α) :
    (traverse f (x :: xs)).isSome = ((f x).isSome && (traverse f xs).isSome) := by
  simp only [traverse]
  cases hx : f x <;> cases hxs : traverse f xs <;> simp

/-- **A sum writes exactly where one of its options writes.** -/
theorem select_isSome_attempt {V A M : Type} (os : List (Codec V A M)) (v : V) :
    (select os (·.e) v).isSome = true ↔ ∃ o ∈ os, (o.e v).isSome = true := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨o, ho, -, he⟩ := select_admits ha
    exact ⟨o, ho, by rw [he]; rfl⟩
  · rintro ⟨o, ho, he⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp he
    obtain ⟨o', hf⟩ := find?_attempt_V ho ha
    unfold select; rw [hf]; exact acts_of_find?_V hf

variable [Sem S] [PrimAdm S]

noncomputable section

variable (α) in
mutual

/-- **The joint admission predicate**, under an environment `ρ` of codecs for the bound
    variables, as `denote` reads one. One structural recursion over the term, with the containers
    recursing through this row. `set`, `opaq` and `mu` ask their own codec, and a variable asks
    the codec that the environment gives the variable. -/
def Adm : Term S → List S.C → S.V → Bool
  | .prim g, _ => PrimAdm.admV g
  | .never, _ => fun _ => false
  | .refine t p, ρ => fun v => Adm t ρ v && Sem.eval p v
  | .held t P k, ρ => fun v => Adm t ρ ((α.word k).1 v) && Adm P ρ v
  | .union opts, ρ => fun v => anyP (AdmList opts ρ) v
  | .set t, ρ => fun v => ((denote α (.set t) ρ).e v).isSome
  | .list pre sp suf, ρ => fun v =>
      match Sem.list (S := S) with
      | some L =>
          match L.pV.out v with
          | some vs => alignPL (AdmList pre ρ) (AdmOptT sp ρ) (AdmList suf ρ) vs
          | none => false
      | none => false
  | .object b, ρ => AdmBody b ρ
  | .opaq, _ => fun v => ((Sem.top (S := S)).e v).isSome
  | .var i, ρ => fun v => ((envAt ρ i).e v).isSome
  | .mu b, ρ => fun v => ((denote α (.mu b) ρ).e v).isSome

/-- The payload's row: the declared names that must be present are, and every present name's
    value is admitted by its slot or by the open block. -/
def AdmBody : Body S → List S.C → S.V → Bool
  | .mk fields fld wild, ρ => fun v =>
      match Sem.map (S := S) with
      | some F =>
          match F.mV.out v with
          | some m =>
              valPresentT fields fld m.keys &&
              objAdmV ⟨fields, fun k => AdmField (fld k) ρ⟩ (AdmWild wild ρ) m.keys m.get
          | none => false
      | none => false

/-- A slot's row is its term's. -/
def AdmField : ObjectSlot S → List S.C → S.V → Bool
  | .req t, ρ => Adm t ρ
  | .optional t, ρ => Adm t ρ

/-- The open block's row, where the body has one. -/
def AdmWild : Option (Term S) → List S.C → Option (S.V → Bool)
  | none, _ => none
  | some t, ρ => some (Adm t ρ)

/-- The options' rows, in order. -/
def AdmList : List (Term S) → List S.C → List (S.V → Bool)
  | [], _ => []
  | t :: ts, ρ => Adm t ρ :: AdmList ts ρ

/-- The spread's row, where there is one. -/
def AdmOptT : Option (Term S) → List S.C → Option (S.V → Bool)
  | none, _ => none
  | some t, ρ => some (Adm t ρ)

end

@[simp] theorem AdmList_eq (ρ : List S.C) : ∀ ts : List (Term S), AdmList α ts ρ = ts.map (Adm α · ρ)
  | [] => rfl
  | t :: ts => by simp only [AdmList, List.map]; rw [AdmList_eq ρ ts]

variable (α) in
/-- The row is `dom(e)`, not merely a bound on it, under the environment `ρ`. -/
def ExactV (t : Term S) (ρ : List S.C) : Prop :=
  ∀ v, Adm α t ρ v = true ↔ ((denote α t ρ).e v).isSome

variable {ρ : List S.C}

/-- `alignP` is `align`'s row: the same length discipline, the same per-position test. -/
theorem alignP_iff (tail : Option (Term S)) (htl : ∀ t ∈ tail, ExactV α t ρ) :
    ∀ (ts : List (Term S)) (vs : List S.V), (∀ t ∈ ts, ExactV α t ρ) →
      (alignP (AdmList α ts ρ) (AdmOptT α tail ρ) vs = true ↔
        ((align (denoteList α ts ρ) (denoteOpt α tail ρ) vs).bind
          (traverse fun cv => cv.1.e cv.2)).isSome = true)
  | [], [], _ => by
      cases tail <;> simp [alignP, AdmList, AdmOptT, align, denoteList, denoteOpt, traverse]
  | [], v :: vs, _ => by
      cases htail : tail with
      | none => simp [alignP, AdmList, AdmOptT, align, denoteList, denoteOpt]
      | some t =>
        have ht : ExactV α t ρ := htl t (by simp [htail])
        have ih := alignP_iff tail htl [] vs (by simp)
        rw [htail] at ih
        simp only [AdmList, AdmOptT, denoteList, denoteOpt] at ih
        simp only [alignP, AdmList, AdmOptT, align, denoteList, denoteOpt,
          Bool.and_eq_true]
        cases hal : align [] (some (denote α t ρ)) vs with
        | none =>
          rw [hal] at ih
          simp at ih
          simp [ih]
        | some ps =>
          rw [hal] at ih
          simp only [Option.map_some, Option.bind_some] at ih ⊢
          rw [traverse_cons_isSome, Bool.and_eq_true, ← ht v, ← ih]
  | t :: ts, [], _ => by
      cases tail <;> simp [alignP, AdmList, AdmOptT, align, denoteList, denoteOpt]
  | t :: ts, v :: vs, h => by
      have ht : ExactV α t ρ := h t (by simp)
      have ih := alignP_iff tail htl ts vs (fun t' ht' => h t' (by simp [ht']))
      simp only [alignP, AdmList, align, denoteList, Bool.and_eq_true]
      cases hal : align (denoteList α ts ρ) (denoteOpt α tail ρ) vs with
      | none =>
        simp only [hal, Option.map_none, Option.bind_none, Option.isSome_none] at ih ⊢
        simp at ih
        simp [ih]
      | some ps =>
        simp only [hal, Option.map_some, Option.bind_some] at ih ⊢
        rw [traverse_cons_isSome, Bool.and_eq_true, ← ht v, ← ih]

/-- The suffix's row, transported across its positions' exactness. The length premise is load
    bearing: `List.zip` truncates, so a row longer than the suffix would answer `true` where
    `zipP` answers `false`. -/
theorem zipP_iff : ∀ (suf : List (Term S)), (∀ t ∈ suf, ExactV α t ρ) → ∀ (back : List S.V),
    back.length = suf.length →
    (zipP (AdmList α suf ρ) back = true ↔
      (traverse (fun cv : S.C × S.V => cv.1.e cv.2)
        ((denoteList α suf ρ).zip back)).isSome = true)
  | [], _, [], _ => by simp [zipP, AdmList, denoteList]
  | [], _, _ :: _, h => by
      exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _, _, [], h => by
      exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | t :: ts, h, v :: vs, hlen => by
      simp only [AdmList, denoteList, zipP, List.zip_cons_cons, Bool.and_eq_true,
        traverse_cons_isSome]
      rw [zipP_iff ts (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) vs
          (by simp only [List.length_cons] at hlen; omega),
        h t List.mem_cons_self v]

/-- **`alignPL` is `alignL`'s row.** The suffix splits off the right end on both sides. -/
theorem alignPL_iff (pre : List (Term S)) (sp : Option (Term S)) (suf : List (Term S))
    (hpre : ∀ t ∈ pre, ExactV α t ρ) (hsp : ∀ t ∈ sp, ExactV α t ρ) (hsuf : ∀ t ∈ suf, ExactV α t ρ)
    (vs : List S.V) :
    alignPL (AdmList α pre ρ) (AdmOptT α sp ρ) (AdmList α suf ρ) vs = true ↔
      ((alignL (denoteList α pre ρ) (denoteOpt α sp ρ) (denoteList α suf ρ) vs).bind
        (traverse fun cv => cv.1.e cv.2)).isSome = true := by
  have hlenA : (AdmList α suf ρ).length = suf.length := by simp
  have hlenD : (denoteList α suf ρ).length = suf.length := by simp
  unfold alignPL
  rw [hlenA]
  rcases Nat.lt_or_ge vs.length suf.length with hlt | hge
  · rw [alignL_short _ _ _ _ (by omega)]
    have h0 : vs.length - suf.length = 0 := by omega
    rw [h0, List.drop_zero]
    refine ⟨fun hc => ?_, fun hc => nomatch hc⟩
    have := zipP_length _ _ (Bool.and_eq_true .. ▸ hc |>.2)
    rw [hlenA] at this
    omega
  · rw [alignL_eq_split _ _ _ _ (by omega), hlenD]
    rw [Bool.and_eq_true, alignP_iff sp hsp pre (vs.take (vs.length - suf.length)) hpre,
      zipP_iff suf hsuf _ (by simp; omega)]
    cases hal : align (denoteList α pre ρ) (denoteOpt α sp ρ) (vs.take (vs.length - suf.length)) with
    | none => simp
    | some ps => simp [traverse_append_isSome]

/-- **`list` is exact** once its three parts are. A universe with no list former denotes the
    list as the bottom, and the row is `false`. -/
theorem ExactV_list {pre : List (Term S)} {sp : Option (Term S)} {suf : List (Term S)}
    (hpre : ∀ t ∈ pre, ExactV α t ρ) (hsp : ∀ t ∈ sp, ExactV α t ρ) (hsuf : ∀ t ∈ suf, ExactV α t ρ) :
    ExactV α (.list pre sp suf) ρ := by
  intro v
  simp only [Adm, denote]
  cases Sem.list (S := S) with
  | none => simp [Codec.empty]
  | some L =>
    simp only [listCodec, carriedCodec]
    cases L.pV.out v with
    | none => simp
    | some vs =>
      simp only [Option.bind_some, Option.isSome_map]
      exact alignPL_iff pre sp suf hpre hsp hsuf vs

variable (α) in
/-- A slot's row is exact when the term it carries is. -/
def ExactField (fd : ObjectSlot S) (ρ : List S.C) : Prop :=
  ∀ v, AdmField α fd ρ v = true ↔ (((fieldSem α fd ρ).codec).e v).isSome

omit [PrimAdm S] in
theorem valPresentT_eq (fields : Finset String) (fld : {k // k ∈ fields} → ObjectSlot S)
    (keys : Finset String) :
    valPresentT fields fld keys = valPresentB ⟨fields, fun k => fieldSem α (fld k) ρ⟩ keys := by
  simp only [valPresentT, valPresentB]
  congr 1
  apply propext
  constructor <;> intro h k <;> have := h k <;>
    (cases hfd : fld k with
      | req t => simp_all [valPresentAt, fieldSem]
      | optional t => simp_all [valPresentAt, fieldSem])

theorem entry_iff {fields : Finset String} {fld : {k // k ∈ fields} → ObjectSlot S}
    {wild : Option (Term S)}
    (hf : ∀ k : {k // k ∈ fields}, ExactField α (fld k) ρ)
    (hr : ∀ t, wild = some t → ExactV α t ρ) (k : String) (v : S.V) :
    (entryP ⟨fields, fun k => AdmField α (fld k) ρ⟩ (AdmWild α wild ρ) k).any (· v) = true ↔
    ((entryCodec ⟨fields, fun k => fieldSem α (fld k) ρ⟩ (rcOf (wildSem α wild ρ)) k).bind
      (fun c => c.e v)).isSome = true := by
  simp only [entryP, entryCodec, MapOf.at]
  by_cases hk : k ∈ fields
  · rw [dif_pos hk, dif_pos hk]
    simpa using hf ⟨k, hk⟩ v
  · rw [dif_neg hk, dif_neg hk]
    cases wild with
    | none => simp [AdmWild, wildSem, rcOf]
    | some pt => simpa [AdmWild, wildSem, rcOf] using hr pt rfl v

/-- **`object` is exact** once its slots and its open block are. -/
theorem ExactV_object {fields : Finset String} {fld : {k // k ∈ fields} → ObjectSlot S}
    {wild : Option (Term S)}
    (hf : ∀ k : {k // k ∈ fields}, ExactField α (fld k) ρ)
    (hr : ∀ t, wild = some t → ExactV α t ρ) :
    ExactV α (.object (.mk fields fld wild)) ρ := by
  intro v
  simp only [Adm, AdmBody, denote, bodySem]
  cases Sem.map (S := S) with
  | none => simp [Codec.empty]
  | some F =>
    simp only [objectCodec, objectCodecCore, carriedCodec]
    cases F.mV.out v with
    | none => simp
    | some m =>
      simp only [Option.bind_some, Option.isSome_map]
      rw [valPresentT_eq (α := α) (ρ := ρ)]
      simp only [objWrite, objAdmV, Bool.and_eq_true, decide_eq_true_eq]
      by_cases hv : valPresentB ⟨fields, fun k => fieldSem α (fld k) ρ⟩ m.keys = true
      · rw [if_pos hv]
        simp only [hv, true_and, Option.isSome_map, funImage_isSome_iff]
        exact forall_congr' fun k => entry_iff hf hr k.1 (m.get k)
      · rw [if_neg hv]
        simp [hv]

/-- **`union` writes exactly what its row says**: the options are exact, and a union writes
    where one of them writes. -/
theorem ExactV_union {opts : List (Term S)} (h : ∀ t ∈ opts, ExactV α t ρ) :
    ExactV α (.union opts) ρ := by
  intro v
  show anyP (AdmList α opts ρ) v = true ↔ (select (denoteList α opts ρ) (·.e) v).isSome = true
  rw [select_isSome_attempt]
  induction opts with
  | nil => simp [anyP, AdmList, denoteList]
  | cons t ts ih =>
    simp only [AdmList, anyP, denoteList, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
    rw [h t List.mem_cons_self v, ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]

variable (α) in
def ExactVL (ρ : List S.C) : List (Term S) → Prop
  | [] => True
  | t :: ts => ExactV α t ρ ∧ ExactVL ρ ts

variable (α) in
def ExactVO (ρ : List S.C) : Option (Term S) → Prop
  | none => True
  | some t => ExactV α t ρ

theorem exactVL_mem : ∀ (ts : List (Term S)), ExactVL α ρ ts → ∀ t ∈ ts, ExactV α t ρ
  | [], _, _, ht => nomatch ht
  | _ :: ts, h, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact h.1
      · exact exactVL_mem ts h.2 t ht'

theorem exactVO_mem : ∀ (tail : Option (Term S)), ExactVO α ρ tail → ∀ t ∈ tail, ExactV α t ρ
  | none, _, _, ht => nomatch ht
  | some _, h, _, ht => by cases ht; exact h

mutual
/-- **Every row is exact**, at every universe, from the exactness of the primitive rows alone.

    Mutual with the list, option, slot and open-block companions, for the reason `denote` is: a
    list's positions and a union's options are reached through a `List`, and an object's slots
    through a *function*. A `∀ t ∈ ts` premise is a membership that the structural checker
    cannot follow back to the constructor's argument, so the companions state a conjunction. -/
theorem Adm_exact : ∀ (t : Term S) (ρ : List S.C), ExactV α t ρ
  | .prim g, _ => PrimAdm.admV_exact g
  | .list pre sp suf, ρ =>
      ExactV_list (exactVL_mem pre (Adm_exactL pre ρ)) (exactVO_mem sp (Adm_exactO sp ρ))
        (exactVL_mem suf (Adm_exactL suf ρ))
  | .object b, ρ => Adm_exactB b ρ
  | .union opts, ρ => ExactV_union (exactVL_mem opts (Adm_exactL opts ρ))
  -- `set`, `opaq`, `mu` and a variable ask their own codec, and the bottom is empty
  | .set _, _ | .opaq, _ | .mu _, _ | .never, _ | .var _, _ => fun _ => Iff.rfl
  | .refine c p, ρ => by
      have hc := Adm_exact c ρ
      intro v
      show (Adm α c ρ v && Sem.eval p v) = true ↔
        (((denote α c ρ).restrict (Sem.eval p)).e v).isSome
      rw [restrict_e_isSome, Bool.and_eq_true, Bool.and_eq_true, hc v]
      exact And.comm
  | .held c P k, ρ => by
      have hc := Adm_exact c ρ
      have hP := Adm_exact P ρ
      intro v
      show (Adm α c ρ ((α.word k).1 v) && Adm α P ρ v) = true ↔
        ((((denote α c ρ).through (α.word k).1 (α.word k).2).restrict
          fun v => ((denote α P ρ).e v).isSome).e v).isSome
      rw [restrict_e_isSome, Bool.and_eq_true, Bool.and_eq_true, hc ((α.word k).1 v), hP v]
      exact And.comm

/-- The payload's own exactness: an object's slots are reached through a function, so the
    recursion lands on a `Body`. -/
theorem Adm_exactB : ∀ (b : Body S) (ρ : List S.C), ExactV α (.object b) ρ
  | .mk _ fld wild, ρ => ExactV_object (fun k => Adm_exactF (fld k) ρ) (fun _ h => by
      have hw := Adm_exactO wild ρ
      rw [h] at hw
      exact hw)

theorem Adm_exactL : ∀ (ts : List (Term S)) (ρ : List S.C), ExactVL α ρ ts
  | [], _ => trivial
  | t0 :: ts, ρ => ⟨Adm_exact t0 ρ, Adm_exactL ts ρ⟩

theorem Adm_exactO : ∀ (tail : Option (Term S)) (ρ : List S.C), ExactVO α ρ tail
  | none, _ => trivial
  | some t0, ρ => Adm_exact t0 ρ

/-- A slot's row is exact when its term's is. -/
theorem Adm_exactF : ∀ (fd : ObjectSlot S) (ρ : List S.C), ExactField α fd ρ
  | .req t0, ρ => fun v => Adm_exact t0 ρ v
  | .optional t0, ρ => fun v => Adm_exact t0 ρ v
end

/-- The row, read as a Boolean: the write domain of the denotation. -/
theorem Adm_eq_isSome (t : Term S) (ρ : List S.C) (v : S.V) :
    Adm α t ρ v = ((denote α t ρ).e v).isSome :=
  Bool.eq_iff_iff.mpr (Adm_exact t ρ v)

/-- **A term with no variable admits one set of values under every environment.** -/
theorem Adm_closed (t : Term S) (h : t.hasVar = false) (ρ ρ' : List S.C) :
    Adm α t ρ = Adm α t ρ' := by
  funext v
  rw [Adm_eq_isSome, Adm_eq_isSome, denote_closed t h ρ ρ']

end

end Calculus.Alg
