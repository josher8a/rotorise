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

variable {S : Syn}

/-- `valPresentB`'s guard, read off the *term*'s field table: only `optional` may be absent. -/
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

mutual

/-- **The joint admission predicate.** One structural recursion over the term, with the
    containers recursing through this row. `set`, `opaq` and `mu` ask their own codec, and a
    closed variable is the bottom. -/
def Adm : Term S → S.V → Bool
  | .prim g => PrimAdm.admV g
  | .never => fun _ => false
  | .refine t p => fun v => Adm t v && Sem.eval p v
  | .held t P f _ => fun v => Adm t (f v) && Adm P v
  | .union opts => fun v => anyP (AdmList opts) v
  | .set t => fun v => ((denote (.set t)).e v).isSome
  | .list pre sp suf => fun v =>
      match Sem.list (S := S) with
      | some L =>
          match L.pV.out v with
          | some vs => alignPL (AdmList pre) (AdmOptT sp) (AdmList suf) vs
          | none => false
      | none => false
  | .object b => AdmBody b
  | .opaq => fun v => ((Sem.top (S := S)).e v).isSome
  | .var _ => fun _ => false
  | .mu b => fun v => ((denote (.mu b)).e v).isSome

/-- The payload's row: the declared names that must be present are, and every present name's
    value is admitted by its slot or by the open block. -/
def AdmBody : Body S → S.V → Bool
  | .mk fields fld wild => fun v =>
      match Sem.map (S := S) with
      | some F =>
          match F.mV.out v with
          | some m =>
              valPresentT fields fld m.keys &&
              objAdmV ⟨fields, fun k => AdmField (fld k)⟩ (AdmWild wild) m.keys m.get
          | none => false
      | none => false

/-- A slot's row is its term's. -/
def AdmField : ObjectSlot S → S.V → Bool
  | .req t => Adm t
  | .optional t => Adm t

/-- The open block's row, where the body has one. -/
def AdmWild : Option (Term S) → Option (S.V → Bool)
  | none => none
  | some t => some (Adm t)

/-- The options' rows, in order. -/
def AdmList : List (Term S) → List (S.V → Bool)
  | [] => []
  | t :: ts => Adm t :: AdmList ts

/-- The spread's row, where there is one. -/
def AdmOptT : Option (Term S) → Option (S.V → Bool)
  | none => none
  | some t => some (Adm t)

end

@[simp] theorem AdmList_eq : ∀ ts : List (Term S), AdmList ts = ts.map Adm
  | [] => rfl
  | t :: ts => by simp only [AdmList, List.map]; rw [AdmList_eq ts]

/-- The row is `dom(e)`, not merely a bound on it. -/
def ExactV (t : Term S) : Prop := ∀ v, Adm t v = true ↔ ((denote t).e v).isSome

/-- `alignP` is `align`'s row: the same length discipline, the same per-position test. -/
theorem alignP_iff (tail : Option (Term S)) (htl : ∀ t ∈ tail, ExactV t) :
    ∀ (ts : List (Term S)) (vs : List S.V), (∀ t ∈ ts, ExactV t) →
      (alignP (AdmList ts) (AdmOptT tail) vs = true ↔
        ((align (denoteList ts) (denoteOpt tail) vs).bind
          (traverse fun cv => cv.1.e cv.2)).isSome = true)
  | [], [], _ => by
      cases tail <;> simp [alignP, AdmList, AdmOptT, align, denoteList, denoteOpt, traverse]
  | [], v :: vs, _ => by
      cases htail : tail with
      | none => simp [alignP, AdmList, AdmOptT, align, denoteList, denoteOpt]
      | some t =>
        have ht : ExactV t := htl t (by simp [htail])
        have ih := alignP_iff tail htl [] vs (by simp)
        rw [htail] at ih
        simp only [AdmList, AdmOptT, denoteList, denoteOpt] at ih
        simp only [alignP, AdmList, AdmOptT, align, denoteList, denoteOpt,
          Bool.and_eq_true]
        cases hal : align [] (some (denote t)) vs with
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
      have ht : ExactV t := h t (by simp)
      have ih := alignP_iff tail htl ts vs (fun t' ht' => h t' (by simp [ht']))
      simp only [alignP, AdmList, align, denoteList, Bool.and_eq_true]
      cases hal : align (denoteList ts) (denoteOpt tail) vs with
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
theorem zipP_iff : ∀ (suf : List (Term S)), (∀ t ∈ suf, ExactV t) → ∀ (back : List S.V),
    back.length = suf.length →
    (zipP (AdmList suf) back = true ↔
      (traverse (fun cv : S.C × S.V => cv.1.e cv.2)
        ((denoteList suf).zip back)).isSome = true)
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
    (hpre : ∀ t ∈ pre, ExactV t) (hsp : ∀ t ∈ sp, ExactV t) (hsuf : ∀ t ∈ suf, ExactV t)
    (vs : List S.V) :
    alignPL (AdmList pre) (AdmOptT sp) (AdmList suf) vs = true ↔
      ((alignL (denoteList pre) (denoteOpt sp) (denoteList suf) vs).bind
        (traverse fun cv => cv.1.e cv.2)).isSome = true := by
  have hlenA : (AdmList suf).length = suf.length := by simp
  have hlenD : (denoteList suf).length = suf.length := by simp
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
    cases hal : align (denoteList pre) (denoteOpt sp) (vs.take (vs.length - suf.length)) with
    | none => simp
    | some ps => simp [traverse_append_isSome]

/-- **`list` is exact** once its three parts are. A universe with no list former denotes the
    list as the bottom, and the row is `false`. -/
theorem ExactV_list {pre : List (Term S)} {sp : Option (Term S)} {suf : List (Term S)}
    (hpre : ∀ t ∈ pre, ExactV t) (hsp : ∀ t ∈ sp, ExactV t) (hsuf : ∀ t ∈ suf, ExactV t) :
    ExactV (.list pre sp suf) := by
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

/-- A slot's row is exact when the term it carries is. -/
def ExactField (fd : ObjectSlot S) : Prop :=
  ∀ v, AdmField fd v = true ↔ (((fieldSem fd).codec).e v).isSome

omit [PrimAdm S] in
theorem valPresentT_eq (fields : Finset String) (fld : {k // k ∈ fields} → ObjectSlot S)
    (keys : Finset String) :
    valPresentT fields fld keys = valPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys := by
  simp only [valPresentT, valPresentB]
  congr 1
  apply propext
  constructor <;> intro h k <;> have := h k <;>
    (cases hfd : fld k with
      | req t => simp_all [valPresentAt, fieldSem]
      | optional t => simp_all [valPresentAt, fieldSem])

theorem entry_iff {fields : Finset String} {fld : {k // k ∈ fields} → ObjectSlot S}
    {wild : Option (Term S)}
    (hf : ∀ k : {k // k ∈ fields}, ExactField (fld k))
    (hr : ∀ t, wild = some t → ExactV t) (k : String) (v : S.V) :
    (entryP ⟨fields, fun k => AdmField (fld k)⟩ (AdmWild wild) k).any (· v) = true ↔
    ((entryCodec ⟨fields, fun k => fieldSem (fld k)⟩ (rcOf (wildSem wild)) k).bind
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
    (hf : ∀ k : {k // k ∈ fields}, ExactField (fld k))
    (hr : ∀ t, wild = some t → ExactV t) :
    ExactV (.object (.mk fields fld wild)) := by
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
      rw [valPresentT_eq]
      simp only [objWrite, objAdmV, Bool.and_eq_true, decide_eq_true_eq]
      by_cases hv : valPresentB ⟨fields, fun k => fieldSem (fld k)⟩ m.keys = true
      · rw [if_pos hv]
        simp only [hv, true_and, Option.isSome_map, funImage_isSome_iff]
        exact forall_congr' fun k => entry_iff hf hr k.1 (m.get k)
      · rw [if_neg hv]
        simp [hv]

/-- **`union` writes exactly what its row says**: the options are exact, and a union writes
    where one of them writes. -/
theorem ExactV_union {opts : List (Term S)} (h : ∀ t ∈ opts, ExactV t) :
    ExactV (.union opts) := by
  intro v
  show anyP (AdmList opts) v = true ↔ (select (denoteList opts) (·.e) v).isSome = true
  rw [select_isSome_attempt]
  induction opts with
  | nil => simp [anyP, AdmList, denoteList]
  | cons t ts ih =>
    simp only [AdmList, anyP, denoteList, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
    rw [h t List.mem_cons_self v, ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]

def ExactVL : List (Term S) → Prop
  | [] => True
  | t :: ts => ExactV t ∧ ExactVL ts

def ExactVO : Option (Term S) → Prop
  | none => True
  | some t => ExactV t

theorem exactVL_mem : ∀ (ts : List (Term S)), ExactVL ts → ∀ t ∈ ts, ExactV t
  | [], _, _, ht => nomatch ht
  | _ :: ts, h, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact h.1
      · exact exactVL_mem ts h.2 t ht'

theorem exactVO_mem : ∀ (tail : Option (Term S)), ExactVO tail → ∀ t ∈ tail, ExactV t
  | none, _, _, ht => nomatch ht
  | some _, h, _, ht => by cases ht; exact h

mutual
/-- **Every row is exact**, at every universe, from the exactness of the primitive rows alone.

    Mutual with the list, option, slot and open-block companions, for the reason `denote` is: a
    list's positions and a union's options are reached through a `List`, and an object's slots
    through a *function*. A `∀ t ∈ ts` premise is a membership that the structural checker
    cannot follow back to the constructor's argument, so the companions state a conjunction. -/
theorem Adm_exact : ∀ (t : Term S), ExactV t
  | .prim g => PrimAdm.admV_exact g
  | .list pre sp suf =>
      ExactV_list (exactVL_mem pre (Adm_exactL pre)) (exactVO_mem sp (Adm_exactO sp))
        (exactVL_mem suf (Adm_exactL suf))
  | .object b => Adm_exactB b
  | .union opts => ExactV_union (exactVL_mem opts (Adm_exactL opts))
  -- `set`, `opaq` and `mu` ask their own codec, and the bottom and a closed variable are empty
  | .set _ | .opaq | .mu _ | .never | .var _ => fun _ => Iff.rfl
  | .refine c p => by
      have hc := Adm_exact c
      intro v
      show (Adm c v && Sem.eval p v) = true ↔ (((denote c).restrict (Sem.eval p)).e v).isSome
      rw [restrict_e_isSome, Bool.and_eq_true, Bool.and_eq_true, hc v]
      exact And.comm
  | .held c P f g => by
      have hc := Adm_exact c
      have hP := Adm_exact P
      intro v
      show (Adm c (f v) && Adm P v) = true ↔
        ((((denote c).through f g).restrict fun v => ((denote P).e v).isSome).e v).isSome
      rw [restrict_e_isSome, Bool.and_eq_true, Bool.and_eq_true, hc (f v), hP v]
      exact And.comm

/-- The payload's own exactness: an object's slots are reached through a function, so the
    recursion lands on a `Body`. -/
theorem Adm_exactB : ∀ (b : Body S), ExactV (.object b)
  | .mk _ fld wild => ExactV_object (fun k => Adm_exactF (fld k)) (fun _ h => by
      have hw := Adm_exactO wild
      rw [h] at hw
      exact hw)

theorem Adm_exactL : ∀ (ts : List (Term S)), ExactVL ts
  | [] => trivial
  | t0 :: ts => ⟨Adm_exact t0, Adm_exactL ts⟩

theorem Adm_exactO : ∀ (tail : Option (Term S)), ExactVO tail
  | none => trivial
  | some t0 => Adm_exact t0

/-- A slot's row is exact when its term's is. -/
theorem Adm_exactF : ∀ (fd : ObjectSlot S), ExactField fd
  | .req t0 => fun v => Adm_exact t0 v
  | .optional t0 => fun v => Adm_exact t0 v
end

end

end Calculus.Alg
