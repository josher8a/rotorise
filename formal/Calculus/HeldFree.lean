import Calculus.ExactA

/-!
# Held-free terms are restrictions of `opaque`

A term with no `held` does not change the carrier. Each combinator either restricts its
subterm or composes subterms through the structure that `opaque` itself uses. So the write
graph and the read graph of a held-free term lie inside the graphs of `opaque`.
`confluence_W` and `confluence_R` state the two inclusions. `sub_denote` proves them by one
mutual induction over `Term`, `Body`, `ObjectSlot`, the list and the option.

`Sub c d` is the inclusion of graphs on both halves. The only case that reads a union is
`select_some`: the selector returns the answer of one option. The set cases go through
`encSet_congr` and `decSet_congr`.

The file sits below the meet because the meet's `set` row reads it: over a held-free element, a
set writes and reads exactly where each element does. `Confluence.lean` holds the payoffs.
-/

namespace Calculus
/-- `Ω` writes a string as `S`. -/
theorem Ωe_str (s : String) : Ω.e (.str s) = some (.s s) := rfl
/-- `Ω` writes a number as `N`. -/
theorem Ωe_num (x : WFNumeral) : Ω.e (.num x) = some (.n x) := rfl
/-- `Ω` writes a boolean as `BOOL`. -/
theorem Ωe_bool (b : Bool) : Ω.e (.bool b) = some (.bool b) := rfl
/-- `Ω` writes a byte string as `B`. -/
theorem Ωe_bin (b : Bytes) : Ω.e (.bin b) = some (.b b) := rfl
/-- `Ω` writes `null` as `NULL`. -/
theorem Ωe_null : Ω.e .null = some .null := rfl
/-- `Ω` reads `S` as a string. -/
theorem Ωp_s (s : String) : Ω.p (.s s) = some (.str s) := rfl
/-- `Ω` reads `N` as a number. -/
theorem Ωp_n (x : WFNumeral) : Ω.p (.n x) = some (.num x) := rfl
/-- `Ω` reads `BOOL` as a boolean. -/
theorem Ωp_bool (b : Bool) : Ω.p (.bool b) = some (.bool b) := rfl
/-- `Ω` reads `B` as a byte string. -/
theorem Ωp_b (b : Bytes) : Ω.p (.b b) = some (.bin b) := rfl
/-- `Ω` reads `NULL` as `null`. -/
theorem Ωp_null : Ω.p .null = some .null := rfl

/-! ## Inclusion lemmas, one per combinator -/

/-- `string` is a restriction of `Ω`. -/
theorem sub_string : Sub stringCodec Ω :=
  ⟨fun v a h => (by cases v <;> simp [stringCodec] at h; subst h; rfl),
   fun a v h => (by cases a <;> simp [stringCodec] at h; subst h; rfl)⟩
/-- `number` is a restriction of `Ω`. -/
theorem sub_number : Sub numberCodec Ω :=
  ⟨fun v a h => (by cases v <;> simp [numberCodec] at h; subst h; rfl),
   fun a v h => (by cases a <;> simp [numberCodec] at h; subst h; rfl)⟩
/-- `boolean` is a restriction of `Ω`. -/
theorem sub_boolean : Sub booleanCodec Ω :=
  ⟨fun v a h => (by cases v <;> simp [booleanCodec] at h; subst h; rfl),
   fun a v h => (by cases a <;> simp [booleanCodec] at h; subst h; rfl)⟩
/-- `binary` is a restriction of `Ω`. -/
theorem sub_binary : Sub binaryCodec Ω :=
  ⟨fun v a h => (by cases v <;> simp [binaryCodec] at h; subst h; rfl),
   fun a v h => (by cases a <;> simp [binaryCodec] at h; subst h; rfl)⟩
/-- `null` is a restriction of `Ω`. -/
theorem sub_null : Sub nullCodec Ω :=
  ⟨fun v a h => (by cases v <;> simp [nullCodec] at h; subst h; rfl),
   fun a v h => (by cases a <;> simp [nullCodec] at h; subst h; rfl)⟩

/-- The empty codec is a restriction of `Ω`. -/
theorem sub_empty : Sub Codec.empty Ω := ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

/-- A restriction of a restriction of `Ω` is a restriction of `Ω`. -/
theorem sub_restrict {c : Codec} (h : Sub c Ω) (q : Value → Bool) : Sub (c.restrict q) Ω := by
  refine ⟨fun v a he => ?_, fun a v hp => ?_⟩
  · simp only [Alg.Codec.restrict] at he; split at he
    · exact h.1 _ _ he
    · exact nomatch he
  · simp only [Alg.Codec.restrict, Option.bind_eq_some_iff] at hp
    obtain ⟨w, hw, hq⟩ := hp; split at hq
    · cases hq; exact h.2 _ _ hw
    · exact nomatch hq

/-- Each ground base is a restriction of `Ω`. -/
theorem sub_baseCodec : ∀ k, Sub (baseCodec k) Ω
  | .string => sub_string | .number => sub_number | .boolean => sub_boolean
  | .binary => sub_binary | .null => sub_null

/-- A literal is a restriction of `Ω`, because a literal restricts its base. -/
theorem sub_literal (k : GroundKind) (x : k.Carrier) : Sub (literalCodec k x) Ω :=
  sub_restrict (sub_baseCodec k) (inL k x)

/-- A traversal keeps an inclusion of graphs. -/
theorem traverse_sub {α β : Type} {f g : α → Option β} (h : ∀ x y, f x = some y → g x = some y)
    {xs ys} (ht : traverse f xs = some ys) : traverse g xs = some ys :=
  traverse_eq_some.mpr ((traverse_eq_some.mp ht).imp (fun _ _ => h _ _))

/-- `encSet` keeps an inclusion of graphs. -/
theorem encSet_sub {α : Type} {c d : Codec} (h : Sub c d) {inj : α → Value} {S : NEFinset α}
    {a : Attr} (he : encSet c inj S = some a) : encSet d inj S = some a := by
  rw [← encSet_congr (c := c) (fun x hx => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (encSet_elem he x hx)
    rw [hy, h.1 _ _ hy])]
  exact he

/-- `decSet` keeps an inclusion of graphs. -/
theorem decSet_sub {α : Type} {c d : Codec} (h : Sub c d) {inj : α → Attr} {S : NEFinset α}
    {v : Value} (hp : decSet c inj S = some v) : decSet d inj S = some v := by
  rw [← decSet_congr (c := c) (fun x hx => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (decSet_elem hp x hx)
    rw [hy, h.2 _ _ hy])]
  exact hp

/-- A set over a restriction of `Ω` is a restriction of `Ω`. -/
theorem sub_setCodec {c : Codec} (h : Sub c Ω) : Sub (setCodec c) Ω := by
  refine ⟨fun v a he => ?_, fun a v hp => ?_⟩
  · rcases setCodec_e_eq.mp he with ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩
    · rw [Ωe_strSet]; exact encSet_sub h hS
    · rw [Ωe_numSet]; exact encSet_sub h hS
    · rw [Ωe_binSet]; exact encSet_sub h hS
  · rcases setCodec_p_eq.mp hp with ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩
    · rw [Ωp_ss]; exact decSet_sub h hS
    · rw [Ωp_ns]; exact decSet_sub h hS
    · rw [Ωp_bs]; exact decSet_sub h hS

/-- A zipped traversal whose every row codec is included in `Ω` is a traversal of `Ω`. -/
theorem forall₂_zip_e : ∀ (ds : List Codec) (vs : List Value) (as : List Attr),
    ds.length = vs.length → (∀ c ∈ ds, Sub c Ω) →
    List.Forall₂ (fun (cv : Codec × Value) a => cv.1.e cv.2 = some a) (ds.zip vs) as →
    List.Forall₂ (fun v a => Ω.e v = some a) vs as
  | [], [], _, _, _, h => by cases h; exact .nil
  | d :: ds, v :: vs, a :: as, hl, hd, .cons h1 h2 =>
      .cons ((hd d (by simp)).1 _ _ h1)
        (forall₂_zip_e ds vs as (by simpa using hl) (fun c hc => hd c (by simp [hc])) h2)
  | [], _ :: _, _, hl, _, _ => nomatch hl
  | _ :: _, [], _, hl, _, _ => nomatch hl
  | _ :: _, _ :: _, [], _, _, h => nomatch h

/-- …and the same on the read side. -/
theorem forall₂_zip_p : ∀ (ds : List Codec) (as : List Attr) (vs : List Value),
    ds.length = as.length → (∀ c ∈ ds, Sub c Ω) →
    List.Forall₂ (fun (ca : Codec × Attr) v => ca.1.p ca.2 = some v) (ds.zip as) vs →
    List.Forall₂ (fun a v => Ω.p a = some v) as vs
  | [], [], _, _, _, h => by cases h; exact .nil
  | d :: ds, a :: as, v :: vs, hl, hd, .cons h1 h2 =>
      .cons ((hd d (by simp)).2 _ _ h1)
        (forall₂_zip_p ds as vs (by simpa using hl) (fun c hc => hd c (by simp [hc])) h2)
  | [], _ :: _, _, hl, _, _ => nomatch hl
  | _ :: _, [], _, hl, _, _ => nomatch hl
  | _ :: _, _ :: _, [], _, _, h => nomatch h

/-- A list whose every slot codec is a restriction of `Ω` is a restriction of `Ω`. -/
theorem sub_listCodec {pre suf : List Codec} {sp : Option Codec}
    (hpre : ∀ c ∈ pre, Sub c Ω) (hsp : ∀ c ∈ sp, Sub c Ω) (hsuf : ∀ c ∈ suf, Sub c Ω) :
    Sub (listCodec pre sp suf) Ω := by
  have hrow : ∀ n ds, slotsL pre sp suf n = some ds → ∀ c ∈ ds, Sub c Ω := fun n ds h c hc => by
    rcases slotsL_mem pre sp suf n ds h c hc with h1 | h1 | h1
    · exact hpre c h1
    · exact hsp c h1
    · exact hsuf c h1
  refine ⟨fun v a he => ?_, fun a v hp => ?_⟩
  · cases v with
    | arr vs =>
      simp only [listCodec, alignL, Option.map_eq_some_iff, Option.bind_eq_some_iff] at he
      obtain ⟨as, ⟨ps, ⟨ds, hds, rfl⟩, ht⟩, rfl⟩ := he
      rw [Ωe_arr, traverse_eq_some.mpr (forall₂_zip_e ds vs as
        (slotsL_length _ _ _ _ _ hds) (hrow _ _ hds) (traverse_eq_some.mp ht))]
      rfl
    | _ => exact nomatch he
  · cases a with
    | l as =>
      simp only [listCodec, alignL, Option.map_eq_some_iff, Option.bind_eq_some_iff] at hp
      obtain ⟨vs, ⟨ps, ⟨ds, hds, rfl⟩, ht⟩, rfl⟩ := hp
      rw [Ωp_l, traverse_eq_some.mpr (forall₂_zip_p ds as vs
        (slotsL_length _ _ _ _ _ hds) (hrow _ _ hds) (traverse_eq_some.mp ht))]
      rfl
    | _ => exact nomatch hp


/-- The selector returns the answer of one option, and nothing else. -/
theorem select_some {A B : Type} {os : List Codec} {run : Codec → A → Option B} {x : A} {y : B}
    (h : select os run x = some y) :
    ∃ o ∈ os, run o x = some y := by
  obtain ⟨o, ho, -, hr⟩ := select_admits h
  exact ⟨o, ho, hr⟩

/-- A union of restrictions of `Ω` is a restriction of `Ω`, because the selector returns the
    answer of one option. -/
theorem sub_altCodec {os : List Codec} (h : ∀ o ∈ os, Sub o Ω) (μ : Option Member) :
    Sub (altCodec os μ) Ω := by
  refine ⟨fun v a he => ?_, fun a v hp => ?_⟩
  · obtain ⟨o, ho, he⟩ := select_some he; exact (h o ho).1 _ _ he
  · obtain ⟨o, ho, hp⟩ := select_some hp; exact (h o ho).2 _ _ hp

/-- A filter that keeps every element is the set. -/
theorem filter_eq_self_on {S : Finset Name} {p : Name → Bool} (h : ∀ k ∈ S, p k = true) :
    S.filter (p ·) = S := by
  ext k
  simp only [Finset.mem_filter]
  exact ⟨fun hk => hk.1, fun hk => ⟨hk, h k hk⟩⟩

/-- An object whose every slot and open block is a restriction of `Ω` is a restriction of `Ω`. -/
theorem sub_bodySem (fields : Finset Name) (f : {k // k ∈ fields} → ObjectSlot)
    (w : Option Term) {ρ : List Codec} (hf : ∀ k, Sub (fieldSem (f k) ρ).codec Ω)
    (hw : ∀ c ∈ rcOf (wildSem w ρ), Sub c Ω) : Sub (bodySem (.mk fields f w) ρ) Ω := by
  refine ⟨fun v a he => ?_, fun a v hp => ?_⟩
  · obtain ⟨keys, g, g', rfl, rfl, -, hg⟩ := objectCodecCore_e_inv he
    rw [Ωe_map, funImage_eq (f := g') (fun k => ?_)]
    · rfl
    have hk := funImage_some hg k
    obtain ⟨c, hc, hce⟩ := Option.bind_eq_some_iff.mp hk
    exact (entryCodec_of (Q := fun c => Sub c Ω) hf hw hc).1 _ _ hce
  · cases a with
    | m keys g =>
      simp only [bodySem, objectCodec, objectCodecCore, carriedCodec, Option.map_eq_some_iff,
        Option.bind_eq_some_iff] at hp
      obtain ⟨q, ⟨p', hmA, hr⟩, rfl⟩ := hp
      cases hmA
      obtain ⟨-, d, hd, rfl⟩ := objRead_eq.mp hr
      rw [Ωp_m]
      have hS : keys = keys.filter (keepB (wildSem w ρ) ⟨fields, fun k => fieldSem (f k) ρ⟩ ·) :=
        (filter_eq_self_on (fun k _ => keepB_wild w _ k)).symm
      rw [funImage_record_congr hS (g' := fun k : {k // k ∈ keys.filter
          (keepB (wildSem w ρ) ⟨fields, fun k => fieldSem (f k) ρ⟩ ·)} =>
            (entryCodec ⟨fields, fun k => fieldSem (f k) ρ⟩ (rcOf (wildSem w ρ)) k.1).bind
              (fun c => c.p (g ⟨k.1, (Finset.mem_filter.mp k.2).1⟩))) (fun k h h' => ?_), hd]
      · rfl
      have hk := funImage_some hd ⟨k, h'⟩
      rw [hk]
      obtain ⟨c, hc, hcp⟩ := Option.bind_eq_some_iff.mp hk
      exact (entryCodec_of (Q := fun c => Sub c Ω) hf hw hc).2 _ _ hcp
    | _ => exact nomatch hp

/-! ## Held-free terms -/

mutual
/-- A term is **held-free** when no `held` occurs in the term. A held-free term does not change
    the carrier, so the term is a restriction of `opaque`. -/
def HF : Term → Prop
  | .held _ _ _ _ => False
  | .refine t _ => HF t
  | .mu t => HF t
  | .list pre sp suf => HFL pre ∧ HFO sp ∧ HFL suf
  | .object b => HFB b
  | .union os => HFL os
  | .set t => HF t
  | .string | .number | .boolean | .binary | .null | .literal _ _ | .opaq
  | .never | .var _ => True
/-- A body is held-free when each slot and the open block are held-free. -/
def HFB : Body → Prop
  | .mk _ f w => (∀ k, HFS (f k)) ∧ HFO w
/-- A slot is held-free when the slot's term is held-free. -/
def HFS : ObjectSlot → Prop
  | .req t => HF t
  | .optional t => HF t
/-- Each term of the list is held-free. -/
def HFL : List Term → Prop
  | [] => True
  | t :: ts => HF t ∧ HFL ts
/-- The optional term is held-free where the term is present. -/
def HFO : Option Term → Prop
  | none => True
  | some t => HF t
end

mutual
/-- **Confluence.** The denotation of a held-free term is a restriction of `Ω`, on both halves,
    over an environment of restrictions of `Ω`. -/
theorem sub_denoteIn : ∀ t : Term, HF t → ∀ ρ : List Codec, (∀ i, Sub (envAt ρ i) Ω) →
    Sub (denote t ρ) Ω
  | .string, _, _, _ => sub_string
  | .number, _, _, _ => sub_number
  | .boolean, _, _, _ => sub_boolean
  | .binary, _, _, _ => sub_binary
  | .null, _, _, _ => sub_null
  | .literal k x, _, _, _ => sub_literal k x
  | .set t, h, ρ, henv => sub_setCodec (sub_denoteIn t h ρ henv)
  | .opaq, _, _, _ => ⟨fun _ _ h => h, fun _ _ h => h⟩
  | .never, _, _, _ => sub_empty
  | .var i, _, _, henv => henv i
  -- each stage is a restriction by the body's case at the stage before, and the limit reads a
  -- stage at each input
  | .mu b, h, ρ, henv => by
      have hs : ∀ n, Sub (muStage (fun c => denote b (c :: ρ)) n) Ω := fun n => by
        induction n with
        | zero => exact sub_empty
        | succ n ih =>
          exact sub_denoteIn b h (_ :: ρ) fun i => match i with
            | 0 => ih
            | i + 1 => henv i
      exact ⟨fun v a he => (hs _).1 v a he, fun a v hp => (hs _).2 a v hp⟩
  | .held _ _ _ _, h, _, _ => h.elim
  | .refine t q, h, ρ, henv => sub_restrict (sub_denoteIn t h ρ henv) q.eval
  | .list pre sp suf, ⟨h1, h2, h3⟩, ρ, henv =>
      sub_listCodec (sub_denoteList pre h1 ρ henv) (sub_denoteOpt sp h2 ρ henv)
        (sub_denoteList suf h3 ρ henv)
  | .object b, h, ρ, henv => sub_body b h ρ henv
  | .union os, h, ρ, henv => sub_altCodec (sub_denoteList os h ρ henv) _
/-- …at a body. -/
theorem sub_body : ∀ b : Body, HFB b → ∀ ρ : List Codec, (∀ i, Sub (envAt ρ i) Ω) →
    Sub (bodySem b ρ) Ω
  | .mk fields f w, ⟨hf, hw⟩, ρ, henv =>
      sub_bodySem fields f w (fun k => sub_slot (f k) (hf k) ρ henv) (sub_wild w hw ρ henv)
/-- …at a slot. -/
theorem sub_slot : ∀ s : ObjectSlot, HFS s → ∀ ρ : List Codec, (∀ i, Sub (envAt ρ i) Ω) →
    Sub (fieldSem s ρ).codec Ω
  | .req t, h, ρ, henv => sub_denoteIn t h ρ henv
  | .optional t, h, ρ, henv => sub_denoteIn t h ρ henv
/-- …at an open block. -/
theorem sub_wild : ∀ w : Option Term, HFO w → ∀ ρ : List Codec, (∀ i, Sub (envAt ρ i) Ω) →
    ∀ c ∈ rcOf (wildSem w ρ), Sub c Ω
  | none, _, _, _ => fun _ hc => nomatch hc
  | some t, h, ρ, henv => fun c hc => by cases hc; exact sub_denoteIn t h ρ henv
/-- …at a list of terms. -/
theorem sub_denoteList : ∀ ts : List Term, HFL ts → ∀ ρ : List Codec,
    (∀ i, Sub (envAt ρ i) Ω) → ∀ c ∈ denoteList ts ρ, Sub c Ω
  | [], _, _, _ => fun _ hc => nomatch hc
  | t :: ts, ⟨h1, h2⟩, ρ, henv => fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact sub_denoteIn t h1 ρ henv
      · exact sub_denoteList ts h2 ρ henv c hc
/-- …at an optional term. -/
theorem sub_denoteOpt : ∀ o : Option Term, HFO o → ∀ ρ : List Codec,
    (∀ i, Sub (envAt ρ i) Ω) → ∀ c ∈ denoteOpt o ρ, Sub c Ω
  | none, _, _, _ => fun _ hc => nomatch hc
  | some t, h, ρ, henv => fun c hc => by cases hc; exact sub_denoteIn t h ρ henv
end

/-- **Confluence**, closed: the denotation of a held-free term is a restriction of `Ω`. -/
theorem sub_denote (t : Term) (h : HF t) : Sub (denote t) Ω :=
  sub_denoteIn t h [] fun _ => sub_empty

/-- **(W)**: a held-free term writes only what `opaque` writes. -/
theorem confluence_W {t : Term} (h : HF t) {v a} (he : (denote t).e v = some a) :
    (denote .opaq).e v = some a := (sub_denote t h).1 _ _ he

/-- **(R)**: a held-free term reads only what `opaque` reads. -/
theorem confluence_R {t : Term} (h : HF t) {a v} (hp : (denote t).p a = some v) :
    (denote .opaq).p a = some v := (sub_denote t h).2 _ _ hp



/-- The image of a nonempty set under `some` is the set. -/
theorem neSetImage_id {α : Type} [DecidableEq α] (S : NEFinset α) :
    neSetImage (fun x => some x) S = some S := by
  refine neSetImage_eq_setImage.mpr (setImage_eq (fun _ _ => rfl)
    (fun _ _ _ _ _ h1 h2 => Option.some.inj (h1.trans h2.symm)) (fun y => ?_))
  simp

/-! ## A set over a restriction of `Ω`, element by element

A restriction of `Ω` writes a string as `S`, a number as `N` and a byte string as `B`, and reads
them back the same way. So a set over one writes and reads exactly where each element does: the
element map is injective and lands in one wire family by construction. The meet's `set` row reads
these. -/

/-- A restriction of `Ω` writes a string as `S`. -/
theorem sub_e_str {c : Codec} (h : Sub c Ω) {s : String} {a : Attr}
    (he : c.e (.str s) = some a) : a = .s s := by
  have := h.1 _ _ he; rw [Ωe_str] at this; exact (Option.some.inj this).symm

/-- …a number as `N`. -/
theorem sub_e_num {c : Codec} (h : Sub c Ω) {x : WFNumeral} {a : Attr}
    (he : c.e (.num x) = some a) : a = .n x := by
  have := h.1 _ _ he; rw [Ωe_num] at this; exact (Option.some.inj this).symm

/-- …a byte string as `B`. -/
theorem sub_e_bin {c : Codec} (h : Sub c Ω) {b : Bytes} {a : Attr}
    (he : c.e (.bin b) = some a) : a = .b b := by
  have := h.1 _ _ he; rw [Ωe_bin] at this; exact (Option.some.inj this).symm

/-- **Over a restriction of `Ω`, a set writes exactly where every element does.** -/
theorem setCodec_e_isSome_of_sub {c : Codec} (h : Sub c Ω) (v : Value) :
    ((setCodec c).e v).isSome = true ↔
      (match v with
        | .strSet S => ∀ s ∈ S.1, (c.e (.str s)).isSome = true
        | .numSet S => ∀ x ∈ S.1, (c.e (.num x)).isSome = true
        | .binSet S => ∀ b ∈ S.1, (c.e (.bin b)).isSome = true
        | _ => False) := by
  cases v
  case strSet S =>
    refine ⟨fun he s hs => ?_, fun hall => ?_⟩
    · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp he; exact encSet_elem ha s hs
    · have hc : neSetImage (fun x => (c.e (Value.str x)).bind sC.out) S =
          neSetImage (fun x => some x) S := neSetImage_congr fun x hx => by
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall x hx)
        rw [ha, sub_e_str h ha]; rfl
      show (encSet c Value.str S).isSome = true
      unfold encSet; rw [hc, neSetImage_id]; rfl
  case numSet S =>
    refine ⟨fun he s hs => ?_, fun hall => ?_⟩
    · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp he; exact encSet_elem ha s hs
    · obtain ⟨x₀, hx₀⟩ := S.2
      have hS : neSetImage (fun x => (c.e (Value.num x)).bind sC.out) S = none :=
        neSetImage_none (setImage_none_of hx₀ (by
          obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
          rw [ha, sub_e_num h ha]; rfl))
      have hN : neSetImage (fun x => (c.e (Value.num x)).bind nC.out) S =
          neSetImage (fun x => some x) S := neSetImage_congr fun x hx => by
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall x hx)
        rw [ha, sub_e_num h ha]; rfl
      show (encSet c Value.num S).isSome = true
      unfold encSet; rw [hS, hN, neSetImage_id]; rfl
  case binSet S =>
    refine ⟨fun he s hs => ?_, fun hall => ?_⟩
    · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp he; exact encSet_elem ha s hs
    · obtain ⟨x₀, hx₀⟩ := S.2
      have hS : neSetImage (fun x => (c.e (Value.bin x)).bind sC.out) S = none :=
        neSetImage_none (setImage_none_of hx₀ (by
          obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
          rw [ha, sub_e_bin h ha]; rfl))
      have hN : neSetImage (fun x => (c.e (Value.bin x)).bind nC.out) S = none :=
        neSetImage_none (setImage_none_of hx₀ (by
          obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
          rw [ha, sub_e_bin h ha]; rfl))
      have hB : neSetImage (fun x => (c.e (Value.bin x)).bind bC.out) S =
          neSetImage (fun x => some x) S := neSetImage_congr fun x hx => by
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall x hx)
        rw [ha, sub_e_bin h ha]; rfl
      show (encSet c Value.bin S).isSome = true
      unfold encSet; rw [hS, hN, hB, neSetImage_id]; rfl
  all_goals exact ⟨(fun h => nomatch h), (fun h => h.elim)⟩

/-- A restriction of `Ω` reads `S` as a string. -/
theorem sub_p_s {c : Codec} (h : Sub c Ω) {s : String} {v : Value}
    (hp : c.p (.s s) = some v) : v = .str s := by
  have := h.2 _ _ hp; rw [Ωp_s] at this; exact (Option.some.inj this).symm

/-- …`N` as a number. -/
theorem sub_p_n {c : Codec} (h : Sub c Ω) {x : WFNumeral} {v : Value}
    (hp : c.p (.n x) = some v) : v = .num x := by
  have := h.2 _ _ hp; rw [Ωp_n] at this; exact (Option.some.inj this).symm

/-- …`B` as a byte string. -/
theorem sub_p_b {c : Codec} (h : Sub c Ω) {b : Bytes} {v : Value}
    (hp : c.p (.b b) = some v) : v = .bin b := by
  have := h.2 _ _ hp; rw [Ωp_b] at this; exact (Option.some.inj this).symm

/-- **Over a restriction of `Ω`, a set reads exactly where every element does.** -/
theorem setCodec_p_isSome_of_sub {c : Codec} (h : Sub c Ω) (a : Attr) :
    ((setCodec c).p a).isSome = true ↔
      (match a with
        | .ss S => ∀ s ∈ S.1, (c.p (.s s)).isSome = true
        | .ns S => ∀ x ∈ S.1, (c.p (.n x)).isSome = true
        | .bs S => ∀ b ∈ S.1, (c.p (.b b)).isSome = true
        | _ => False) := by
  cases a
  case ss S =>
    refine ⟨fun he s hs => ?_, fun hall => ?_⟩
    · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp he; exact decSet_elem hw s hs
    · have hc : neSetImage (fun x => (c.p (Attr.s x)).bind vStr) S =
          neSetImage (fun x => some x) S := neSetImage_congr fun x hx => by
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hall x hx)
        rw [hw, sub_p_s h hw]; rfl
      show (decSet c Attr.s S).isSome = true
      unfold decSet; rw [hc, neSetImage_id]; rfl
  case ns S =>
    refine ⟨fun he s hs => ?_, fun hall => ?_⟩
    · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp he; exact decSet_elem hw s hs
    · obtain ⟨x₀, hx₀⟩ := S.2
      have hS : neSetImage (fun x => (c.p (Attr.n x)).bind vStr) S = none :=
        neSetImage_none (setImage_none_of hx₀ (by
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
          rw [hw, sub_p_n h hw]; rfl))
      have hN : neSetImage (fun x => (c.p (Attr.n x)).bind vNum) S =
          neSetImage (fun x => some x) S := neSetImage_congr fun x hx => by
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hall x hx)
        rw [hw, sub_p_n h hw]; rfl
      show (decSet c Attr.n S).isSome = true
      unfold decSet; rw [hS, hN, neSetImage_id]; rfl
  case bs S =>
    refine ⟨fun he s hs => ?_, fun hall => ?_⟩
    · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp he; exact decSet_elem hw s hs
    · obtain ⟨x₀, hx₀⟩ := S.2
      have hS : neSetImage (fun x => (c.p (Attr.b x)).bind vStr) S = none :=
        neSetImage_none (setImage_none_of hx₀ (by
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
          rw [hw, sub_p_b h hw]; rfl))
      have hN : neSetImage (fun x => (c.p (Attr.b x)).bind vNum) S = none :=
        neSetImage_none (setImage_none_of hx₀ (by
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
          rw [hw, sub_p_b h hw]; rfl))
      have hB : neSetImage (fun x => (c.p (Attr.b x)).bind vBin) S =
          neSetImage (fun x => some x) S := neSetImage_congr fun x hx => by
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hall x hx)
        rw [hw, sub_p_b h hw]; rfl
      show (decSet c Attr.b S).isSome = true
      unfold decSet; rw [hS, hN, hB, neSetImage_id]; rfl
  all_goals exact ⟨(fun h => nomatch h), (fun h => h.elim)⟩

end Calculus
