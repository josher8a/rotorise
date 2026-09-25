import Calculus.Universal
import Calculus.DynamoDB

/-!
# Confluence: a held-free term is a restriction of `opaque`

A term with no `held` does not change the carrier. Each combinator either restricts its
subterm or composes subterms through the structure that `opaque` itself uses. So the write
graph and the read graph of a held-free term lie inside the graphs of `opaque`.
`confluence_W` and `confluence_R` state the two inclusions. `sub_denote` proves them by one
mutual induction over `Term`, `Body`, `ObjectSlot`, the list and the option.

`Sub c d` is the inclusion of graphs on both halves. The only case that reads a union is
`select_some`: the selector returns the answer of one option. The set cases go through
`encSet_congr` and `decSet_congr`.

The payoffs follow from one fact: `opaque`'s pair is a bijection between `Value` and `Attr`.
`Ω_onto` and `Ω_canon` prove the bijection. So two held-free terms that both write a value
write one attribute (`write_agree`), and two that both read an attribute read one value
(`read_agree`). `admAAt_of_HF` discharges the agreement conjunct of the read-side meet row at
held-free terms.

`held` is the one constructor outside the result. An adapter changes the carrier, so it is
not a restriction of `opaque`. `held_violates_W` and `held_violates_R` are the control:
`decimalHeld` writes `"1"` as the number `1`, which `opaque` does not.
-/

namespace Calculus

/-- Graph inclusion of two codecs on both halves: a restriction of `d` to the domains of `c`. -/
def Sub (c d : Codec) : Prop :=
  (∀ v a, c.e v = some a → d.e v = some a) ∧ (∀ a v, c.p a = some v → d.p a = some v)

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
  · simp only [Codec.restrict] at he; split at he
    · exact h.1 _ _ he
    · exact nomatch he
  · simp only [Codec.restrict, Option.bind_eq_some_iff] at hp
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

/-- Each set base is a restriction of `Ω`. -/
theorem sub_setBase (b : SetBase) : Sub (setCodec b.elem) Ω :=
  sub_setCodec (by cases b <;> first | exact sub_string | exact sub_number | exact sub_binary)

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
  | .string | .number | .boolean | .binary | .null | .literal _ _ | .set _ | .opaq
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
/-- **Below `opaque`, the read occupancy lies inside the write occupancy.** The rows agree
    under `Member.slot` at every base. A `held` is excluded: the write occupancy of a `held`
    is its caller-side term's and the read occupancy is its stored-side term's, two
    coordinates that need not agree. So `Orth1` asks the read question as well. -/
theorem occA_le_occV : ∀ (t : Term), HF t → ∀ (m : Member), occA t m = true → occV t m.slot = true
  | .string, _, m, h | .number, _, m, h | .boolean, _, m, h | .binary, _, m, h
  | .null, _, m, h => by
      cases m <;> simp_all [occA, occV, occOnly, Member.slot]
  | .literal k _, _, m, h => by
      cases k <;> cases m <;>
        simp_all [occA, occV, occOnly, Member.slot, GroundKind.slot, GroundKind.member]
  | .set b, _, m, h => by
      cases b <;> cases m <;>
        simp_all [occA, occV, occOnly, Member.slot, SetBase.slot, SetBase.member]
  | .list _ _ _, _, m, h | .object _, _, m, h => by
      cases m <;> simp_all [occA, occV, occOnly, Member.slot]
  | .never, _, _, h => by simp [occA, occNone] at h
  | .held _ _ _ _, hf, _, _ => nomatch hf
  | .refine t _, hf, m, h => occA_le_occV t hf m (by simpa [occA] using h)
  | .opaq, _, _, _ => by simp [occV, occTop]
  | .mu b, hf, m, h => by simpa [occV] using occA_le_occV b hf m (by simpa [occA] using h)
  | .var _, _, _, h => by simp [occA, occNone] at h
  | .union os, hf, m, h => by
      simp only [occA, occV] at h ⊢
      exact occAL_le_occVL os hf m h

/-- …and over the options of a union, where both sides are the join of the options'. -/
theorem occAL_le_occVL : ∀ (ts : List Term), HFL ts → ∀ (m : Member),
    occAL ts m = true → occVL ts m.slot = true
  | [], _, _, h => by simp [occAL] at h
  | t :: ts, hf, m, h => by
      simp only [occAL, occVL, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl (occA_le_occV t hf.1 m h)
      · exact Or.inr (occAL_le_occVL ts hf.2 m h)
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
  | .set b, _, _, _ => sub_setBase b
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



/-! ## Payoffs -/

/-- Two held-free terms that both write a value write one attribute. -/
theorem write_agree {s t : Term} (hs : HF s) (ht : HF t) {v a b}
    (ha : (denote s).e v = some a) (hb : (denote t).e v = some b) : a = b :=
  Option.some.inj ((confluence_W hs ha).symm.trans (confluence_W ht hb))

/-- Two held-free terms that both read an attribute read one value. -/
theorem read_agree {s t : Term} (hs : HF s) (ht : HF t) {a v w}
    (hv : (denote s).p a = some v) (hw : (denote t).p a = some w) : v = w :=
  Option.some.inj ((confluence_R hs hv).symm.trans (confluence_R ht hw))

/-- The image of a nonempty set under `some` is the set. -/
theorem neSetImage_id {α : Type} [DecidableEq α] (S : NEFinset α) :
    neSetImage (fun x => some x) S = some S := by
  refine neSetImage_eq_setImage.mpr (setImage_eq (fun _ _ => rfl)
    (fun _ _ _ _ _ h1 h2 => Option.some.inj (h1.trans h2.symm)) (fun y => ?_))
  simp

/-- The image of a nonempty set under a function that answers `none` everywhere is `none`. -/
theorem neSetImage_none_all {α β : Type} [DecidableEq β] {f : α → Option β} (S : NEFinset α)
    (h : ∀ x, f x = none) : neSetImage f S = none := by
  obtain ⟨x, hx⟩ := S.2
  exact neSetImage_none (setImage_none_of hx (h x))

mutual
/-- The value that `Ω` writes to an attribute, by structure. The witness of `Ω_onto` is this
    function and not a choice, so the map case names its preimage without `Classical.choose`. -/
def valueOfAttr : Attr → Value
  | .s x => .str x
  | .n x => .num x
  | .b x => .bin x
  | .bool x => .bool x
  | .null => .null
  | .ss S => .strSet S
  | .ns S => .numSet S
  | .bs S => .binSet S
  | .l as => .arr (valueOfAttrL as)
  | .m keys g => .map keys (fun k => valueOfAttr (g k))
/-- …and on a list of attributes. -/
def valueOfAttrL : List Attr → List Value
  | [] => []
  | a :: as => valueOfAttr a :: valueOfAttrL as
end

mutual
/-- `Ω` writes each attribute from `valueOfAttr`. -/
theorem Ω_e_valueOfAttr : ∀ a : Attr, Ω.e (valueOfAttr a) = some a
  | .s _ => rfl
  | .n _ => rfl
  | .b _ => rfl
  | .bool _ => rfl
  | .null => rfl
  | .ss S => by
      show Ω.e (.strSet S) = _
      rw [Ωe_strSet]; unfold encSet
      rw [show (fun x : String => (Ω.e (Value.str x)).bind sC.out) = fun x => some x from rfl,
        neSetImage_id]
  | .ns S => by
      show Ω.e (.numSet S) = _
      rw [Ωe_numSet]; unfold encSet
      rw [neSetImage_none_all (f := fun x : WFNumeral => (Ω.e (Value.num x)).bind sC.out) S
          (fun _ => rfl),
        show (fun x : WFNumeral => (Ω.e (Value.num x)).bind nC.out) = fun x => some x from rfl,
        neSetImage_id]
  | .bs S => by
      show Ω.e (.binSet S) = _
      rw [Ωe_binSet]; unfold encSet
      rw [neSetImage_none_all (f := fun x : Bytes => (Ω.e (Value.bin x)).bind sC.out) S
          (fun _ => rfl),
        neSetImage_none_all (f := fun x : Bytes => (Ω.e (Value.bin x)).bind nC.out) S
          (fun _ => rfl),
        show (fun x : Bytes => (Ω.e (Value.bin x)).bind bC.out) = fun x => some x from rfl,
        neSetImage_id]; rfl
  | .l as => by
      show Ω.e (.arr (valueOfAttrL as)) = _
      rw [Ωe_arr, Ω_e_valueOfAttrL as]; rfl
  | .m keys g => by
      show Ω.e (.map keys (fun k => valueOfAttr (g k))) = _
      rw [Ωe_map, funImage_eq (f := g) (fun k => Ω_e_valueOfAttr (g k))]; rfl
/-- …and each list of attributes from `valueOfAttrL`. -/
theorem Ω_e_valueOfAttrL : ∀ as : List Attr, traverse Ω.e (valueOfAttrL as) = some as
  | [] => rfl
  | a :: as => by simp only [valueOfAttrL, traverse, Ω_e_valueOfAttr a, Ω_e_valueOfAttrL as]
end

/-- `Ω` writes every attribute: its write side is onto. -/
theorem Ω_onto (a : Attr) : ∃ v, Ω.e v = some a := ⟨_, Ω_e_valueOfAttr a⟩

/-- `Ω` reads only canonical attributes: `e ∘ p = id` on `dom(p)`. -/
theorem Ω_canon {a : Attr} {t : Value} (h : Ω.p a = some t) : Ω.e t = some a :=
  lawful_opaq.can_roundTrip (Ω_onto a) h

/-- Each member of a held-free list is held-free. -/
theorem HFL_mem : ∀ {ts : List Term}, HFL ts → ∀ t ∈ ts, HF t
  | [], _, _, h => nomatch h
  | _ :: _, ⟨h1, h2⟩, t, hm => by
      rcases List.mem_cons.mp hm with rfl | hm
      · exact h1
      · exact HFL_mem h2 t hm

/-- The read-side meet row's agreement conjunct is free at held-free terms. -/
theorem admAAt_of_HF {x y z : Term} (hx : HF x) (hy : HF y) (hz : HF z)
    (h1 : ∀ a, AdmA z a = (AdmA x a && AdmA y a)) : AdmAAt x y z := by
  refine ⟨h1, fun a hxa hya => ?_⟩
  have hza : AdmA z a = true := by rw [h1, hxa, hya]; rfl
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp ((AdmA_exact x a).mp hxa)
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((AdmA_exact y a).mp hya)
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp ((AdmA_exact z a).mp hza)
  rw [hu, hw, hr, read_agree hz hx hr hu, read_agree hx hy hu hw]
  exact ⟨rfl, rfl⟩


/-! ## The false control: a `held` adapter is not a restriction of `opaque` -/

/-- `decimalHeld` writes the string `"1"` as the number `1`. -/
theorem decimalHeld_writes : (denote decimalHeld).e (.str "1") = some (.n (WFNumeral.of "1")) := by
  rfl

/-- **The false control, write side.** `decimalHeld` writes an attribute that `opaque` does not
    write at the same value, so `confluence_W` needs `HF`. -/
theorem held_violates_W :
    ¬ ∀ v a, (denote decimalHeld).e v = some a → (denote .opaq).e v = some a := by
  intro h
  have := h _ _ decimalHeld_writes
  rw [denote_opaq, show (muCodec opaqStep).e (.str "1") = some (.s "1") from rfl] at this
  exact nomatch this

/-- `decimalHeld` reads the number `1` as the string `"1"`. -/
theorem decimalHeld_reads : (denote decimalHeld).p (.n (WFNumeral.of "1")) = some (.str "1") := by
  rfl

/-- **The false control, read side.** `decimalHeld` reads a value that `opaque` does not read at
    the same attribute, so `confluence_R` needs `HF`. -/
theorem held_violates_R :
    ¬ ∀ a v, (denote decimalHeld).p a = some v → (denote .opaq).p a = some v := by
  intro h
  have := h _ _ decimalHeld_reads
  rw [denote_opaq, show (muCodec opaqStep).p (.n (WFNumeral.of "1"))
    = some (.num (WFNumeral.of "1")) from rfl] at this
  exact nomatch this


/-- The control of the control: `decimalHeld` is not held-free, so `confluence_W` does not
    apply to it. -/
theorem not_HF_decimalHeld : ¬ HF decimalHeld := id

/-- **The views do not certify the decimal adapter beside `string`.** Its caller side is
    `string`, so the caller-side views overlap. -/
theorem certPair_decimalHeld_string : certPair decimalHeld .string = false := by
  decide

end Calculus
