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
(`read_agree`). `uAtAct_of_HF` discharges (U) where the union acts for a held-free union of
lawful options, with no certificate. `admAAt_of_HF` discharges the agreement conjunct of the
read-side meet row at held-free terms.

`held` is the one constructor outside the result. An adapter changes the carrier, so it is
not a restriction of `opaque`. `held_violates_W` and `held_violates_R` are the control:
`decimalHeld` writes `"1"` as the number `1`, which `opaque` does not.
-/

namespace Calculus

/-- Graph inclusion of two codecs on both halves: a restriction of `d` to the domains of `c`. -/
def Sub (c d : Codec) : Prop :=
  (∀ v a, c.e v = some a → d.e v = some a) ∧ (∀ a v, c.p a = some v → d.p a = some v)

/-- `opaque`'s fuel-free codec, under the short name that the inclusion lemmas use. -/
noncomputable abbrev Ω : Codec := opaqCodecω

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

/-- `Ω` writes an array element by element, through `Ω` itself. -/
theorem Ωe_arr (vs : List Value) : Ω.e (.arr vs) = (traverse Ω.e vs).map Attr.l := by
  show (opaqCodec (Value.depthL vs + 1)).e (.arr vs) = _
  rw [opaqCodec_e_arr]
  show (traverse (opaqCodec (Value.depthL vs)).e vs).map Attr.l = _
  rw [traverse_congr (fun x hx => opaq_e_agree x _ _ (depth_le_depthL hx) (Nat.le_refl _))]
  rfl

/-- `Ω` reads a list element by element, through `Ω` itself. -/
theorem Ωp_l (as : List Attr) : Ω.p (.l as) = (traverse Ω.p as).map Value.arr := by
  show (opaqCodec (Attr.depthL as + 1)).p (.l as) = _
  rw [opaqCodec_p_l]
  show (traverse (opaqCodec (Attr.depthL as)).p as).map Value.arr = _
  rw [traverse_congr (fun x hx => opaq_p_agree x _ _ (depth_le_depthLA hx) (Nat.le_refl _))]
  rfl

/-- `Ω` writes a map entry by entry, through `Ω` itself. -/
theorem Ωe_map (keys : Finset Name) (g : {k // k ∈ keys} → Value) :
    Ω.e (.map keys g) = (funImage fun k => Ω.e (g k)).map (Attr.m keys) := by
  obtain ⟨n, hn⟩ : ∃ n, Value.depth (.map keys g) = n + 1 := ⟨_, rfl⟩
  show (opaqCodec (Value.depth (.map keys g))).e _ = _
  rw [hn, opaqCodec_e_map]
  show (funImage fun k => (opaqCodec n).e (g k)).map (Attr.m keys) = _
  congr 2; funext k
  have := Value.depth_map_entry (f := g) k
  exact opaq_e_agree (g k) _ _ (by omega) (Nat.le_refl _)

/-- `Ω` reads a map entry by entry, through `Ω` itself. -/
theorem Ωp_m (keys : Finset Name) (g : {k // k ∈ keys} → Attr) :
    Ω.p (.m keys g) = (funImage fun k => Ω.p (g k)).map (Value.map keys) := by
  obtain ⟨n, hn⟩ : ∃ n, Attr.depth (.m keys g) = n + 1 := ⟨_, rfl⟩
  show (opaqCodec (Attr.depth (.m keys g))).p _ = _
  rw [hn, opaqCodec_p_m]
  show (funImage fun k => (opaqCodec n).p (g k)).map (Value.map keys) = _
  congr 2; funext k
  have := Attr.depth_map_entry (f := g) k
  exact opaq_p_agree (g k) _ _ (by omega) (Nat.le_refl _)

/-- `Ω` writes a string set through `encSet` over `Ω` itself. -/
theorem Ωe_strSet (S : NEFinset String) : Ω.e (.strSet S) = encSet Ω Value.str S := by
  show (opaqCodec 2).e _ = _
  rw [opaqCodec_e_strSet]; show encSet (opaqCodec 1) Value.str S = _
  simp only [encSet, show ∀ x : String, (opaqCodec 1).e (Value.str x) = Ω.e (Value.str x)
    from fun x => rfl]
/-- `Ω` writes a number set through `encSet` over `Ω` itself. -/
theorem Ωe_numSet (S : NEFinset WFNumeral) : Ω.e (.numSet S) = encSet Ω Value.num S := by
  show (opaqCodec 2).e _ = _
  rw [opaqCodec_e_numSet]; show encSet (opaqCodec 1) Value.num S = _
  simp only [encSet, show ∀ x : WFNumeral, (opaqCodec 1).e (Value.num x) = Ω.e (Value.num x)
    from fun x => rfl]
/-- `Ω` writes a binary set through `encSet` over `Ω` itself. -/
theorem Ωe_binSet (S : NEFinset Bytes) : Ω.e (.binSet S) = encSet Ω Value.bin S := by
  show (opaqCodec 2).e _ = _
  rw [opaqCodec_e_binSet]; show encSet (opaqCodec 1) Value.bin S = _
  simp only [encSet, show ∀ x : Bytes, (opaqCodec 1).e (Value.bin x) = Ω.e (Value.bin x)
    from fun x => rfl]
/-- `Ω` reads `SS` through `decSet` over `Ω` itself. -/
theorem Ωp_ss (S : NEFinset String) : Ω.p (.ss S) = decSet Ω Attr.s S := by
  show (opaqCodec 2).p _ = _
  rw [opaqCodec_p_ss]; show decSet (opaqCodec 1) Attr.s S = _
  simp only [decSet, show ∀ x : String, (opaqCodec 1).p (Attr.s x) = Ω.p (Attr.s x)
    from fun x => rfl]
/-- `Ω` reads `NS` through `decSet` over `Ω` itself. -/
theorem Ωp_ns (S : NEFinset WFNumeral) : Ω.p (.ns S) = decSet Ω Attr.n S := by
  show (opaqCodec 2).p _ = _
  rw [opaqCodec_p_ns]; show decSet (opaqCodec 1) Attr.n S = _
  simp only [decSet, show ∀ x : WFNumeral, (opaqCodec 1).p (Attr.n x) = Ω.p (Attr.n x)
    from fun x => rfl]
/-- `Ω` reads `BS` through `decSet` over `Ω` itself. -/
theorem Ωp_bs (S : NEFinset Bytes) : Ω.p (.bs S) = decSet Ω Attr.b S := by
  show (opaqCodec 2).p _ = _
  rw [opaqCodec_p_bs]; show decSet (opaqCodec 1) Attr.b S = _
  simp only [decSet, show ∀ x : Bytes, (opaqCodec 1).p (Attr.b x) = Ω.p (Attr.b x)
    from fun x => rfl]


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
theorem select_some {A B : Type} {os : List OptionSem} {adm : OptionSem → A → Bool}
    {run : OptionSem → A → Option B} {x : A} {y : B} (h : select os adm run x = some y) :
    ∃ o ∈ os, run o x = some y := by
  unfold select at h
  split at h
  · next o ho => exact ⟨o, List.mem_of_mem_filter (ho ▸ List.mem_singleton_self o), h⟩
  · exact nomatch h

/-- A union of restrictions of `Ω` is a restriction of `Ω`, because the selector returns the
    answer of one option. -/
theorem sub_altCodec {os : List OptionSem} (h : ∀ o ∈ os, Sub o.c Ω) (μ : Option Member) :
    Sub (altCodec os μ) Ω := by
  refine ⟨fun v a he => ?_, fun a v hp => ?_⟩
  · obtain ⟨o, ho, he⟩ := select_some he; exact (h o ho).1 _ _ he
  · obtain ⟨o, ho, hp⟩ := select_some hp; exact (h o ho).2 _ _ hp

/-- An object whose every slot and open block is a restriction of `Ω` is a restriction of `Ω`. -/
theorem sub_bodySem (fields : Finset Name) (f : {k // k ∈ fields} → ObjectSlot)
    (w : Option Term) (hf : ∀ k, Sub (fieldSem (f k)).codec Ω)
    (hw : ∀ c ∈ rcOf (wildSem w), Sub c Ω) : Sub (bodySem (.mk fields f w)) Ω := by
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
      have hS : keys = keys.filter (keepB (wildSem w) ⟨fields, fun k => fieldSem (f k)⟩ ·) := by
        rw [show keepB (wildSem w) _ = fun _ => true from funext (keepB_wild w _)]; simp
      rw [funImage_record_congr hS (g' := fun k : {k // k ∈ keys.filter
          (keepB (wildSem w) ⟨fields, fun k => fieldSem (f k)⟩ ·)} =>
            (entryCodec ⟨fields, fun k => fieldSem (f k)⟩ (rcOf (wildSem w)) k.1).bind
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
  | .held _ _ _ => False
  | .refine t _ => HF t
  | .lazy t => HF t
  | .list pre sp suf => HFL pre ∧ HFO sp ∧ HFL suf
  | .object b => HFB b
  | .union os => HFL os
  | .string | .number | .boolean | .binary | .null | .literal _ _ | .set _ | .opaq
  | .never => True
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
/-- **Confluence.** The denotation of a held-free term is a restriction of `Ω`, on both halves. -/
theorem sub_denote : ∀ t : Term, HF t → Sub (denote t) Ω
  | .string, _ => sub_string
  | .number, _ => sub_number
  | .boolean, _ => sub_boolean
  | .binary, _ => sub_binary
  | .null, _ => sub_null
  | .literal k x, _ => sub_literal k x
  | .set b, _ => sub_setBase b
  | .opaq, _ => ⟨fun _ _ h => h, fun _ _ h => h⟩
  | .never, _ => sub_empty
  | .held _ _ _, h => h.elim
  | .refine t q, h => sub_restrict (sub_denote t h) q.eval
  | .lazy t, h => (sub_denote t h)
  | .list pre sp suf, ⟨h1, h2, h3⟩ =>
      sub_listCodec (sub_denoteList pre h1) (sub_denoteOpt sp h2) (sub_denoteList suf h3)
  | .object b, h => sub_body b h
  | .union os, h => sub_altCodec (sub_optionSems os h) _
/-- …at a body. -/
theorem sub_body : ∀ b : Body, HFB b → Sub (bodySem b) Ω
  | .mk fields f w, ⟨hf, hw⟩ =>
      sub_bodySem fields f w (fun k => sub_slot (f k) (hf k)) (sub_wild w hw)
/-- …at a slot. -/
theorem sub_slot : ∀ s : ObjectSlot, HFS s → Sub (fieldSem s).codec Ω
  | .req t, h => sub_denote t h
  | .optional t, h => sub_denote t h
/-- …at an open block. -/
theorem sub_wild : ∀ w : Option Term, HFO w → ∀ c ∈ rcOf (wildSem w), Sub c Ω
  | none, _ => fun _ hc => nomatch hc
  | some t, h => fun c hc => by cases hc; exact sub_denote t h
/-- …at a list of terms. -/
theorem sub_denoteList : ∀ ts : List Term, HFL ts → ∀ c ∈ denoteList ts, Sub c Ω
  | [], _ => fun _ hc => nomatch hc
  | t :: ts, ⟨h1, h2⟩ => fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact sub_denote t h1
      · exact sub_denoteList ts h2 c hc
/-- …at an optional term. -/
theorem sub_denoteOpt : ∀ o : Option Term, HFO o → ∀ c ∈ denoteOpt o, Sub c Ω
  | none, _ => fun _ hc => nomatch hc
  | some t, h => fun c hc => by cases hc; exact sub_denote t h
/-- …at the options of a union. -/
theorem sub_optionSems : ∀ ts : List Term, HFL ts → ∀ o ∈ optionSems ts, Sub o.c Ω
  | [], _ => fun _ ho => nomatch ho
  | t :: ts, ⟨h1, h2⟩ => fun o ho => by
      rcases List.mem_cons.mp ho with rfl | ho
      · exact sub_denote t h1
      · exact sub_optionSems ts h2 o ho
end

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
/-- `Ω` writes every attribute: its write side is onto. -/
theorem Ω_onto : ∀ a : Attr, ∃ v, Ω.e v = some a
  | .s x => ⟨.str x, rfl⟩
  | .n x => ⟨.num x, rfl⟩
  | .b x => ⟨.bin x, rfl⟩
  | .bool x => ⟨.bool x, rfl⟩
  | .null => ⟨.null, rfl⟩
  | .ss S => ⟨.strSet S, by
      rw [Ωe_strSet]; unfold encSet
      rw [show (fun x : String => (Ω.e (Value.str x)).bind sC.out) = fun x => some x from rfl,
        neSetImage_id]⟩
  | .ns S => ⟨.numSet S, by
      rw [Ωe_numSet]; unfold encSet
      rw [neSetImage_none_all (f := fun x : WFNumeral => (Ω.e (Value.num x)).bind sC.out) S
          (fun _ => rfl),
        show (fun x : WFNumeral => (Ω.e (Value.num x)).bind nC.out) = fun x => some x from rfl,
        neSetImage_id]⟩
  | .bs S => ⟨.binSet S, by
      rw [Ωe_binSet]; unfold encSet
      rw [neSetImage_none_all (f := fun x : Bytes => (Ω.e (Value.bin x)).bind sC.out) S
          (fun _ => rfl),
        neSetImage_none_all (f := fun x : Bytes => (Ω.e (Value.bin x)).bind nC.out) S
          (fun _ => rfl),
        show (fun x : Bytes => (Ω.e (Value.bin x)).bind bC.out) = fun x => some x from rfl,
        neSetImage_id]; rfl⟩
  | .l as => by
      obtain ⟨vs, hvs⟩ := Ω_ontoL as
      exact ⟨.arr vs, by rw [Ωe_arr, hvs]; rfl⟩
  | .m keys g => by
      have h := fun k => Ω_onto (g k)
      refine ⟨.map keys (fun k => Classical.choose (h k)), ?_⟩
      rw [Ωe_map, funImage_eq (f := g) (fun k => Classical.choose_spec (h k))]; rfl
/-- …and `Ω` writes every list of attributes. -/
theorem Ω_ontoL : ∀ as : List Attr, ∃ vs, traverse Ω.e vs = some as
  | [] => ⟨[], rfl⟩
  | a :: as => by
      obtain ⟨v, hv⟩ := Ω_onto a
      obtain ⟨vs, hvs⟩ := Ω_ontoL as
      exact ⟨v :: vs, by simp only [traverse, hv, hvs]⟩
end

/-- `Ω` reads only canonical attributes: `e ∘ p = id` on `dom(p)`. -/
theorem Ω_canon {a : Attr} {t : Value} (h : Ω.p a = some t) : Ω.e t = some a :=
  lawful_opaqCodecω.can_roundTrip (Ω_onto a) h

/-- **(U) where the union acts, with no certificate.** The options are attempted, lawful, and
    included in `Ω`; `Ω` is lawful, so its graph is the one inverse pair every option reads. -/
theorem ubw_of_sub (os : List OptionSem)
    (hf : ∀ o ∈ os, Lawful o.c ∧ Sub o.c Ω ∧ (∀ v, o.admitV v = (o.c.e v).isSome) ∧
      (∀ a, o.admitA a = (o.c.p a).isSome)) : UniqueBothWays os := by
  have hΩ := lawful_opaqCodecω
  -- at a pair of `Ω`, each option admits the attribute exactly when it admits the value
  have key : ∀ t a, Ω.e t = some a → os.filter (·.admitA a) = os.filter (·.admitV t) := by
    intro t a hta
    refine List.filter_congr (fun o ho => ?_)
    obtain ⟨hl, hs, hV, hA⟩ := hf o ho
    rw [hV, hA]
    cases hp : o.c.p a with
    | some w =>
        have hw : Ω.p a = some w := hs.2 _ _ hp
        rw [hΩ.retract hta] at hw; cases hw
        simpa using (hl.canon hp).symm
    | none =>
        cases he : o.c.e t with
        | none => rfl
        | some a' =>
            have := hs.1 _ _ he; rw [hta] at this; cases this
            rw [hl.retract he] at hp; exact nomatch hp
  refine ⟨?_, ?_⟩
  · intro o ho t a hsel he
    rw [key t a ((hf o ho).2.1.1 _ _ he)]; exact hsel
  · intro o ho a t a' hsel hp he
    have hpa : Ω.p a = some t := (hf o ho).2.1.2 _ _ hp
    have hta : Ω.e t = some a := Ω_canon hpa
    rw [← key t a hta]; exact hsel

/-- Each member of a held-free list is held-free. -/
theorem HFL_mem : ∀ {ts : List Term}, HFL ts → ∀ t ∈ ts, HF t
  | [], _, _, h => nomatch h
  | _ :: _, ⟨h1, h2⟩, t, hm => by
      rcases List.mem_cons.mp hm with rfl | hm
      · exact h1
      · exact HFL_mem h2 t hm

/-- **`UAtAct` is free for a held-free union of lawful options.** No certificate. -/
theorem uAtAct_of_HF {opts : List Term} (h : HFL opts) (hl : ∀ t ∈ opts, Lawful (denote t)) :
    UAtAct opts := by
  refine ubw_of_sub _ (fun o ho => ?_)
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ho
  exact ⟨hl t ht, sub_denote t (HFL_mem h t ht), fun _ => rfl, fun _ => rfl⟩


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
  rw [denote_opaq, show opaqCodecω.e (.str "1") = some (.s "1") from rfl] at this
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
  rw [denote_opaq, show opaqCodecω.p (.n (WFNumeral.of "1")) = some (.num (WFNumeral.of "1"))
    from rfl] at this
  exact nomatch this


/-- The control of the control: `decimalHeld` is not held-free, so `confluence_W` does not
    apply to it. -/
theorem not_HF_decimalHeld : ¬ HF decimalHeld := id

end Calculus
