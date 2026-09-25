import Calculus.Typing

/-!
# §5 — Soundness

The theorem. `Obligations t` collects the semantic rule premises: `(held)` cancellation laws,
and `(union)` pairwise compatibility, at every stage of each enclosing `mu`. The current term
language has no read adapter, so every typed term whose obligations hold satisfies retract, canon
and writes.

The induction runs over open terms. `soundnessIn` takes an environment of lawful codecs for the
variables, and a `mu` builds its stages from the body's soundness at the stage before.
`soundness` is the closed case.

The ground-term cases are wrappers over the certified combinators,
where the per-construction lemmas — proved and open — now live.
-/

namespace Calculus

/-! ## Obligations -/


/-- A term's rest policy keeps every name. -/
theorem wildSem_ne_drop (w : Option Term) {ρ : List Codec} : wildSem w ρ ≠ .drop :=
  Option.casesOn (motive := fun w => wildSem w ρ ≠ .drop) w RestSem.noConfusion
    fun _ => RestSem.noConfusion

/-- **The union's obligation**: its options are pairwise compatible. -/
def PairwiseCompat (opts : List Term) (ρ : List Codec := []) : Prop :=
  ∀ s ∈ opts, ∀ t ∈ opts, Compat (denote s ρ) (denote t ρ)

mutual

/-- The doc's semantic rule premises.

    **Structural**, and it means what the specification means: the premises hold. The list
    companions exist because `∀ t' ∈ ts, Obligations t'` is not a structural recursion and
    `ObligationsList` is. -/
def Obligations : Term → (ρ : List Codec := []) → Prop
  -- `set` joins the leaves: its base is an index, so there is no subterm to carry premises.
  | .string, _ | .number, _ | .boolean, _ | .binary, _ | .null, _
  | .literal _ _, _ | .opaq, _ | .set _, _ | .never, _ | .var _, _ => True
  | .refine t' _, ρ => Obligations t' ρ
  | .list pre sp suf, ρ => ObligationsList pre ρ ∧ ObligationsOpt sp ρ ∧ ObligationsList suf ρ
  -- the caller-side term owes nothing: a restriction keeps the laws of any lawful codec
  | .held t' _ f g, ρ => Obligations t' ρ ∧ IsoCancels (denote t' ρ) f g
  | .object b, ρ => ObligationsBody b ρ
  | .union opts, ρ => ObligationsList opts ρ ∧ PairwiseCompat opts ρ
  -- the body's premises at each stage, given that the stage before is lawful
  | .mu b, ρ => ∀ n, Lawful (muStage (fun c => denote b (c :: ρ)) n) →
      Obligations b (muStage (fun c => denote b (c :: ρ)) n :: ρ)

/-- The payload's premises: every declared slot's, and the open block's. The companion
    `ObjectSlot` and the open block already had and the object row inlined. -/
def ObligationsBody : Body → (ρ : List Codec := []) → Prop
  | .mk _ f wild, ρ => (∀ k, ObligationsField (f k) ρ) ∧ ObligationsWild wild ρ

/-- A slot's premises are the current-schema term's premises. -/
def ObligationsField : ObjectSlot → (ρ : List Codec := []) → Prop
  | .req t', ρ => Obligations t' ρ
  | .optional t', ρ => Obligations t' ρ

def ObligationsWild : Option Term → (ρ : List Codec := []) → Prop
  | some t', ρ => Obligations t' ρ
  | none, _ => True

def ObligationsList : List Term → (ρ : List Codec := []) → Prop
  | [], _ => True
  | t' :: ts, ρ => Obligations t' ρ ∧ ObligationsList ts ρ

def ObligationsOpt : Option Term → (ρ : List Codec := []) → Prop
  | none, _ => True
  | some t', ρ => Obligations t' ρ

end

/-! ### The companions, as the quantifiers the rest of the file speaks in

`ObligationsList` is what made the recursion structural; `∀ t ∈ ts, Obligations t` is what every
proof below wants. These are that bridge, and they are the entire cost of losing the fuel. -/

theorem obligationsList_iff {ρ : List Codec} : ∀ {ts : List Term},
    ObligationsList ts ρ ↔ ∀ t ∈ ts, Obligations t ρ
  | [] => by simp [ObligationsList]
  | t :: ts => by
      simp only [ObligationsList, List.mem_cons, forall_eq_or_imp]
      exact and_congr_right (fun _ => obligationsList_iff)

theorem obligationsOpt_iff {ρ : List Codec} : ∀ {tail : Option Term},
    ObligationsOpt tail ρ ↔ ∀ t ∈ tail, Obligations t ρ
  | none => by simp [ObligationsOpt]
  | some _ => by simp [ObligationsOpt]

/-! ### The premises, per rule

`Obligations` is a recursion over the term, so at each rule it *is* the proposition that
rule's premises make — but only up to unfolding, and every case of the two inductions
below was re-stating that proposition to name it. These are that unfolding, once per
rule, and they read as the rule they belong to. Each is `:= h`. -/

namespace Obligations

theorem array {t} (h : Obligations (.array t)) : Obligations t := h.2.1
theorem record {t} (h : Obligations (.record t)) : Obligations t := h.2
theorem refine {t q ρ} (h : Obligations (.refine t q) ρ) : Obligations t ρ := h

theorem tuple {ts tail} (h : Obligations (.tuple ts tail)) :
    (∀ t ∈ ts, Obligations t) ∧ (∀ t ∈ tail, Obligations t) :=
  ⟨obligationsList_iff.mp h.1, obligationsOpt_iff.mp h.2.1⟩

/-- §3 `(list)`: one premise per declared position, the spread's, and the suffix's. -/
theorem list {pre sp suf ρ} (h : Obligations (.list pre sp suf) ρ) :
    (∀ t ∈ pre, Obligations t ρ) ∧ (∀ t ∈ sp, Obligations t ρ) ∧ (∀ t ∈ suf, Obligations t ρ) :=
  ⟨obligationsList_iff.mp h.1, obligationsOpt_iff.mp h.2.1, obligationsList_iff.mp h.2.2⟩

/-- §3 `(held)`: the subterm's premises, and the iso cancelling on the carriers. -/
theorem held {t P f g ρ} (h : Obligations (.held t P f g) ρ) :
    Obligations t ρ ∧ IsoCancels (denote t ρ) f g := h

/-- §5 `(union)`: one premise per option, and pairwise compatibility. -/
theorem union {opts ρ} (h : Obligations (.union opts) ρ) :
    (∀ t ∈ opts, Obligations t ρ) ∧ PairwiseCompat opts ρ :=
  ⟨obligationsList_iff.mp h.1, h.2⟩

end Obligations

/-! ## Ground-term lemmas -/

theorem lawful_string : Lawful (denote .string) := by
  simp only [denote]; exact lawful_stringCodec

theorem lawful_boolean : Lawful (denote .boolean) := by
  simp only [denote]; exact lawful_booleanCodec

theorem lawful_null : Lawful (denote .null) := by
  simp only [denote]; exact lawful_nullCodec

theorem lawful_binary : Lawful (denote .binary) := by
  simp only [denote]; exact lawful_binaryCodec

theorem lawful_number : Lawful (denote .number) := by
  simp only [denote]; exact lawful_numberCodec

/-- One where there were two, at every base rather than the two commonest. -/
theorem lawful_literal (k : GroundKind) (x : k.Carrier) :
    Lawful (denote (.literal k x)) := by
  simp only [denote]; exact lawful_literalCodec k x

/-! ## Inversion and dispatch helpers -/

theorem TypedList.forall : ∀ {ts Ts}, TypedList ts Ts → ∀ t ∈ ts, ∃ T μ, Typed t T μ
  | _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, _, h⟩
      · exact TypedList.forall hs t ht'

theorem TypedListμ.forall : ∀ {ts Ts μs}, TypedListμ ts Ts μs →
    ∀ t ∈ ts, ∃ T μ, Typed t T μ
  | _, _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, _, h⟩
      · exact TypedListμ.forall hs t ht'

theorem TypedListM.forall : ∀ {ts Ts}, TypedListM ts Ts →
    ∀ t ∈ ts, ∃ T, Typed t T (some .M)
  | _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, h⟩
      · exact TypedListM.forall hs t ht'

theorem unanimous_spec : ∀ {l : List (Option Member)} {m},
    unanimous l = some m → ∀ x ∈ l, x = some m
  | [], _, h => nomatch h
  | μ :: μs, m, h => by
      replace h : (if μs.all (· == μ) then μ else none) = some m := h
      cases hall : μs.all (· == μ) with
      | false => rw [hall] at h; exact nomatch h
      | true =>
        rw [hall] at h
        replace h : μ = some m := h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h
        · have hbe := List.all_eq_true.mp hall x hx'
          have hxeq : x = μ := eq_of_beq hbe
          rw [hxeq, h]

mutual

/-- Typing's member index is the syntactic one — exactly, both sides. -/
theorem typed_μSyn : ∀ {t T μ}, Typed t T μ → μSyn t = μ
  -- `rfl`, where this used to be the rule's `hμ`. The member is a function of the *index* on
  -- both sides now — `μSyn` reads `GroundKind.member`, and so does the rule.
  | _, _, _, .literal _ _ => rfl
  | _, _, _, .string => rfl
  | _, _, _, .number => rfl
  | _, _, _, .boolean => rfl
  | _, _, _, .null => rfl
  | _, _, _, .binary => rfl
  | _, _, _, .set _ => rfl
  | _, _, _, .never => rfl
  | _, _, _, .list _ _ _ => rfl
  | _, _, _, .held h' => by have ih := typed_μSyn h'; exact ih
  | _, _, _, .refine h' => by have ih := typed_μSyn h'; exact ih
  | _, _, _, .opaq => rfl
  | _, _, _, .var _ => rfl
  | _, _, _, .mu _ _ => rfl
  | _, _, _, .object _ _ => rfl
  | _, _, _, .union h => by
      show unanimous (μSynList _) = unanimous _
      rw [typedListμ_μSyn h]

theorem typedListμ_μSyn : ∀ {ts Ts μs}, TypedListμ ts Ts μs → μSynList ts = μs
  | _, _, _, .nil => rfl
  | _, _, _, .cons h hs => by
      show μSyn _ :: μSynList _ = _
      rw [typed_μSyn h, typedListμ_μSyn hs]

end

/-! ## The theorem

One induction. A ground case is lawful outright, and a case with one subterm applies its
combinator lemma to the induction hypothesis. A case with a list of subterms reads the
hypothesis off the mapped list. What is left in each case is the combinator lemma it cites. -/

-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- Soundness over an environment: every term whose obligations hold at `ρ`, and whose free
    variables `ρ` gives lawful codecs, satisfies retract, canon and writes. One walk of the
    derivation, one unpacking of the obligations; each case dispatches to its combinator lemma. -/
theorem soundnessIn : ∀ {t T μ} (ρ : List Codec), Typed t T μ → Obligations t ρ →
    (∀ i, Lawful (envAt ρ i)) → Lawful (denote t ρ)
  | t, T, μ, ρ, h, hob, henv => by
    cases h with
    | literal k ls => exact (lawful_literalCodec k ls)
    -- the bottom's domains are empty, so every law holds vacuously
    | never => exact Lawful.empty
    | string => exact lawful_stringCodec
    | number => exact lawful_numberCodec
    | boolean => exact lawful_booleanCodec
    | null => exact lawful_nullCodec
    | binary => exact lawful_binaryCodec
    | opaq => exact lawful_opaq
    | var i => exact henv i
    -- each stage is lawful by the body's soundness at the stage before, and the guard carries
    -- the laws to the limit
    | @mu b T' μ' hg h' =>
      refine lawful_muCodec (contractive_body hg ρ) fun n => ?_
      induction n with
      | zero => exact Lawful.empty
      | succ n ih =>
        exact soundnessIn (_ :: ρ) h' (hob n ih) fun i => match i with
          | 0 => ih
          | i + 1 => henv i
    -- a leaf now: `setCodec` is lawful at each of the four bases, so `(set)` discharges the
    -- way the ground rules do rather than by wrapping a subterm's soundness
    | set b => exact (lawful_setCodec (lawful_setBase b))
    | @refine t' T' μ' p h' =>
      exact (soundnessIn ρ h' hob henv).restrict p.eval
    | @held t' I' μ' P f g h' =>
      exact ((soundnessIn ρ h' hob.1 henv).through hob.2).restrict _
    | @list pre Tpre sp Tsp suf Tsuf hp hs hf =>
      have ihp : ∀ t' ∈ pre, Lawful (denote t' ρ) := fun t' ht' => by
        obtain ⟨T', μ', hμ'⟩ := TypedList.forall hp t' ht'
        exact soundnessIn ρ hμ' ((Obligations.list hob).1 t' ht') henv
      have ihsp : ∀ t' ∈ sp, Lawful (denote t' ρ) := fun t' ht' => by
        cases sp with
        | none => exact nomatch ht'
        | some tx =>
          replace ht' : some tx = some t' := ht'
          cases ht'
          cases hs with
          | some hμ' => exact soundnessIn ρ hμ' ((Obligations.list hob).2.1 t' rfl) henv
      have ihf : ∀ t' ∈ suf, Lawful (denote t' ρ) := fun t' ht' => by
        obtain ⟨T', μ', hμ'⟩ := TypedList.forall hf t' ht'
        exact soundnessIn ρ hμ' ((Obligations.list hob).2.2 t' ht') henv
      rw [denote_list, denoteList_eq, denoteOpt_eq, denoteList_eq]
      exact lawful_listCodec
          (List.forall_mem_map.mpr fun t' ht' => ihp t' ht')
          (forall_mem_map_option fun t' ht' => ihsp t' ht')
          (List.forall_mem_map.mpr fun t' ht' => ihf t' ht')
    -- The field table is indexed by the declared names, so the induction hypothesis is
    -- read off at a key rather than at a membership, and ~~TypedFields.forall~~ — which
    -- existed to walk the row — is not needed. Nor is a `Nodup` to transport.
    | @object body bind R μs hfields hrest =>
      -- the payload is taken apart once, here: the field lemmas below read a key set and a
      -- function on it, and `objectCodec` is stated over those
      cases body with | mk fields ff wild =>
      simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at hfields hrest
      -- a field's codec is its term's denotation, and its laws reach it unchanged
      have ihf : ∀ k, Lawful (fieldSem (ff k) ρ).codec := by
        intro k
        have hobf := hob.1 k
        obtain ⟨t', hty', hshape⟩ := TypedField.term (hfields k)
        rcases hshape with heq | heq
        · rw [heq] at hobf ⊢
          exact soundnessIn ρ hty' hobf henv
        · rw [heq] at hobf ⊢; exact soundnessIn ρ hty' hobf henv
      have ihr : ∀ c, wildSem wild ρ = .codec c → Lawful c := by
        intro c hcr
        cases hrest with
        | none => exact nomatch hcr
        | @some t' T' μ' hty =>
          replace hcr : RestSem.codec (denote t' ρ) = RestSem.codec c := hcr
          cases hcr
          exact soundnessIn ρ hty hob.2 henv
      rw [denote_object_table, fieldTable]
      exact lawful_objectCodec ihf ihr (wildSem_ne_drop _)
    | @union opts Ts μs hlist =>
      have ihs : ∀ t' ∈ opts, Lawful (denote t' ρ) := fun t' ht' => by
        obtain ⟨T', μ', hμ'⟩ := TypedListμ.forall hlist t' ht'
        exact soundnessIn ρ hμ' ((Obligations.union hob).1 t' ht') henv
      have hC : ∀ o ∈ opts.map fun t' => denote t' ρ,
          ∀ o' ∈ opts.map fun t' => denote t' ρ, Compat o o' := by
        refine List.forall_mem_map.mpr fun s hs => List.forall_mem_map.mpr fun t' ht' => ?_
        exact hob.2 s hs t' ht'
      have hW : ∀ m, unanimous (opts.map fun t' => (denote t' ρ).μ) = some m →
          ∀ o ∈ opts.map fun t' => denote t' ρ,
            ∀ t' a, o.e t' = some a → a.member = m := by
        intro m hm
        refine List.forall_mem_map.mpr fun tx htx t' a he' => ?_
        exact (ihs tx htx).writes
          (unanimous_spec hm _ (List.mem_map.mpr ⟨tx, htx, rfl⟩)) he'
      rw [denote_union_sems, denoteList_eq, denoteμs_eq_map]
      exact lawful_altCodec (List.forall_mem_map.mpr fun t' ht' => ihs t' ht') hC hW

termination_by t _ _ _ _ _ _ => Term.depth t
decreasing_by term_depth_wf

/-- Soundness: every closed term whose obligations hold satisfies retract, canon and writes. -/
theorem soundness {t T μ} (h : Typed t T μ) (hob : Obligations t) : Lawful (denote t) :=
  soundnessIn [] h hob fun _ => Lawful.empty

/-! ## The denotation's held set is the judgement's

    `Carrier` bounds `e` and `p` by the *codec's* `T`. `typed_TSub` bounds the codec's
    `T` by the *judgement's*, which is what makes §3's `⊢ c : T ⇝ μ` a claim about the
    denotation rather than a decoration. The two compose into `typed_e_mem` and
    `typed_p_mem` below.

    Each rule's held set is built by the same former the combinator's `T` field uses, so
    most cases are pointwise. Three are not: `tuple` (positional through `align`),
    `object` (name-dispatched) and `opaque` (a fixpoint), and each gets a helper. -/

/-- The uniform tail of a `(tuple-tail)`: every trailing position is the tail's. -/
theorem alignTail_TSub {c : Codec} {T' : Held} (ih : ∀ v, c.T v → T' v) :
    ∀ {vs ps}, align [] (some c) vs = some ps → (∀ p ∈ ps, p.1.T p.2) → ∀ x ∈ vs, T' x
  | [], _, _, _, x, hx => absurd hx (by simp)
  | v :: vs, ps, hal, hall, x, hx => by
      replace hal : ((align [] (some c) vs).map ((c, v) :: ·)) = some ps := hal
      cases hal' : align ([] : List Codec) (some c) vs with
      | none => rw [hal'] at hal; exact nomatch hal
      | some ps' =>
        rw [hal'] at hal
        replace hal : some ((c, v) :: ps') = some ps := hal
        cases hal
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ih x (hall (c, x) (List.mem_cons_self))
        · exact alignTail_TSub ih hal'
            (fun p hp => hall p (List.mem_cons_of_mem _ hp)) x hx'

/-- …and the same tail, built rather than read. `alignTail_TSub` takes an `align` that
    already succeeded; the converse has to *produce* one, and that is the whole difference
    between the two directions here: on this side `align`'s success is a conclusion, not a
    hypothesis. It never fails at a tail, because a tail accepts any length. -/
theorem alignTail_T {c : Codec} {T' : Held} (ih : ∀ v, T' v → c.T v) :
    ∀ (vs : List Value), (∀ x ∈ vs, T' x) →
      ∃ ps, align [] (some c) vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2
  | [], _ => ⟨[], rfl, by simp⟩
  | v :: vs, hall => by
      obtain ⟨ps, hal, hps⟩ :=
        alignTail_T ih vs (fun x hx => hall x (List.mem_cons_of_mem _ hx))
      refine ⟨(c, v) :: ps, ?_, ?_⟩
      · simp only [align, hal, Option.map_some]
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ih v (hall v (List.mem_cons_self))
        · exact hps p hp'

/-- `align`'s positional pairing is §3's `T₁ × … × Tₙ`, one position at a time. -/
theorem align_TSub {tail Tt} (hopt : TypedOpt tail Tt)
    (ihTail : ∀ t' ∈ tail, ∀ (T' : Held) (μ' : Option Member),
      Typed t' T' μ' → ∀ v, (denote t').T v → T' v) :
    ∀ {ts Ts}, TypedList ts Ts →
      (∀ t' ∈ ts, ∀ (T' : Held) (μ' : Option Member),
        Typed t' T' μ' → ∀ v, (denote t').T v → T' v) → ∀ {vs ps},
      align (ts.map denote) (tail.map denote) vs = some ps →
      (∀ p ∈ ps, p.1.T p.2) → HTuple Ts Tt vs
  | _, _, .nil, _, vs, ps, hal, hall => by
      cases hopt with
      | none =>
        show HTuple [] none vs
        cases vs with
        | nil => rfl
        | cons _ _ => exact nomatch hal
      | @some t' T' μ' hty =>
        show HTuple [] (some T') vs
        exact alignTail_TSub (ihTail _ rfl _ _ hty) hal hall
  | _, _, .cons hty hs, ih, vs, ps, hal, hall => by
      cases vs with
      | nil => exact nomatch hal
      | cons v vs' =>
        replace hal : (((align _ (tail.map denote) vs')).map
          ((denote _, v) :: ·)) = some ps := hal
        cases hal' : align _ (tail.map denote) vs' with
        | none => rw [hal'] at hal; exact nomatch hal
        | some ps' =>
          rw [hal'] at hal
          replace hal : some ((denote _, v) :: ps') = some ps := hal
          cases hal
          refine ⟨ih _ (List.mem_cons_self) _ _ hty v (hall _ (List.mem_cons_self)), ?_⟩
          exact align_TSub hopt ihTail hs
            (fun t' ht' => ih t' (List.mem_cons_of_mem _ ht')) hal'
            (fun p hp => hall p (List.mem_cons_of_mem _ hp))

/-- …and the positional pairing built from the held sets instead of read off them.

    **`HTuple` is what makes `align` total here**, and that is the content of this direction:
    the head lists are the same length by construction, and a tail accepts whatever is left,
    so the `none` rows of `align` are unreachable under the hypothesis. `align_TSub` never
    has to know that — it is handed the `some`. -/
theorem align_T_of_HTuple {tail Tt} (hopt : TypedOpt tail Tt)
    (ihTail : ∀ t' ∈ tail, ∀ (T' : Held) (μ' : Option Member),
      Typed t' T' μ' → ∀ v, T' v → (denote t').T v) :
    ∀ {ts Ts}, TypedList ts Ts →
      (∀ t' ∈ ts, ∀ (T' : Held) (μ' : Option Member),
        Typed t' T' μ' → ∀ v, T' v → (denote t').T v) →
      ∀ (vs : List Value), HTuple Ts Tt vs →
      ∃ ps, align (ts.map denote) (tail.map denote) vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2
  | _, _, .nil, _, vs, hall => by
      cases hopt with
      | none =>
        obtain rfl : vs = [] := hall
        exact ⟨[], rfl, by simp⟩
      | @some t' T' μ' hty =>
        exact alignTail_T (ihTail _ rfl _ _ hty) vs hall
  | _, _, @TypedList.cons tx tsx Tx Tsx μx hty hs, ih, vs, hall => by
      cases vs with
      | nil => exact nomatch hall
      | cons v vs' =>
        obtain ⟨ps, hal, hps⟩ :=
          align_T_of_HTuple hopt ihTail hs
            (fun x hx => ih x (List.mem_cons_of_mem _ hx)) vs' hall.2
        refine ⟨(denote tx, v) :: ps, ?_, ?_⟩
        · simp only [List.map_cons, align, hal, Option.map_some]
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact ih tx (List.mem_cons_self) _ _ hty v hall.1
          · exact hps p hp'

/-! #### The suffix, and the `list` shape that carries it

`align_TSub` and `align_T_of_HTuple` state the prefix-and-spread half. The suffix half is a
`Forall₂` against the zipped row, and `alignL_split` joins the two: an alignment of a
`list` IS an alignment of its prefix and spread beside a zip of its suffix, so neither
half is restated. -/

/-- The declared length of a judgement's row is the row's. -/
theorem TypedList.length_eq : ∀ {ts Ts}, TypedList ts Ts → ts.length = Ts.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => by simp [TypedList.length_eq hs]

/-- The suffix's positions, read off the zipped row. -/
theorem zipSuf_TSub :
    ∀ {suf Tsuf}, TypedList suf Tsuf →
      (∀ t' ∈ suf, ∀ (T' : Held) (μ' : Option Member),
        Typed t' T' μ' → ∀ v, (denote t').T v → T' v) →
      ∀ {back : List Value}, back.length = suf.length →
      (∀ p ∈ (suf.map denote).zip back, p.1.T p.2) →
      List.Forall₂ (fun T v => T v) Tsuf back
  | _, _, .nil, _, back, hlen, _ => by
      cases back with
      | nil => exact .nil
      | cons _ _ =>
          exact absurd hlen (by simp only [List.length_cons, List.length_nil]; omega)
  | _, _, @TypedList.cons t ts T Ts μ hty hs, ih, back, hlen, hall => by
      cases back with
      | nil => exact absurd hlen (by simp only [List.length_cons, List.length_nil]; omega)
      | cons b bs =>
        refine .cons (ih t (List.mem_cons_self) _ _ hty b (hall (denote t, b) ?_)) ?_
        · simp only [List.map_cons, List.zip_cons_cons]
          exact List.mem_cons_self
        · exact zipSuf_TSub hs (fun t' ht' => ih t' (List.mem_cons_of_mem _ ht'))
            (by simp only [List.length_cons] at hlen; omega)
            (fun p hp => hall p (by
              simp only [List.map_cons, List.zip_cons_cons]
              exact List.mem_cons_of_mem _ hp))

/-- …and the same suffix, built rather than read. -/
theorem zipSuf_T :
    ∀ {suf Tsuf}, TypedList suf Tsuf →
      (∀ t' ∈ suf, ∀ (T' : Held) (μ' : Option Member),
        Typed t' T' μ' → ∀ v, T' v → (denote t').T v) →
      ∀ {back : List Value}, List.Forall₂ (fun T v => T v) Tsuf back →
      back.length = suf.length ∧ ∀ p ∈ (suf.map denote).zip back, p.1.T p.2
  | _, _, .nil, _, back, hb => by
      cases hb; exact ⟨rfl, by simp⟩
  | _, _, @TypedList.cons t ts T Ts μ hty hs, ih, back, hb => by
      cases hb with
      | cons hhead htail =>
        obtain ⟨hlen, hall⟩ :=
          zipSuf_T hs (fun t' ht' => ih t' (List.mem_cons_of_mem _ ht')) htail
        refine ⟨by simpa using hlen, ?_⟩
        intro p hp
        simp only [List.map_cons, List.zip_cons_cons] at hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ih t (List.mem_cons_self) _ _ hty _ hhead
        · exact hall p hp'

/-- `alignL`'s pairing is §3's `(list)` held set, read off the alignment. -/
theorem alignL_TSub {pre Tpre sp Tsp suf Tsuf} (hp : TypedList pre Tpre)
    (hs : TypedOpt sp Tsp) (hf : TypedList suf Tsuf)
    (ihp : ∀ t' ∈ pre, ∀ (T' : Held) (μ' : Option Member),
      Typed t' T' μ' → ∀ v, (denote t').T v → T' v)
    (ihs : ∀ t' ∈ sp, ∀ (T' : Held) (μ' : Option Member),
      Typed t' T' μ' → ∀ v, (denote t').T v → T' v)
    (ihf : ∀ t' ∈ suf, ∀ (T' : Held) (μ' : Option Member),
      Typed t' T' μ' → ∀ v, (denote t').T v → T' v)
    {vs ps}
    (hal : alignL (pre.map denote) (sp.map denote) (suf.map denote) vs = some ps)
    (hall : ∀ p ∈ ps, p.1.T p.2) : HTupleL Tpre Tsp Tsuf vs := by
  obtain ⟨front, back, psF, rfl, hblen, halF, rfl⟩ :=
    alignL_split _ _ _ _ _ hal
  refine ⟨front, back, rfl, ?_, ?_⟩
  · exact zipSuf_TSub hf ihf (by simpa using hblen)
      (fun p hp => hall p (List.mem_append_right _ hp))
  · exact align_TSub hs ihs hp ihp halF (fun p hp => hall p (List.mem_append_left _ hp))

/-- …and the same held set built rather than read: the `list` aligns whenever it holds. -/
theorem alignL_T_of_HTupleL {pre Tpre sp Tsp suf Tsuf} (hp : TypedList pre Tpre)
    (hs : TypedOpt sp Tsp) (hf : TypedList suf Tsuf)
    (ihp : ∀ t' ∈ pre, ∀ (T' : Held) (μ' : Option Member),
      Typed t' T' μ' → ∀ v, T' v → (denote t').T v)
    (ihs : ∀ t' ∈ sp, ∀ (T' : Held) (μ' : Option Member),
      Typed t' T' μ' → ∀ v, T' v → (denote t').T v)
    (ihf : ∀ t' ∈ suf, ∀ (T' : Held) (μ' : Option Member),
      Typed t' T' μ' → ∀ v, T' v → (denote t').T v)
    {vs} (hh : HTupleL Tpre Tsp Tsuf vs) :
    ∃ ps, alignL (pre.map denote) (sp.map denote) (suf.map denote) vs = some ps
      ∧ ∀ p ∈ ps, p.1.T p.2 := by
  obtain ⟨front, back, rfl, hback, hfront⟩ := hh
  obtain ⟨hblen, hzip⟩ := zipSuf_T hf ihf hback
  obtain ⟨psF, halF, hpsF⟩ := align_T_of_HTuple hs ihs hp ihp front hfront
  refine ⟨psF ++ (suf.map denote).zip back, alignL_of_split (by simpa using hblen) halF, ?_⟩
  intro p hp
  rcases List.mem_append.mp hp with hp' | hp'
  · exact hpsF p hp'
  · exact hzip p hp'

/-- Every stage of `opaque` carries `HOpaque`. The stage is the budget on the *input's* depth, not
    a budget on the term. -/
theorem opaq_TSub : ∀ (fuel : Nat) (v : Value),
    (muStage opaqStep fuel).T v → HOpaque v
  | 0, _, h => nomatch h
  | fuel+1, v, h => by
    obtain ⟨o, ho, hT⟩ := h
    have ih := opaq_TSub fuel
    simp only [opaqOptions, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨s, rfl⟩ := hT; exact .str s
    · obtain ⟨b, rfl⟩ := hT; exact .bool b
    · obtain ⟨b, rfl⟩ := hT; exact .bin b
    · cases hT; exact .null
    · obtain ⟨d, rfl⟩ := hT; exact .num d
    · cases v <;> first
        | exact .strSet _ fun s hs => ih (Value.str s) (hT s hs)
        | exact .numSet _ fun d hd => ih (Value.num d) (hT d hd)
        | exact .binSet _ fun b hb => ih (Value.bin b) (hT b hb)
        | exact nomatch hT
    · cases v <;> first
        | exact .arr _ fun x hx => ih x (hT x hx)
        | exact nomatch hT
    · cases v <;> first
        | exact .map _ _ fun k => ih _ (hT k)
        | exact nomatch hT

/-- `opaque`'s held set — its write domain — lands in `HOpaque`: the stage that writes a value is
    on its carrier. -/
theorem opaq_TSubω (v : Value) :
    Ω.T v → HOpaque v := by
  intro h
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
  exact opaq_TSub _ v
    ((muStage_induct Carrier.empty (fun _ => carrier_opaqStep) (Value.depth v)).domE ha)

/-- A union option's held set is one of the rule's. -/
theorem TypedListμ.mem : ∀ {ts Ts μs}, TypedListμ ts Ts μs →
    ∀ t ∈ ts, ∃ T ∈ Ts, ∃ μ, Typed t T μ
  | _, _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, List.mem_cons_self, _, h⟩
      · obtain ⟨T', hT', μ', hty⟩ := TypedListμ.mem hs t ht'
        exact ⟨T', List.mem_cons_of_mem _ hT', μ', hty⟩

theorem TypedListM.mem : ∀ {ts Ts}, TypedListM ts Ts →
    ∀ t ∈ ts, ∃ T ∈ Ts, Typed t T (some .M)
  | _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨T', hT', hty⟩ := TypedListM.mem hs t ht'
        exact ⟨T', List.mem_cons_of_mem _ hT', hty⟩

/-- …and the option that answers for a held set, which is the lookup in the other direction.

    `TypedListμ.mem` goes from a *term* in the list to its held set; here a value is known to
    lie in one of the rule's held sets and the option holding it has to be produced. The two
    lists are built together by the same `cons`, so neither direction needs a premise — but
    membership in `Ts` names no term, so this cannot be `mem` applied backwards and is a
    recursion of its own. The denotation argument arrives as `ih` rather than being taken
    here, because the caller is the one with the depth measure. -/
theorem unionT_of_mem : ∀ {opts : List Term} {Ts μs}, TypedListμ opts Ts μs →
    (∀ t ∈ opts, ∀ (T : Held) (μ), Typed t T μ → ∀ v, T v → (denote t).T v) →
    ∀ (v : Value) (T : Held), T ∈ Ts → T v → ∃ t ∈ opts, (denote t).T v
  | _, _, _, .nil, _, _, _, hT, _ => nomatch hT
  | _, _, _, .cons hty hs, ih, v, T, hT, hv => by
    rcases List.mem_cons.mp hT with rfl | hT'
    · exact ⟨_, List.mem_cons_self, ih _ (List.mem_cons_self) _ _ hty v hv⟩
    · obtain ⟨t'', ht'', hd⟩ :=
        unionT_of_mem hs (fun x hx => ih x (List.mem_cons_of_mem _ hx)) v T hT' hv
      exact ⟨t'', List.mem_cons_of_mem _ ht'', hd⟩

/-- …and its twin where every option is at `M`. -/
theorem unionMT_of_mem : ∀ {opts : List Term} {Ts}, TypedListM opts Ts →
    (∀ t ∈ opts, ∀ (T : Held) (μ), Typed t T μ → ∀ v, T v → (denote t).T v) →
    ∀ (v : Value) (T : Held), T ∈ Ts → T v → ∃ t ∈ opts, (denote t).T v
  | _, _, .nil, _, _, _, hT, _ => nomatch hT
  | _, _, .cons hty hs, ih, v, T, hT, hv => by
    rcases List.mem_cons.mp hT with rfl | hT'
    · exact ⟨_, List.mem_cons_self, ih _ (List.mem_cons_self) _ _ hty v hv⟩
    · obtain ⟨t'', ht'', hd⟩ :=
        unionMT_of_mem hs (fun x hx => ih x (List.mem_cons_of_mem _ hx)) v T hT' hv
      exact ⟨t'', List.mem_cons_of_mem _ ht'', hd⟩

-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- The denotation's held set is inside the judgement's, at every fuel. -/
theorem typed_TSub : ∀ {t T μ}, Typed t T μ → ∀ v, (denote t).T v → T v
  | t, T, μ, h, v, hv => by
    cases h with
    | string | number | boolean | binary | null => exact hv
    -- `exact hv`, where this was a five-way split guarding against `simp` unfolding
    -- `numberCodec` into `Numeral.WF`'s decision procedure. The denotation's held set and the
    -- rule's are the same expression now — `HLit k ls` — so there is nothing to prove.
    | literal _ _ => exact hv
    | never => exact hv
    | opaq => exact opaq_TSubω v hv
    -- a closed variable is the bottom, and a `mu`'s index is its codec's held set
    | var _ => exact False.elim hv
    | mu _ _ => exact hv
    -- the base's codec holds exactly the base's held set (`SetBase.elem_T`), so the three
    -- wire families transport with no recursion left to do
    | set b =>
      cases b <;> cases v <;> first
        | exact Or.inl ⟨_, rfl, fun x hx => hv x hx⟩
        | exact Or.inr (Or.inl ⟨_, rfl, fun x hx => hv x hx⟩)
        | exact Or.inr (Or.inr ⟨_, rfl, fun x hx => hv x hx⟩)
        | exact nomatch hv
    | @list pre Tpre sp Tsp suf Tsuf hp hs hf =>
      rw [denote_list, denoteList_eq, denoteOpt_eq, denoteList_eq] at hv
      cases v
      case arr vs =>
        obtain ⟨ps, hal, hall⟩ := hv
        exact ⟨_, rfl, alignL_TSub hp hs hf
          (fun t' _ _ _ hty v hv => typed_TSub hty v hv)
          (fun t' _ _ _ hty v hv => typed_TSub hty v hv)
          (fun t' _ _ _ hty v hv => typed_TSub hty v hv) hal hall⟩
      all_goals exact absurd hv (by simp only [listCodec]; exact id)
    | @held t' I' μ' P f g h' =>
      exact ⟨typed_TSub h' (f v) hv.1, hv.2⟩
    | @refine t' T' μ' q h' => exact ⟨typed_TSub h' v hv.1, hv.2⟩
    | @object body bind R μs hfields hrest =>
      cases body with | mk fields ff wild =>
      simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at hfields hrest ⊢
      -- No case split on `v`: the object's `T` is `carriedCodec`'s, so it *hands over*
      -- the payload — a key set and a function on it, which is exactly `HObject`'s
      -- witness. The list representation had to take `v` apart to find one.
      obtain ⟨⟨keys, kvs⟩, hvp, hval, hall⟩ := hv
      refine ⟨keys, kvs, hvp, ?_, ?_⟩
      · -- every required binding's name is present, because its field is not `opt`
        intro k hreq
        have hty := hfields k
        have hno : ∀ c, fieldSem (ff k) ≠ FieldSem.opt c := by
          intro c hc
          obtain ⟨t', -, hshape⟩ := TypedField.term hty
          rcases hshape with heq | heq
          · rw [heq] at hc; exact nomatch hc
          · exact TypedField.not_optional hty hreq t' heq
        exact valPresentB_spec hval (MapOf.at_of_mem (m := ⟨fields, _⟩) k) hno
      · -- and every present name holds what its binding, or the open part, says
        intro k
        have hentry := hall k
        by_cases hk : k.1 ∈ fields
        · -- declared: the entry holds its field's set, and the binding is at the same key
          rw [dif_pos hk]
          simp only [objEntryT,
            MapOf.at_of_mem (m := (⟨fields, fun k => fieldSem (ff k)⟩ :
              MapOf FieldSem)) ⟨k.1, hk⟩] at hentry
          obtain ⟨t', hty', hshape⟩ := TypedField.term (hfields ⟨k.1, hk⟩)
          rcases hshape with heq | heq
          · rw [heq] at hentry; exact typed_TSub hty' _ hentry
          · rw [heq] at hentry; exact typed_TSub hty' _ hentry
        · -- undeclared: it falls to the open part
          rw [dif_neg hk]
          simp only [objEntryT, MapOf.at, dif_neg hk] at hentry
          obtain ⟨rc, hrc, hrcT⟩ := hentry
          cases hrest with
          | none => exact nomatch hrc
          | @some t' T'' μ'' hty' =>
            replace hrc : some (denote t') = some rc := hrc
            cases hrc
            exact ⟨T'', rfl, typed_TSub hty' _ hrcT⟩
    | @union opts Ts μs hlist =>
      simp only [denote, denoteList_eq, denoteμs_eq_map] at hv
      obtain ⟨o, ho, hT⟩ := hv
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      obtain ⟨T', hT', μ', hty⟩ := TypedListμ.mem hlist tx htx
      exact ⟨T', hT', typed_TSub hty v hT⟩

termination_by t _ _ _ _ _ => Term.depth t
decreasing_by term_depth_wf

-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- Every derivable term denotes a pair **on its carrier** — §3's `e : T ⇀ 𝔸`,
    `p : 𝔸 ⇀ T`. One walk of the derivation, dispatching to the `Carrier` lemmas, with
    `soundness` supplying the lawfulness that the `held` and `mu` cases need. -/
theorem carrier_denote : ∀ {t T μ}, Typed t T μ → Obligations t → Carrier (denote t)
  | t, T, μ, h, hob => by
    cases h with
    | literal k ls => exact carrier_literalCodec k ls
    | never => exact Carrier.empty
    | string => exact carrier_stringCodec
    | number => exact carrier_numberCodec
    | boolean => exact carrier_booleanCodec
    | null => exact carrier_nullCodec
    | binary => exact carrier_binaryCodec
    | set b => exact carrier_setCodec (carrier_setBase b)
    | @list pre Tpre sp Tsp suf Tsuf hp hs hf =>
      rw [denote_list, denoteList_eq, denoteOpt_eq, denoteList_eq]
      refine carrier_listCodec (List.forall_mem_map.mpr ?_) (forall_mem_map_option ?_)
        (List.forall_mem_map.mpr ?_)
      · intro t' ht'
        obtain ⟨T', μ', hty⟩ := TypedList.forall hp t' ht'
        exact carrier_denote hty ((Obligations.list hob).1 t' ht')
      · intro t' ht'
        cases sp with
        | none => exact nomatch ht'
        | some tx =>
          replace ht' : some tx = some t' := ht'
          cases ht'
          cases hs with
          | some hty => exact carrier_denote hty ((Obligations.list hob).2.1 t' rfl)
      · intro t' ht'
        obtain ⟨T', μ', hty⟩ := TypedList.forall hf t' ht'
        exact carrier_denote hty ((Obligations.list hob).2.2 t' ht')
    | @held t' I' μ' P f g h' =>
      exact carrier_restrict (carrier_through (carrier_denote h' hob.1)
        (soundness h' hob.1).core hob.2.2) _
    | @refine t' T' μ' p h' =>
      exact carrier_restrict (carrier_denote h' hob.refine) p.eval
    | opaq => exact carrier_opaq
    -- a closed variable is the bottom, and a lawful `mu` is on its held set, its write domain
    | var _ => exact Carrier.empty
    | @mu b T' μ' hg h' => exact carrier_muCodec (soundness (.mu hg h') hob)
    | @object body bind R μs hfields hrest =>
      cases body with | mk fields ff wild =>
      simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at hfields hrest
      have hsems : ∀ k : {k // k ∈ fields},
          Carrier (fieldSem (ff k)).codec := by
        intro k
        have hobf := hob.1 k
        obtain ⟨t', hty', hshape⟩ := TypedField.term (hfields k)
        rcases hshape with heq | heq
        · rw [heq] at hobf ⊢
          exact carrier_denote hty' hobf
        · rw [heq] at hobf ⊢; exact carrier_denote hty' hobf
      have hrc : ∀ rc, rcOf (wildSem wild) = some rc → Carrier rc := by
        intro rc hcr
        cases hrest with
        | none => exact nomatch hcr
        | @some t' T' μ' hty =>
          replace hcr : some (denote t') = some rc := hcr
          cases hcr
          exact carrier_denote hty hob.2
      exact carrier_objectCodec hsems hrc
    | @union opts Ts μs hlist =>
      rw [denote_union_sems, denoteList_eq]
      refine carrier_altCodec (List.forall_mem_map.mpr fun t' ht' => ?_)
      obtain ⟨T', μ', hty⟩ := TypedListμ.forall hlist t' ht'
      exact carrier_denote hty ((Obligations.union hob).1 t' ht')

termination_by t _ _ _ _ => Term.depth t
decreasing_by term_depth_wf
/-- §3's `e : T ⇀ 𝔸`, at the judgement's own index: a derivable term writes only
    values of the held set it names. -/
theorem typed_e_mem {t T μ} (h : Typed t T μ) (hob : Obligations t)
    {v a} (he : (denote t).e v = some a) : T v :=
  typed_TSub h v ((carrier_denote h hob).domE he)

/-- §3's `p : 𝔸 ⇀ T`, at the judgement's own index: a derivable term reads only into
    the held set it names. -/
theorem typed_p_mem {t T μ} (h : Typed t T μ) (hob : Obligations t)
    {a v} (hp : (denote t).p a = some v) : T v :=
  typed_TSub h v ((carrier_denote h hob).ranP hp)

/-- §3 `(alternate reader)`: an alternate reader over a derivable term preserves the three
    core laws under its coherence condition. -/
theorem extendRead_lawfulCore {t T μ} (ht : Typed t T μ) (hob : Obligations t)
    {r : Attr → Option Value} (hr : ReadsCoherently (denote t) r) :
    LawfulCore ((denote t).extendRead r) :=
  LawfulCore.extendRead (soundness ht hob).core hr.1

end Calculus
