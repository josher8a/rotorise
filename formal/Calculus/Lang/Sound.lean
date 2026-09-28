import Calculus.Lang.Typing
import Calculus.Lang.Guarded

/-!
# §5 — Soundness, for every universe

The theorem. `Obligations t` collects the semantic rule premises: `(held)` cancellation laws,
`(union)` pairwise compatibility, the universe's set obligation, and the body's premises at every
stage of each enclosing `mu`. Every typed term whose obligations hold satisfies retract, canon and
writes, and lies on its carrier.

The induction runs over open terms. `soundnessIn` takes an environment of lawful codecs for the
variables, and a `mu` builds its stages from the body's soundness at the stage before.
`soundness` is the closed case. A universe supplies the laws of its primitives, of its formers
and of its top, and the positivity of its depths. The generic combinators supply the rest.
-/

namespace Calculus.Alg

variable {S : Syn} [Sem S] {α : Table S} {β : Table S.op}

/-! ## The companions, as mapped lists -/

/-- The options' codecs are the mapped denotation. -/
@[simp] theorem denoteList_eq {ρ : List S.C} :
    ∀ ts : List (Term S), denoteList α β ts ρ = ts.map (denote α β · ρ)
  | [] => rfl
  | t :: ts => by simp only [denoteList, List.map]; rw [denoteList_eq ts]

/-- The spread's codec is the mapped denotation. -/
@[simp] theorem denoteOpt_eq {ρ : List S.C} :
    ∀ tail : Option (Term S), denoteOpt α β tail ρ = tail.map (denote α β · ρ)
  | none => rfl
  | some _ => rfl

/-- The options' members are the mapped members. -/
@[simp] theorem denoteμs_eq_map {ρ : List S.C} : ∀ opts : List (Term S),
    denoteμs α β opts ρ = opts.map fun t => (denote α β t ρ).μ
  | [] => rfl
  | t :: ts => by simp only [denoteμs, List.map]; rw [denoteμs_eq_map ts]

/-- A term's open block keeps every name. -/
theorem wildSem_ne_drop (w : Option (Term S)) {ρ : List S.C} : wildSem α β w ρ ≠ .drop := by
  cases w <;> exact fun h => nomatch h

/-- A unanimous member is the member of every option. -/
theorem unanimous_spec {M : Type} [DecidableEq M] : ∀ {l : List (Option M)} {m},
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

/-! ## The theorem

One induction. A primitive case is lawful by the universe's law, and a case with one subterm
applies its combinator lemma to the induction hypothesis. A case with a list of subterms reads the
hypothesis off the mapped list. -/

-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- Soundness over an environment: every term whose obligations hold at `ρ`, and whose free
    variables `ρ` gives lawful codecs, satisfies retract, canon and writes. -/
theorem soundnessIn : ∀ {t : Term S} {T μ} (ρ : List S.C), Typed α β t T μ → Obligations α β t ρ →
    (∀ i, Lawful Syn.member (envAt ρ i)) → Lawful Syn.member (denote α β t ρ)
  | t, T, μ, ρ, h, hob, henv => by
    cases h with
    | prim g => exact Syn.lawful_ground g
    -- the bottom's domains are empty, so every law holds vacuously
    | never => exact Lawful.empty
    | opaq => exact Syn.lawful_top
    | var i => exact henv i
    -- each stage is lawful by the body's soundness at the stage before, and the guard carries
    -- the laws to the limit
    | @mu b T' μ' hg h' =>
      refine lawful_muCodec Syn.dV_pos Syn.dA_pos (contractive_body hg ρ) fun n => ?_
      induction n with
      | zero => exact Lawful.empty
      | succ n ih =>
        exact soundnessIn (_ :: ρ) h' (hob n ih) fun i => match i with
          | 0 => ih
          | i + 1 => henv i
    -- the lift of a lawful element is lawful, and the universe's set obligation is not read
    | @set L t' T' μ' hL h' =>
      simp only [denote, hL]
      exact L.lawful (soundnessIn ρ h' hob.1 henv)
    | @refine t' T' μ' p pA h' =>
      exact (soundnessIn ρ h' hob henv).refine2 _ _
    | @held t' I' μ' P PA k kA h' =>
      exact ((soundnessIn ρ h' hob.1 henv).adapt2 hob.2).refine2 _ _
    | @list L pre Tpre sp Tsp suf Tsuf hL hp hs hf =>
      have ihp : ∀ t' ∈ pre, Lawful Syn.member (denote α β t' ρ) := fun t' ht' => by
        obtain ⟨T', μ', hμ'⟩ := TypedList.forall (α := α) (β := β) hp t' ht'
        exact soundnessIn ρ hμ' (obligationsList_iff.mp hob.1 t' ht') henv
      have ihsp : ∀ t' ∈ sp, Lawful Syn.member (denote α β t' ρ) := fun t' ht' => by
        cases sp with
        | none => exact nomatch ht'
        | some tx =>
          replace ht' : some tx = some t' := ht'
          cases ht'
          cases hs with
          | some hμ' => exact soundnessIn ρ hμ' (obligationsOpt_iff.mp hob.2.1 t' rfl) henv
      have ihf : ∀ t' ∈ suf, Lawful Syn.member (denote α β t' ρ) := fun t' ht' => by
        obtain ⟨T', μ', hμ'⟩ := TypedList.forall (α := α) (β := β) hf t' ht'
        exact soundnessIn ρ hμ' (obligationsList_iff.mp hob.2.2 t' ht') henv
      simp only [denote, hL, denoteList_eq, denoteOpt_eq]
      exact lawful_listCodec L.hμ
          (List.forall_mem_map.mpr fun t' ht' => ihp t' ht')
          (forall_mem_map_option fun t' ht' => ihsp t' ht')
          (List.forall_mem_map.mpr fun t' ht' => ihf t' ht')
    | @object F body bind R μs hF hfields hrest =>
      -- the payload is taken apart once, here: the field lemmas below read a key set and a
      -- function on it, and `objectCodec` is stated over those
      cases body with | mk fields ff wild =>
      simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at hfields hrest
      -- a field's codec is its term's denotation, and its laws reach it unchanged
      have ihf : ∀ k, Lawful Syn.member (fieldSem α β (ff k) ρ).codec := by
        intro k
        have hobf := hob.1 k
        obtain ⟨t', hty', hshape⟩ := TypedField.term (α := α) (β := β) (hfields k)
        rcases hshape with heq | heq
        · rw [heq] at hobf ⊢
          exact soundnessIn ρ hty' hobf henv
        · rw [heq] at hobf ⊢; exact soundnessIn ρ hty' hobf henv
      have ihr : ∀ c, wildSem α β wild ρ = .codec c → Lawful Syn.member c := by
        intro c hcr
        cases hrest with
        | none => exact nomatch hcr
        | @some t' T' μ' hty =>
          replace hcr : RestSem.codec (denote α β t' ρ) = RestSem.codec c := hcr
          cases hcr
          exact soundnessIn ρ hty hob.2 henv
      simp only [denote, bodySem, hF]
      exact lawful_objectCodec F.hμ ihf ihr (wildSem_ne_drop _)
    | @union opts Ts μs hlist =>
      have ihs : ∀ t' ∈ opts, Lawful Syn.member (denote α β t' ρ) := fun t' ht' => by
        obtain ⟨T', μ', hμ'⟩ := TypedListμ.forall (α := α) (β := β) hlist t' ht'
        exact soundnessIn ρ hμ' (obligationsList_iff.mp hob.1 t' ht') henv
      have hC : ∀ o ∈ opts.map fun t' => denote α β t' ρ,
          ∀ o' ∈ opts.map fun t' => denote α β t' ρ, Compat o o' := by
        refine List.forall_mem_map.mpr fun s hs => List.forall_mem_map.mpr fun t' ht' => ?_
        exact hob.2 s hs t' ht'
      have hW : ∀ m, unanimous (opts.map fun t' => (denote α β t' ρ).μ) = some m →
          ∀ o ∈ opts.map fun t' => denote α β t' ρ,
            ∀ t' a, o.e t' = some a → Syn.member a = m := by
        intro m hm
        refine List.forall_mem_map.mpr fun tx htx t' a he' => ?_
        exact (ihs tx htx).writes
          (unanimous_spec hm _ (List.mem_map.mpr ⟨tx, htx, rfl⟩)) he'
      simp only [denote, denoteList_eq, denoteμs_eq_map]
      exact lawful_altCodec (List.forall_mem_map.mpr fun t' ht' => ihs t' ht') hC hW

termination_by t _ _ _ _ _ _ => Term.depth t
decreasing_by term_depth_wf

/-- Soundness: every closed term whose obligations hold satisfies retract, canon and writes. -/
theorem soundness {t : Term S} {T μ} (h : Typed α β t T μ) (hob : Obligations α β t) :
    Lawful Syn.member (denote α β t) :=
  soundnessIn [] h hob fun _ => Lawful.empty

/-! ## The denotation's held set is the judgement's

`Carrier` bounds `e` and `p` by the *codec's* `T`. `typed_TSub` bounds the codec's `T` by the
*judgement's*, which is what makes §3's `⊢ c : T ⇝ μ` a claim about the denotation rather than a
decoration. Each rule's held set is built by the same former the combinator's `T` field uses, so
most cases are pointwise. Three are not: `list` (positional through `align`), `object`
(name-dispatched) and the top, which is the universe's law. -/

/-- The uniform tail of a `(tuple-tail)`: every trailing position is the tail's. -/
theorem alignTail_TSub {c : S.C} {T' : S.V → Prop} (ih : ∀ v, c.T v → T' v) :
    ∀ {vs : List S.V} {ps}, align [] (some c) vs = some ps → (∀ p ∈ ps, p.1.T p.2) →
      ∀ x ∈ vs, T' x
  | [], _, _, _, x, hx => absurd hx (by simp)
  | v :: vs, ps, hal, hall, x, hx => by
      replace hal : ((align [] (some c) vs).map ((c, v) :: ·)) = some ps := hal
      cases hal' : align ([] : List S.C) (some c) vs with
      | none => rw [hal'] at hal; exact nomatch hal
      | some ps' =>
        rw [hal'] at hal
        replace hal : some ((c, v) :: ps') = some ps := hal
        cases hal
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ih x (hall (c, x) (List.mem_cons_self))
        · exact alignTail_TSub ih hal'
            (fun p hp => hall p (List.mem_cons_of_mem _ hp)) x hx'

/-- `align`'s positional pairing is §3's `T₁ × … × Tₙ`, one position at a time. -/
theorem align_TSub {tail : Option (Term S)} {Tt} (hopt : TypedOpt α β tail Tt)
    (ihTail : ∀ t' ∈ tail, ∀ (T' : S.V → Prop) (μ' : Option (Syn.M S)),
      Typed α β t' T' μ' → ∀ v, (denote α β t').T v → T' v) :
    ∀ {ts : List (Term S)} {Ts}, TypedList α β ts Ts →
      (∀ t' ∈ ts, ∀ (T' : S.V → Prop) (μ' : Option (Syn.M S)),
        Typed α β t' T' μ' → ∀ v, (denote α β t').T v → T' v) → ∀ {vs ps},
      align (ts.map (denote α β)) (tail.map (denote α β)) vs = some ps →
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
        replace hal : (((align _ (tail.map (denote α β)) vs')).map
          ((denote α β _, v) :: ·)) = some ps := hal
        cases hal' : align _ (tail.map (denote α β)) vs' with
        | none => rw [hal'] at hal; exact nomatch hal
        | some ps' =>
          rw [hal'] at hal
          replace hal : some ((denote α β _, v) :: ps') = some ps := hal
          cases hal
          refine ⟨ih _ (List.mem_cons_self) _ _ hty v (hall _ (List.mem_cons_self)), ?_⟩
          exact align_TSub hopt ihTail hs
            (fun t' ht' => ih t' (List.mem_cons_of_mem _ ht')) hal'
            (fun p hp => hall p (List.mem_cons_of_mem _ hp))

/-- The suffix's positions, read off the zipped row. -/
theorem zipSuf_TSub :
    ∀ {suf : List (Term S)} {Tsuf}, TypedList α β suf Tsuf →
      (∀ t' ∈ suf, ∀ (T' : S.V → Prop) (μ' : Option (Syn.M S)),
        Typed α β t' T' μ' → ∀ v, (denote α β t').T v → T' v) →
      ∀ {back : List S.V}, back.length = suf.length →
      (∀ p ∈ (suf.map (denote α β)).zip back, p.1.T p.2) →
      List.Forall₂ (fun T v => T v) Tsuf back
  | _, _, .nil, _, back, hlen, _ => by
      cases back with
      | nil => exact .nil
      | cons _ _ =>
          exact absurd hlen (by simp only [List.length_cons, List.length_nil]; omega)
  | _, _, @TypedList.cons _ _ _ _ t ts T Ts μ hty hs, ih, back, hlen, hall => by
      cases back with
      | nil => exact absurd hlen (by simp only [List.length_cons, List.length_nil]; omega)
      | cons b bs =>
        refine .cons (ih t (List.mem_cons_self) _ _ hty b (hall (denote α β t, b) ?_)) ?_
        · simp only [List.map_cons, List.zip_cons_cons]
          exact List.mem_cons_self
        · exact zipSuf_TSub hs (fun t' ht' => ih t' (List.mem_cons_of_mem _ ht'))
            (by simp only [List.length_cons] at hlen; omega)
            (fun p hp => hall p (by
              simp only [List.map_cons, List.zip_cons_cons]
              exact List.mem_cons_of_mem _ hp))

/-- `alignL`'s pairing is §3's `(list)` held set, read off the alignment. -/
theorem alignL_TSub {pre : List (Term S)} {Tpre sp Tsp suf Tsuf} (hp : TypedList α β pre Tpre)
    (hs : TypedOpt α β sp Tsp) (hf : TypedList α β suf Tsuf)
    (ihp : ∀ t' ∈ pre, ∀ (T' : S.V → Prop) (μ' : Option (Syn.M S)),
      Typed α β t' T' μ' → ∀ v, (denote α β t').T v → T' v)
    (ihs : ∀ t' ∈ sp, ∀ (T' : S.V → Prop) (μ' : Option (Syn.M S)),
      Typed α β t' T' μ' → ∀ v, (denote α β t').T v → T' v)
    (ihf : ∀ t' ∈ suf, ∀ (T' : S.V → Prop) (μ' : Option (Syn.M S)),
      Typed α β t' T' μ' → ∀ v, (denote α β t').T v → T' v)
    {vs ps}
    (hal : alignL (pre.map (denote α β)) (sp.map (denote α β)) (suf.map (denote α β)) vs = some ps)
    (hall : ∀ p ∈ ps, p.1.T p.2) : HTupleL Tpre Tsp Tsuf vs := by
  obtain ⟨front, back, psF, rfl, hblen, halF, rfl⟩ :=
    alignL_split _ _ _ _ _ hal
  refine ⟨front, back, rfl, ?_, ?_⟩
  · exact zipSuf_TSub hf ihf (by simpa using hblen)
      (fun p hp => hall p (List.mem_append_right _ hp))
  · exact align_TSub hs ihs hp ihp halF (fun p hp => hall p (List.mem_append_left _ hp))

-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- The denotation's held set is inside the judgement's. -/
theorem typed_TSub : ∀ {t : Term S} {T μ}, Typed α β t T μ → ∀ v, (denote α β t).T v → T v
  | t, T, μ, h, v, hv => by
    cases h with
    | prim _ => exact hv
    | never => exact hv
    | opaq => exact Syn.top_held v hv
    -- a closed variable is the bottom, and a `mu`'s index is its codec's held set
    | var _ => exact False.elim hv
    | mu _ _ => exact hv
    | @set L t' T' μ' hL h' =>
      simp only [denote, hL] at hv
      exact L.held_of (fun w hw => typed_TSub h' w hw) v hv
    | @list L pre Tpre sp Tsp suf Tsuf hL hp hs hf =>
      simp only [denote, hL, denoteList_eq, denoteOpt_eq] at hv
      obtain ⟨vs, rfl, ps, hal, hall⟩ := hv
      exact ⟨_, rfl, alignL_TSub hp hs hf
        (fun t' _ _ _ hty v hv => typed_TSub hty v hv)
        (fun t' _ _ _ hty v hv => typed_TSub hty v hv)
        (fun t' _ _ _ hty v hv => typed_TSub hty v hv) hal hall⟩
    | @held t' I' μ' P PA k kA h' =>
      exact ⟨typed_TSub h' ((α.word (halfK S.o.c k kA)).1 v) hv.1, hv.2⟩
    | @refine t' T' μ' q qA h' => exact ⟨typed_TSub h' v hv.1, hv.2⟩
    | @object F body bind R μs hF hfields hrest =>
      cases body with | mk fields ff wild =>
      simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at hfields hrest ⊢
      simp only [denote, bodySem, hF] at hv
      -- No case split on `v`: the object's `T` is `carriedCodec`'s, so it *hands over*
      -- the payload, a key set and a function on it, which is exactly `HObject`'s witness.
      obtain ⟨⟨keys, kvs⟩, hvp, hval, hall⟩ := hv
      refine ⟨keys, kvs, hvp, ?_, ?_⟩
      · -- every required binding's name is present, because its field is not `opt`
        intro k hreq
        have hty := hfields k
        have hno : ∀ c, fieldSem α β (ff k) ≠ FieldSem.opt c := by
          intro c hc
          obtain ⟨t', -, hshape⟩ := TypedField.term (α := α) (β := β) hty
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
            MapOf.at_of_mem (m := (⟨fields, fun k => fieldSem α β (ff k)⟩ :
              MapOf (FieldSem S.V (Syn.A S) (Syn.M S)))) ⟨k.1, hk⟩] at hentry
          obtain ⟨t', hty', hshape⟩ := TypedField.term (α := α) (β := β) (hfields ⟨k.1, hk⟩)
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
            replace hrc : some (denote α β t') = some rc := hrc
            cases hrc
            exact ⟨T'', rfl, typed_TSub hty' _ hrcT⟩
    | @union opts Ts μs hlist =>
      simp only [denote, denoteList_eq, denoteμs_eq_map] at hv
      obtain ⟨o, ho, hT⟩ := hv
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      obtain ⟨T', hT', μ', hty⟩ := TypedListμ.mem (α := α) (β := β) hlist tx htx
      exact ⟨T', hT', typed_TSub hty v hT⟩

termination_by t _ _ _ _ _ => Term.depth t
decreasing_by term_depth_wf

-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- Every derivable term denotes a pair **on its carrier**: §3's `e : T ⇀ 𝔸`, `p : 𝔸 ⇀ T`. One
    walk of the derivation, dispatching to the `Carrier` lemmas, with `soundness` supplying the
    lawfulness that the `held` and `mu` cases need. -/
theorem carrier_denote : ∀ {t : Term S} {T μ}, Typed α β t T μ → Obligations α β t → Carrier (denote α β t)
  | t, T, μ, h, hob => by
    cases h with
    | prim g => exact Syn.carrier_ground g
    | never => exact Carrier.empty
    | opaq => exact Syn.carrier_top
    -- a closed variable is the bottom, and a lawful `mu` is on its held set, its write domain
    | var _ => exact Carrier.empty
    | @mu b T' μ' hg h' => exact carrier_muCodec (soundness (.mu hg h') hob)
    | @set L t' T' μ' hL h' =>
      simp only [denote, hL]
      exact L.carrier (carrier_denote h' hob.1)
    | @list L pre Tpre sp Tsp suf Tsuf hL hp hs hf =>
      simp only [denote, hL, denoteList_eq, denoteOpt_eq]
      refine carrier_listCodec (List.forall_mem_map.mpr ?_) (forall_mem_map_option ?_)
        (List.forall_mem_map.mpr ?_)
      · intro t' ht'
        obtain ⟨T', μ', hty⟩ := TypedList.forall (α := α) (β := β) hp t' ht'
        exact carrier_denote hty (obligationsList_iff.mp hob.1 t' ht')
      · intro t' ht'
        cases sp with
        | none => exact nomatch ht'
        | some tx =>
          replace ht' : some tx = some t' := ht'
          cases ht'
          cases hs with
          | some hty => exact carrier_denote hty (obligationsOpt_iff.mp hob.2.1 t' rfl)
      · intro t' ht'
        obtain ⟨T', μ', hty⟩ := TypedList.forall (α := α) (β := β) hf t' ht'
        exact carrier_denote hty (obligationsList_iff.mp hob.2.2 t' ht')
    | @held t' I' μ' P PA k kA h' =>
      exact carrier_refine2 (carrier_adapt2 (carrier_denote h' hob.1)
        (soundness h' hob.1).core _ _ hob.2.1.2) _ _
    | @refine t' T' μ' p pA h' =>
      exact carrier_refine2 (carrier_denote h' hob) _ _
    | @object F body bind R μs hF hfields hrest =>
      cases body with | mk fields ff wild =>
      simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at hfields hrest
      have hsems : ∀ k : {k // k ∈ fields}, Carrier (fieldSem α β (ff k)).codec := by
        intro k
        have hobf := hob.1 k
        obtain ⟨t', hty', hshape⟩ := TypedField.term (α := α) (β := β) (hfields k)
        rcases hshape with heq | heq
        · rw [heq] at hobf ⊢
          exact carrier_denote hty' hobf
        · rw [heq] at hobf ⊢; exact carrier_denote hty' hobf
      have hrc : ∀ rc, rcOf (wildSem α β wild) = some rc → Carrier rc := by
        intro rc hcr
        cases hrest with
        | none => exact nomatch hcr
        | @some t' T' μ' hty =>
          replace hcr : some (denote α β t') = some rc := hcr
          cases hcr
          exact carrier_denote hty hob.2
      simp only [denote, bodySem, hF]
      exact carrier_objectCodec hsems hrc
    | @union opts Ts μs hlist =>
      simp only [denote, denoteList_eq]
      refine carrier_altCodec (List.forall_mem_map.mpr fun t' ht' => ?_)
      obtain ⟨T', μ', hty⟩ := TypedListμ.forall (α := α) (β := β) hlist t' ht'
      exact carrier_denote hty (obligationsList_iff.mp hob.1 t' ht')

termination_by t _ _ _ _ => Term.depth t
decreasing_by term_depth_wf

end Calculus.Alg
