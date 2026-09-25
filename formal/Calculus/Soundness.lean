import Calculus.Typing
import Calculus.AlgSound

/-!
# §5 — Soundness

The theorem. `Obligations t` collects the semantic rule premises: `(held)` cancellation laws,
`(union)` pairwise compatibility, and the set obligation `SetElem`, at every stage of each
enclosing `mu`. The current term
language has no read adapter, so every typed term whose obligations hold satisfies retract, canon
and writes.

The induction runs over open terms. `soundnessIn` takes an environment of lawful codecs for the
variables, and a `mu` builds its stages from the body's soundness at the stage before.
`soundness` is the closed case.

The proofs are `Alg.soundnessIn`, `Alg.typed_TSub` and `Alg.carrier_denote`, for every universe.
Each theorem here states the generic one at the DynamoDB signature, through `denote_eq_alg`.
-/

namespace Calculus

open Alg (Body.fields_mk Body.wild_mk Body.at_mk Term.depth)

/-! ## Obligations -/


/-- **The union's obligation**: its options are pairwise compatible. -/
def PairwiseCompat (opts : List Term) (ρ : List Codec := []) : Prop :=
  ∀ s ∈ opts, ∀ t ∈ opts, Compat (denote s ρ) (denote t ρ)


/-- The doc's semantic rule premises, at DynamoDB: `Alg.Obligations` at the DynamoDB signature,
    whose set obligation is `SetElem`. -/
abbrev Obligations : Term → optParam (List Codec) [] → Prop := @Alg.Obligations dynSyn _

export Alg (ObligationsBody ObligationsField ObligationsWild ObligationsList ObligationsOpt)

/-! ### The companions, as the quantifiers the rest of the file speaks in

`ObligationsList` is what made the recursion structural; `∀ t ∈ ts, Obligations t` is what every
proof below wants. These are that bridge, and they are the entire cost of losing the fuel. -/

export Alg (obligationsList_iff obligationsOpt_iff)

/-! ### The premises, per rule

`Obligations` is a recursion over the term, so at each rule it *is* the proposition that
rule's premises make — but only up to unfolding, and every case of the two inductions
below was re-stating that proposition to name it. These are that unfolding, once per
rule, and they read as the rule they belong to. Each is `:= h`. -/

namespace Obligations

theorem array {t} (h : Obligations (.array t)) : Obligations t := h.2.1
theorem record {t} (h : Obligations (.record t)) : Obligations t := h.2
theorem refine {t q ρ} (h : Obligations (.refine t q) ρ) : Obligations t ρ := h

/-- §3 `(set)`: the element's premises, and the DynamoDB set rule. -/
theorem set {t ρ} (h : Obligations (.set t) ρ) : Obligations t ρ ∧ SetElem (denote t ρ) :=
  ⟨h.1, by rw [denote_eq_alg]; exact h.2⟩

theorem tuple {ts tail} (h : Obligations (.tuple ts tail)) :
    (∀ t ∈ ts, Obligations t) ∧ (∀ t ∈ tail, Obligations t) :=
  ⟨obligationsList_iff.mp h.1, obligationsOpt_iff.mp h.2.1⟩

/-- §3 `(list)`: one premise per declared position, the spread's, and the suffix's. -/
theorem list {pre sp suf ρ} (h : Obligations (.list pre sp suf) ρ) :
    (∀ t ∈ pre, Obligations t ρ) ∧ (∀ t ∈ sp, Obligations t ρ) ∧ (∀ t ∈ suf, Obligations t ρ) :=
  ⟨obligationsList_iff.mp h.1, obligationsOpt_iff.mp h.2.1, obligationsList_iff.mp h.2.2⟩

/-- §3 `(held)`: the subterm's premises, and the iso cancelling on the carriers. -/
theorem held {t P f g ρ} (h : Obligations (.held t P f g) ρ) :
    Obligations t ρ ∧ IsoCancels (denote t ρ) f g :=
  ⟨h.1, by rw [denote_eq_alg]; exact h.2⟩

/-- §5 `(union)`: one premise per option, and pairwise compatibility. -/
theorem union {opts ρ} (h : Obligations (.union opts) ρ) :
    (∀ t ∈ opts, Obligations t ρ) ∧ PairwiseCompat opts ρ :=
  ⟨obligationsList_iff.mp h.1, fun s hs t ht => by
    rw [denote_eq_alg, denote_eq_alg]; exact h.2 s hs t ht⟩

/-- A binder's premises: the body's, at each stage whose stage before is lawful. -/
theorem mu {b ρ} (h : Obligations (.mu b) ρ) : ∀ n, Lawful (muStage (fun c => denote b (c :: ρ)) n) →
    Obligations b (muStage (fun c => denote b (c :: ρ)) n :: ρ) := by
  rw [show (fun c => denote b (c :: ρ)) = fun c => Alg.denote b (c :: ρ) from
    funext fun c => denote_eq_alg b _]
  exact h

end Obligations

/-! ## Ground-term lemmas -/

/-- Each ground base is lawful: the term denotes the base codec. -/
theorem lawful_base (k : GroundKind) : Lawful (denote (.base k)) := lawful_baseCodec k

/-- One where there were two, at every base rather than the two commonest. -/
theorem lawful_literal (k : GroundKind) (x : k.Carrier) :
    Lawful (denote (.literal k x)) := by
  simp only [denote]; exact lawful_literalCodec k x

/-! ## Inversion and dispatch helpers -/

theorem TypedListM.forall : ∀ {ts Ts}, TypedListM ts Ts →
    ∀ t ∈ ts, ∃ T, Typed t T (some .M)
  | _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, h⟩
      · exact TypedListM.forall hs t ht'

/-- The DynamoDB member index is the generic one at `dynSem`. -/
theorem μSyn_eq_alg : ∀ t : Term, μSyn t = Alg.μSyn t
  | .base _ | .literal _ _ | .list _ _ _ | .opaq | .var _ | .mu _ | .object _ | .never => rfl
  | .set t => by
      show (μSyn t).bind setMember = (Alg.μSyn t).bind setMember
      rw [μSyn_eq_alg t]
  | .held t _ _ _ => μSyn_eq_alg t
  | .refine t _ => μSyn_eq_alg t
  | .union opts => by
      show unanimous (μSynList opts) = unanimous (Alg.μSynList opts)
      rw [μSynList_eq_alg opts]
where
  μSynList_eq_alg : ∀ ts : List Term, μSynList ts = Alg.μSynList ts
    | [] => rfl
    | t :: ts => by
        show μSyn t :: μSynList ts = Alg.μSyn t :: Alg.μSynList ts
        rw [μSyn_eq_alg t, μSynList_eq_alg ts]

/-- Typing's member index is the syntactic one — exactly, both sides. -/
theorem typed_μSyn {t T μ} (h : Typed t T μ) : μSyn t = μ :=
  (μSyn_eq_alg t).trans (Alg.typed_μSyn h)

/-! ## The theorem

`Alg.soundnessIn` at the DynamoDB signature. -/

/-- Soundness over an environment: every term whose obligations hold at `ρ`, and whose free
    variables `ρ` gives lawful codecs, satisfies retract, canon and writes. -/
theorem soundnessIn {t T μ} (ρ : List Codec) (h : Typed t T μ) (hob : Obligations t ρ)
    (henv : ∀ i, Lawful (envAt ρ i)) : Lawful (denote t ρ) := by
  rw [denote_eq_alg]; exact Alg.soundnessIn ρ h hob henv

/-- Soundness: every closed term whose obligations hold satisfies retract, canon and writes. -/
theorem soundness {t T μ} (h : Typed t T μ) (hob : Obligations t) : Lawful (denote t) :=
  soundnessIn [] h hob fun _ => Lawful.empty

/-! ## The denotation's held set is the judgement's

    `Carrier` bounds `e` and `p` by the *codec's* `T`. `typed_TSub` bounds the codec's
    `T` by the *judgement's*, which is what makes §3's `⊢ c : T ⇝ μ` a claim about the
    denotation rather than a decoration. The two compose into `typed_e_mem` and
    `typed_p_mem` below. `Alg.typed_TSub` is the proof. The converse helpers below serve `typed_T_eq`. -/

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
  | _, _, @TypedList.cons _ _ tx tsx Tx Tsx μx hty hs, ih, vs, hall => by
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

/-- …and the same suffix, built rather than read. -/
theorem zipSuf_T :
    ∀ {suf Tsuf}, TypedList suf Tsuf →
      (∀ t' ∈ suf, ∀ (T' : Held) (μ' : Option Member),
        Typed t' T' μ' → ∀ v, T' v → (denote t').T v) →
      ∀ {back : List Value}, List.Forall₂ (fun T v => T v) Tsuf back →
      back.length = suf.length ∧ ∀ p ∈ (suf.map denote).zip back, p.1.T p.2
  | _, _, .nil, _, back, hb => by
      cases hb; exact ⟨rfl, by simp⟩
  | _, _, @TypedList.cons _ _ t ts T Ts μ hty hs, ih, back, hb => by
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

/-- The denotation's held set is inside the judgement's. -/
theorem typed_TSub {t T μ} (h : Typed t T μ) (v : Value) (hv : (denote t).T v) : T v :=
  Alg.typed_TSub h v (by rw [← denote_eq_alg]; exact hv)

/-- Every derivable term denotes a pair **on its carrier** — §3's `e : T ⇀ 𝔸`,
    `p : 𝔸 ⇀ T`. -/
theorem carrier_denote {t T μ} (h : Typed t T μ) (hob : Obligations t) : Carrier (denote t) := by
  rw [denote_eq_alg]; exact Alg.carrier_denote h hob

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
  Alg.LawfulCore.extendRead (soundness ht hob).core hr.1

end Calculus
