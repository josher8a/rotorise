import Calculus.Typing

/-!
# §5 — Soundness

The theorem, in the fueled form. `Obligations fuel t` collects the doc's *semantic* rule
premises at each fuel — `(legacy)`'s two side conditions, `(nullable)`'s null-honesty,
`(fallback)`'s writable stand-in, `(custom)`'s laws, `(union)`'s residual (U) at
canonical inputs. `MPOk` marks a derivation legacy-free to depth `fuel` — the doc's
(MP) exemption, as a predicate.

Statements:

* `soundness_core` — (R), (C), (W) for every derivable term.
* `soundness` — all four laws, legacy-free.

The ground-term cases are wrappers over the certified combinators (Combinators.lean),
where the per-construction lemmas — proved and open — now live.
-/

namespace Calculus

/-! ## Obligations -/

/-- The union options, denoted with their name specs — as in `denote`'s union case. -/
noncomputable def semsOf (fuel : Nat) (opts : List Term) : List OptionSem :=
  opts.map fun t' => optionSemOf (denote fuel t') (specOf t')

/-- §5 (U) at canonical inputs: every canonical attribute of an option is admitted by
    that option alone, on both sides. The strong form, and what the disjointness
    dischargers of `Calculus.Discharge` produce (`uAtCan_of_disjoint`). -/
def UAtCan (fuel : Nat) (opts : List Term) : Prop :=
  UniqueAdmission (semsOf fuel opts)

/-- **§5 (U) where the union acts** — the theorem's actual residue, and what `(union)`
    carries as an obligation.

    `UAtCan` quantifies over every canonical pair of every *option*; the laws only ever
    ask about inputs the *union* resolves, since `altCodec` declines everything else and
    a law quantified over `dom` cannot reach a declined input. `UAtAct` is that
    restriction (`UniqueBothWays`), and it is strictly weaker: the gap is where the
    working schemas sit — `union(array(literal "A"), array(literal "B"))` fails `UAtCan`
    at `[]` and meets `UAtAct`, because the union declines to write `[]`.

    Every discharger still discharges, through `uAtAct_of_uAtCan`. -/
def UAtAct (fuel : Nat) (opts : List Term) : Prop :=
  UniqueBothWays (semsOf fuel opts)

/-- The strong residue implies the one the laws need, so §5's dischargers are unaffected. -/
theorem uAtAct_of_uAtCan {fuel opts} (h : UAtCan fuel opts) : UAtAct fuel opts :=
  uniqueBothWays_of_uniqueAdmission h

/-- The doc's semantic rule premises, at each fuel. Fuel 0 asks nothing — the
    denotation there is `Codec.empty`, whose laws are vacuous. -/
def Obligations : Nat → Term → Prop
  | 0, _ => True
  | fuel+1, t =>
    match t with
    | .string | .number | .decimal | .boolean | .binary | .null
    | .literal _ | .literalS _ | .literalN _ | .opaq _ => True
    | .set t' | .array t' | .record t' | .refine t' _ => Obligations fuel t'
    | .tuple ts tail =>
      (∀ t' ∈ ts, Obligations fuel t') ∧ (∀ t' ∈ tail, Obligations fuel t')
    | .held t' f g => Obligations fuel t' ∧ IsoCancels (denote fuel t') f g
    | .legacy t' r => Obligations fuel t' ∧ ReadsCoherently (denote fuel t') r
    | .nullable t' => Obligations fuel t'
    | .lazy t' => Obligations fuel t'
    | .custom ce cp =>
      Lawful { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp }
    | .object _ f rest =>
      (∀ k,
        match f k with
        | .req t' => Obligations fuel t'
        | .optional t' => Obligations fuel t'
        | .fallback t' v =>
          Obligations fuel t' ∧ ((denote fuel t').e v).isSome) ∧
      (match rest with | .codec t' => Obligations fuel t' | _ => True)
    | .union opts =>
      (∀ t' ∈ opts, Obligations fuel t') ∧ UAtAct fuel opts
    | .dunion _ opts => ∀ t' ∈ opts, Obligations fuel t'

/-- Legacy-free to depth `fuel`: where (MP) holds without exemption. -/
def MPOk : Nat → Term → Prop
  | 0, _ => True
  | fuel+1, t =>
    match t with
    | .legacy _ _ => False
    | .literal _
    | .string | .number | .decimal | .boolean | .binary | .null
    | .literalS _ | .literalN _ | .opaq _ | .custom _ _ => True
    | .set t' | .array t' | .record t' | .refine t' _ | .nullable t'
    | .held t' _ _ => MPOk fuel t'
    | .tuple ts tail =>
      (∀ t' ∈ ts, MPOk fuel t') ∧ (∀ t' ∈ tail, MPOk fuel t')
    | .lazy t' => MPOk fuel t'
    | .object _ f rest =>
      (∀ k,
        match f k with
        | .req t' => MPOk fuel t'
        | .optional t' => MPOk fuel t'
        | .fallback t' _ => MPOk fuel t') ∧
      (match rest with | .codec t' => MPOk fuel t' | _ => True)
    | .union opts => ∀ t' ∈ opts, MPOk fuel t'
    | .dunion _ opts => ∀ t' ∈ opts, MPOk fuel t'

/-! ### The premises, per rule

`Obligations` is a recursion over the term, so at each rule it *is* the proposition that
rule's premises make — but only up to unfolding, and every case of the two inductions
below was re-stating that proposition to name it. These are that unfolding, once per
rule, and they read as the rule they belong to. Each is `:= h`. -/

namespace Obligations

theorem set {fuel t} (h : Obligations (fuel+1) (.set t)) : Obligations fuel t := h
theorem array {fuel t} (h : Obligations (fuel+1) (.array t)) : Obligations fuel t := h
theorem record {fuel t} (h : Obligations (fuel+1) (.record t)) : Obligations fuel t := h
theorem refine {fuel t q} (h : Obligations (fuel+1) (.refine t q)) : Obligations fuel t := h
theorem lazy {fuel t} (h : Obligations (fuel+1) (.lazy t)) : Obligations fuel t := h

theorem tuple {fuel ts tail} (h : Obligations (fuel+1) (.tuple ts tail)) :
    (∀ t ∈ ts, Obligations fuel t) ∧ (∀ t ∈ tail, Obligations fuel t) := h

/-- §3 `(held)`: the subterm's premises, and the iso cancelling on the carriers. -/
theorem held {fuel t f g} (h : Obligations (fuel+1) (.held t f g)) :
    Obligations fuel t ∧ IsoCancels (denote fuel t) f g := h

/-- §3 `(legacy)`: the subterm's premises, and the migration landing on writable values
    and agreeing with the current reading. -/
theorem legacy {fuel t r} (h : Obligations (fuel+1) (.legacy t r)) :
    Obligations fuel t ∧ ReadsCoherently (denote fuel t) r := h

/-- §3 `(nullable)`: the subterm's premises, and **nothing else**. Null-honesty was the
    other half of this until the wrapper's guard made it derivable
    (`nullHonest_of_not_ownsNull`) — one of the four premises §5's theorem levied, now
    paid by lawfulness instead. -/
theorem nullable {fuel t} (h : Obligations (fuel+1) (.nullable t)) :
    Obligations fuel t := h

/-- §3 `(custom)`: the escape hatch proves §2's laws for itself. -/
theorem custom {fuel ce cp} (h : Obligations (fuel+1) (.custom ce cp)) :
    Lawful { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp } := h

/-- §5 `(union)`: one premise per option, and (U) where the union acts. -/
theorem union {fuel opts} (h : Obligations (fuel+1) (.union opts)) :
    (∀ t ∈ opts, Obligations fuel t) ∧ UAtAct fuel opts := h

/-- §5 `(dunion)`: one premise per option; (U) is a theorem here, not a premise. -/
theorem dunion {fuel d opts} (h : Obligations (fuel+1) (.dunion d opts)) :
    ∀ t ∈ opts, Obligations fuel t := h

/-- The `fallback` field's own premise, `v(∗) ∈ dom(e)`. -/
theorem fallback {fuel t v}
    (h : match Field.fallback t v with
      | .req t => Obligations fuel t
      | .optional t => Obligations fuel t
      | .fallback t v => Obligations fuel t ∧ ((denote fuel t).e v).isSome) :
    Obligations fuel t ∧ ((denote fuel t).e v).isSome := h

end Obligations

/-! ## Ground-term lemmas -/

theorem lawful_string : ∀ fuel, Lawful (denote fuel .string)
  | 0 => lawful_dead
  | _+1 => by simp only [denote]; exact lawful_stringCodec

theorem lawful_boolean : ∀ fuel, Lawful (denote fuel .boolean)
  | 0 => lawful_dead
  | _+1 => by simp only [denote]; exact lawful_booleanCodec

theorem lawful_null : ∀ fuel, Lawful (denote fuel .null)
  | 0 => lawful_dead
  | _+1 => by simp only [denote]; exact lawful_nullCodec

theorem lawful_binary : ∀ fuel, Lawful (denote fuel .binary)
  | 0 => lawful_dead
  | _+1 => by simp only [denote]; exact lawful_binaryCodec

theorem lawful_decimal : ∀ fuel, Lawful (denote fuel .decimal)
  | 0 => lawful_dead
  | _+1 => by simp only [denote]; exact lawful_decimalCodec

theorem lawful_number : ∀ fuel, Lawful (denote fuel .number)
  | 0 => lawful_dead
  | _+1 => by simp only [denote]; exact lawful_numberCodec

theorem lawful_literalS (ls : List String) : ∀ fuel, Lawful (denote fuel (.literalS ls))
  | 0 => lawful_dead
  | _+1 => by simp only [denote]; exact lawful_literalSCodec ls

theorem lawful_literalN (ls : List Double) : ∀ fuel, Lawful (denote fuel (.literalN ls))
  | 0 => lawful_dead
  | _+1 => by simp only [denote]; exact lawful_literalNCodec ls

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

theorem optionSemOf_c (c : Codec) : ∀ s?, (optionSemOf c s?).c = c
  | some _ => rfl
  | none => rfl

/-! ## The member index is fuel-free -/

mutual

theorem denote_μ : ∀ (fuel : Nat) (t : Term), (denote fuel t).μ = μSyn t
  | 0, _ => rfl
  | fuel+1, t => by
    cases t with
    | literal v => exact literalCodec_μ v
    | string => rfl
    | number => rfl
    | decimal => rfl
    | boolean => rfl
    | binary => rfl
    | null => rfl
    | literalS ls => rfl
    | literalN ls => rfl
    | set t' =>
      show (denote fuel t').μ.bind setMember = (μSyn t').bind setMember
      rw [denote_μ fuel t']
    | array t' => rfl
    | tuple ts tail => rfl
    | record t' => rfl
    | held t' f g => exact denote_μ fuel t'
    | refine t' q => exact denote_μ fuel t'
    | legacy t' r => exact denote_μ fuel t'
    | nullable t' => rfl
    | lazy γ => rfl
    | custom ce cp => rfl
    | opaq lossy => rfl
    | object fields rest => rfl
    | union opts =>
      show unanimous (opts.map fun t' => (denote fuel t').μ) = unanimous (μSynList opts)
      rw [μSynList_eq fuel opts]
    | dunion d opts => rfl
termination_by fuel _ => (fuel, 0)

theorem μSynList_eq : ∀ (fuel : Nat) (opts : List Term),
    (opts.map fun t' => (denote fuel t').μ) = μSynList opts
  | _, [] => rfl
  | fuel, t :: ts => by
    simp only [List.map, μSynList]
    rw [denote_μ fuel t, μSynList_eq fuel ts]
termination_by fuel opts => (fuel, opts.length + 1)

end

mutual

/-- Typing's member index is the syntactic one — exactly, both sides. -/
theorem typed_μSyn : ∀ {t T μ}, Typed t T μ → μSyn t = μ
  | _, _, _, .literal _ _ _ hμ => hμ
  | _, _, _, .string => rfl
  | _, _, _, .number => rfl
  | _, _, _, .decimal => rfl
  | _, _, _, .boolean => rfl
  | _, _, _, .null => rfl
  | _, _, _, .binary => rfl
  | _, _, _, .literalS _ _ _ => rfl
  | _, _, _, .literalN _ _ _ _ => rfl
  | _, _, _, .set h' hs => by
      show (μSyn _).bind setMember = _
      rw [typed_μSyn h']
      exact hs
  | _, _, _, .array _ => rfl
  | _, _, _, .tuple _ _ => rfl
  | _, _, _, .record _ => rfl
  | _, _, _, .held h' _ => by have ih := typed_μSyn h'; exact ih
  | _, _, _, .refine h' => by have ih := typed_μSyn h'; exact ih
  | _, _, _, .legacy h' => by have ih := typed_μSyn h'; exact ih
  | _, _, _, .nullable _ => rfl
  | _, _, _, .lazy _ => rfl
  | _, _, _, .custom _ _ => rfl
  | _, _, _, .opaq _ => rfl
  | _, _, _, .object _ _ => rfl
  | _, _, _, .union h _ => by
      show unanimous (μSynList _) = unanimous _
      rw [typedListμ_μSyn h]
  | _, _, _, .dunion _ _ _ => rfl

theorem typedListμ_μSyn : ∀ {ts Ts μs}, TypedListμ ts Ts μs → μSynList ts = μs
  | _, _, _, .nil => rfl
  | _, _, _, .cons h hs => by
      show μSyn _ :: μSynList _ = _
      rw [typed_μSyn h, typedListμ_μSyn hs]

end

/-! ## The `(dunion)` stamp -/

/-- Typing's nonempty-tags premise **is** a shape constraint: `tagsOf` is empty for
    everything except an object whose `d` field is a `req literalS`, so a term with tags
    is one, and its tags are that literal's set. Stated once, it replaces the outer case
    analysis in `dunion_stamp` below. -/
theorem tagsOf_ne_nil {d : Name} {t : Term} (h : tagsOf d t ≠ []) :
    ∃ fields f rest ls, t = .object fields f rest ∧
      MapOf.at ⟨fields, f⟩ d = some (.req (.literalS ls)) ∧ tagsOf d t = ls := by
  cases t
  case object fields f rest =>
    cases hlk : MapOf.at (α := Field) ⟨fields, f⟩ d with
    | none => exact absurd (by simp only [tagsOf]; rw [hlk]; rfl) h
    | some fd =>
      cases fd with
      | optional _ => exact absurd (by simp only [tagsOf]; rw [hlk]; rfl) h
      | fallback _ _ => exact absurd (by simp only [tagsOf]; rw [hlk]; rfl) h
      | req tlit =>
        cases tlit
        case literalS ls => exact ⟨fields, f, rest, ls, rfl, hlk, by
          simp only [tagsOf]; rw [hlk]; rfl⟩
        all_goals exact absurd (by simp only [tagsOf]; rw [hlk]; rfl) h
  all_goals exact absurd rfl h

/-- Typing's nonempty-tags premise forces each `(dunion)` option to be an object whose
    discriminator is a `req literalS`, and object-encode then stamps the tag on both
    sides of every canonical pair — exactly the `hstamp` the sum lemmas consume.
    Shared by both halves of the theorem. -/
theorem dunion_stamp (fuel : Nat) {d : Name} {opts : List Term}
    (htags : ∀ t' ∈ opts, tagsOf d t' ≠ []) :
    ∀ o ∈ opts.map fun t' => (tagsOf d t', denote fuel t'), ∀ t' a, o.2.e t' = some a →
      ∃ tag ∈ o.1, tagOfA d a = some tag ∧ tagOfV d t' = some tag := by
  refine forall_mem_map fun tx htx t' a he' => ?_
  replace he' : (denote fuel tx).e t' = some a := he'
  obtain ⟨fields, ff, rest, ls, rfl, hlk, htagsls⟩ := tagsOf_ne_nil (htags tx htx)
  cases fuel with
  | zero => exact nomatch he'
  | succ f =>
    replace he' : (objectCodec ⟨fields, fun k => fieldSemOf (denote f) (ff k)⟩
        (restSemOf (denote f) rest)).e t' = some a := he'
    obtain ⟨keys, fv, g, rfl, rfl, hval, hfi⟩ := objectCodecCore_e_inv he'
    -- the discriminator is declared and non-`opt`, so the key set carries it. Denoting
    -- the table does not touch its key set, so the term's lookup *is* the semantics'.
    have hslk : MapOf.at (⟨fields, fun k => fieldSemOf (denote f) (ff k)⟩ : MapOf FieldSem) d
        = some (FieldSem.req (denote f (Term.literalS ls))) := by
      obtain ⟨hdf, hfd⟩ := MapOf.at_eq_some.mp hlk
      replace hfd : ff ⟨d, hdf⟩ = Field.req (Term.literalS ls) := hfd
      refine MapOf.at_eq_some.mpr ⟨hdf, ?_⟩
      show fieldSemOf (denote f) (ff ⟨d, hdf⟩) = _
      rw [hfd]; rfl
    have hd : d ∈ keys :=
      valPresentB_spec hval hslk (fun _ h' => nomatch h')
    -- …and `literal` writes it verbatim, which is the stamp on both sides. The key set
    -- is shared by the two payloads, so one membership proof serves both projections —
    -- where the list representation had to find `d` in each row separately.
    have hw := funImage_some hfi ⟨d, hd⟩
    rw [show entryCodec ⟨fields, fun k => fieldSemOf (denote f) (ff k)⟩
          (rcOf (restSemOf (denote f) rest)) d = some (denote f (Term.literalS ls)) by
        simp only [entryCodec, hslk]; rfl] at hw
    cases f with
    | zero => exact nomatch hw
    | succ f' =>
      replace hw : (literalSCodec ls).e (fv ⟨d, hd⟩) = some (g ⟨d, hd⟩) := hw
      cases hfv : fv ⟨d, hd⟩ <;> rw [hfv] at hw
      case str tagv =>
        replace hw : (if tagv ∈ ls then some (Attr.s tagv) else none)
            = some (g ⟨d, hd⟩) := hw
        split at hw
        · rename_i hin
          replace hw : Attr.s tagv = g ⟨d, hd⟩ := by simpa using hw
          exact ⟨tagv, htagsls ▸ hin,
            by simp only [tagOfA, dif_pos hd, ← hw],
            by simp only [tagOfV, dif_pos hd, hfv]⟩
        · exact nomatch hw
      all_goals exact nomatch hw

/-! ## The theorem

Both halves in one induction. `Sound` names what a case has to deliver, and three
helpers name the three shapes a case comes in: a ground pair, lawful outright; one
subterm, whose two combinator lemmas are applied to the two halves of the induction
hypothesis; and a list of subterms, where the hypothesis is read off the mapped list.
What is left in each case is the combinator lemmas it cites — which is the content. -/

/-- What one derivation has to deliver: the core laws unconditionally, and all four
    where it is legacy-free. -/
abbrev Sound (fuel : Nat) (t : Term) : Prop :=
  LawfulCore (denote fuel t) ∧ (MPOk fuel t → Lawful (denote fuel t))

/-- A ground case: the pair is lawful outright, so both halves are the same lemma. -/
theorem sound_ground {P : Prop} {c : Codec} (h : Lawful c) :
    LawfulCore c ∧ (P → Lawful c) :=
  ⟨h.core, fun _ => h⟩

/-- A one-subterm case: the subterm's core lemma and its full one, applied to the two
    halves of the induction hypothesis. (MP) passes through unchanged — every wrapper
    but `legacy` is transparent to it. -/
theorem sound_wrap {fuel : Nat} {t : Term} {c : Codec} (ih : Sound fuel t)
    (core : LawfulCore (denote fuel t) → LawfulCore c)
    (full : Lawful (denote fuel t) → Lawful c) :
    LawfulCore c ∧ (MPOk fuel t → Lawful c) :=
  ⟨core ih.1, fun hmp => full (ih.2 hmp)⟩

/-- `(fallback)`'s premise `v(∗) ∈ dom(e)`, transported to the denoted field list —
    which is the shape `object`'s two lemmas ask for. Both walks of the derivation
    need it, so it is stated here rather than twice inside them. -/
theorem fieldSems_fb {fuel : Nat} {fields : Finset Name}
    {f : {k // k ∈ fields} → Field}
    (hob : ∀ k, match f k with
      | .req t' => Obligations fuel t'
      | .optional t' => Obligations fuel t'
      | .fallback t' v => Obligations fuel t' ∧ ((denote fuel t').e v).isSome) :
    ∀ (k : {k // k ∈ fields}) c v,
      fieldSemOf (denote fuel) (f k) = .fb c v → (c.e v).isSome := by
  intro k c v hcv
  have hobf := hob k
  cases hfk : f k with
  | req t' => rw [hfk] at hcv; exact nomatch hcv
  | optional t' => rw [hfk] at hcv; exact nomatch hcv
  | fallback t' v₀ =>
    rw [hfk] at hcv hobf
    replace hobf := Obligations.fallback hobf
    replace hcv : FieldSem.fb (denote fuel t') v₀ = FieldSem.fb c v := hcv
    cases hcv
    exact hobf.2

/-- Both halves of §5's theorem in one induction: the core laws unconditionally, and
    all four where the derivation is legacy-free. One walk of the derivation, one
    unpacking of the obligations; each case dispatches to its two combinator lemmas.
    The public statements are the projections below. -/
theorem soundness_both : ∀ (fuel : Nat) {t T μ}, Typed t T μ → Obligations fuel t →
    Sound fuel t
  | 0, _, _, _, _, _ => ⟨lawful_dead.core, fun _ => lawful_dead⟩
  | fuel+1, t, T, μ, h, hob => by
    have ih : ∀ {t' : Term} {T' μ'}, Typed t' T' μ' → Obligations fuel t' → Sound fuel t' :=
      fun h' hob' => soundness_both fuel h' hob'
    cases h with
    | literal v μ hok hμ => exact sound_ground (lawful_literalCodec hok)
    | string => exact sound_ground lawful_stringCodec
    | number => exact sound_ground lawful_numberCodec
    | decimal => exact sound_ground lawful_decimalCodec
    | boolean => exact sound_ground lawful_booleanCodec
    | null => exact sound_ground lawful_nullCodec
    | binary => exact sound_ground lawful_binaryCodec
    | literalS ls hne hnd => exact sound_ground (lawful_literalSCodec ls)
    | literalN ls hne hnd hD => exact sound_ground (lawful_literalNCodec ls)
    | opaq lossy => exact sound_ground (lawful_opaqCodecω lossy)
    | custom ce cp =>
      exact sound_ground hob.custom
    | @set t' T' μ₀ μS h' hs =>
      have hμ : (denote fuel t').μ = some μ₀ := by rw [denote_μ]; exact typed_μSyn h'
      exact sound_wrap (t := t') (ih h' hob) (lawfulCore_setCodec · hμ hs) lawful_setCodec
    | @array t' T' μ' h' =>
      exact sound_wrap (t := t') (ih h' hob) lawfulCore_arrayCodec lawful_arrayCodec
    | @record t' T' μ' h' =>
      exact sound_wrap (t := t') (ih h' hob) lawfulCore_recordCodec lawful_recordCodec
    | @refine t' T' μ' q h' =>
      exact sound_wrap (t := t') (ih h' hob) (LawfulCore.restrict · q) (Lawful.restrict · q)
    | @lazy γ T' μ' h' =>
      exact sound_wrap (t := γ) (ih h' hob) LawfulCore.μNone Lawful.μNone
    | @held t' I' T' μ' f g h' hT =>
      exact sound_wrap (t := t') (ih h' hob.1) (LawfulCore.through · hob.2)
        (Lawful.through · hob.2)
    | @nullable t' T' μ' h' =>
      exact sound_wrap (t := t') (ih h' hob) lawfulCore_withNull lawful_withNull
    | @legacy t' T' μ' r h' =>
      -- (MP) is off here by design: `MPOk` is `False` at a `legacy`, so the second
      -- half is vacuous and only the core laws survive. §5's first residue.
      exact ⟨LawfulCore.extendRead (ih h' hob.1).1 hob.2.1, fun hmp => hmp.elim⟩
    | @tuple ts Ts tail Tt hlist hopt =>
      have ihs : ∀ t' ∈ ts, Sound fuel t' := fun t' ht' => by
        obtain ⟨T', μ', hμ'⟩ := TypedList.forall hlist t' ht'
        exact ih hμ' (hob.1 t' ht')
      have iht : ∀ t' ∈ tail, Sound fuel t' := fun t' ht' => by
        cases tail with
        | none => exact nomatch ht'
        | some tx =>
          replace ht' : some tx = some t' := ht'
          cases ht'
          cases hopt with
          | some hμ' => exact ih hμ' (hob.2 t' rfl)
      exact ⟨lawfulCore_tupleCodec (forall_mem_map fun t' ht' => (ihs t' ht').1)
          (forall_mem_map_option fun t' ht' => (iht t' ht').1),
        fun hmp => lawful_tupleCodec
          (forall_mem_map fun t' ht' => (ihs t' ht').2 (hmp.1 t' ht'))
          (forall_mem_map_option fun t' ht' => (iht t' ht').2 (hmp.2 t' ht'))⟩
    -- The field table is indexed by the declared names, so the induction hypothesis is
    -- read off at a key rather than at a membership, and `TypedFields.forall` — which
    -- existed to walk the row — is not needed. Nor is a `Nodup` to transport.
    | @object fields ff b rest R μs hfields hrest =>
      -- a field's codec is its term's denotation, and (MP) reaches it unchanged
      have ihf : ∀ k, LawfulCore (fieldSemOf (denote fuel) (ff k)).codec ∧
          ((match ff k with
            | .req t' | .optional t' | .fallback t' _ => MPOk fuel t') →
            Lawful (fieldSemOf (denote fuel) (ff k)).codec) := by
        intro k
        have hobf := hob.1 k
        obtain ⟨t', hty', hshape⟩ := TypedField.term (hfields k)
        rcases hshape with heq | heq | ⟨v, heq⟩ <;> rw [heq] at hobf ⊢
        · exact ih hty' hobf
        · exact ih hty' hobf
        · exact ih hty' (Obligations.fallback hobf).1
      have hfb := fieldSems_fb hob.1
      have ihr : ∀ c, restSemOf (denote fuel) rest = .codec c →
          LawfulCore c ∧ (MPOk (fuel+1) (.object fields ff rest) → Lawful c) := by
        intro c hcr
        cases hrest with
        | drop => exact nomatch hcr
        | refuse => exact nomatch hcr
        | @codec t' T' μ' hty =>
          replace hcr : RestSem.codec (denote fuel t') = RestSem.codec c := hcr
          cases hcr
          exact ⟨(ih hty hob.2).1, fun hmp => (ih hty hob.2).2 hmp.2⟩
      exact ⟨lawfulCore_objectCodec (fun k => (ihf k).1) hfb
          (fun c hcr => (ihr c hcr).1),
        fun hmp => lawful_objectCodec (fun k => (ihf k).2 (hmp.1 k)) hfb
          (fun c hcr => (ihr c hcr).2 hmp)⟩
    | @union opts Ts μs hlist _ =>
      have ihs : ∀ t' ∈ opts, Sound fuel t' := fun t' ht' => by
        obtain ⟨T', μ', hμ'⟩ := TypedListμ.forall hlist t' ht'
        exact ih hμ' (hob.1 t' ht')
      have hU : UniqueBothWays
          (opts.map fun t' => optionSemOf (denote fuel t') (specOf t')) := hob.2
      have hW : ∀ m, unanimous (opts.map fun t' => (denote fuel t').μ) = some m →
          ∀ o ∈ opts.map fun t' => optionSemOf (denote fuel t') (specOf t'),
            ∀ t' a, o.c.e t' = some a → a.member = m := by
        intro m hm
        refine forall_mem_map fun tx htx t' a he' => ?_
        rw [optionSemOf_c] at he'
        exact (ihs tx htx).1.writes
          (unanimous_spec hm _ (List.mem_map.mpr ⟨tx, htx, rfl⟩)) he'
      exact ⟨lawfulCore_altCodec
          (forall_mem_map fun t' ht' => (optionSemOf_c _ _) ▸ (ihs t' ht').1) hU hW,
        fun hmp => lawful_altCodec
          (forall_mem_map fun t' ht' => (optionSemOf_c _ _) ▸ (ihs t' ht').2 (hmp t' ht'))
          hU hW⟩
    | @dunion d opts Ts hlistM htags hdisj =>
      have ihs : ∀ t' ∈ opts, Sound fuel t' := fun t' ht' => by
        obtain ⟨T', hty⟩ := TypedListM.forall hlistM t' ht'
        exact ih hty (hob t' ht')
      have hstamp := dunion_stamp fuel htags
      have hdisj' : List.Pairwise (fun x y => ∀ tag ∈ x.1, tag ∉ y.1)
          (opts.map fun t' => (tagsOf d t', denote fuel t')) :=
        List.pairwise_map.mpr hdisj
      exact ⟨lawfulCore_dunionCodec
          (forall_mem_map fun t' ht' => (ihs t' ht').1) hstamp hdisj',
        fun hmp => lawful_dunionCodec
          (forall_mem_map fun t' ht' => (ihs t' ht').2 (hmp t' ht')) hstamp hdisj'⟩

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
        · exact ih x (hall (c, x) (List.mem_cons_self _ _))
        · exact alignTail_TSub ih hal'
            (fun p hp => hall p (List.mem_cons_of_mem _ hp)) x hx'

/-- `align`'s positional pairing is §3's `T₁ × … × Tₙ`, one position at a time. -/
theorem align_TSub {fuel : Nat}
    (ih : ∀ {t' : Term} {T' μ'}, Typed t' T' μ' → ∀ v, (denote fuel t').T v → T' v)
    {tail Tt} (hopt : TypedOpt tail Tt) :
    ∀ {ts Ts}, TypedList ts Ts → ∀ {vs ps},
      align (ts.map (denote fuel)) (tail.map (denote fuel)) vs = some ps →
      (∀ p ∈ ps, p.1.T p.2) → HTuple Ts Tt vs
  | _, _, .nil, vs, ps, hal, hall => by
      cases hopt with
      | none =>
        show HTuple [] none vs
        cases vs with
        | nil => rfl
        | cons _ _ => exact nomatch hal
      | @some t' T' μ' hty =>
        show HTuple [] (some T') vs
        exact alignTail_TSub (ih hty) hal hall
  | _, _, .cons hty hs, vs, ps, hal, hall => by
      cases vs with
      | nil => exact nomatch hal
      | cons v vs' =>
        replace hal : (((align _ (tail.map (denote fuel)) vs')).map
          ((denote fuel _, v) :: ·)) = some ps := hal
        cases hal' : align _ (tail.map (denote fuel)) vs' with
        | none => rw [hal'] at hal; exact nomatch hal
        | some ps' =>
          rw [hal'] at hal
          replace hal : some ((denote fuel _, v) :: ps') = some ps := hal
          cases hal
          refine ⟨ih hty v (hall _ (List.mem_cons_self _ _)), ?_⟩
          exact align_TSub ih hopt hs hal'
            (fun p hp => hall p (List.mem_cons_of_mem _ hp))

/-- `opaque`'s fixpoint carries §3's `Uν` at every fuel. -/
theorem opaq_TSub : ∀ (fuel : Nat) (lossy : Bool) (v : Value),
    (opaqCodec fuel lossy).T v → HOpaque lossy v
  | 0, _, _, h => nomatch h
  | fuel+1, lossy, v, h => by
    obtain ⟨o, ho, hT⟩ := h
    have ih := opaq_TSub fuel lossy
    simp only [opaqOptions, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨s, rfl⟩ := hT; exact .str s
    · obtain ⟨b, rfl⟩ := hT; exact .bool b
    · obtain ⟨b, rfl⟩ := hT; exact .bin b
    · cases hT; exact .null
    · cases hl : lossy with
      | false => rw [hl] at hT; exact nomatch hT
      | true =>
        rw [hl] at hT
        obtain ⟨d, rfl, hw⟩ := hT
        exact .num d rfl hw
    · cases v <;> first
        | (obtain ⟨hne, hall⟩ := hT
           exact .strSet _ hne fun s hs => ih (Value.str s) (hall s hs))
        | (obtain ⟨hne, hall⟩ := hT
           exact .numSet _ hne fun d hd => ih (Value.num d) (hall d hd))
        | (obtain ⟨hne, hall⟩ := hT
           exact .binSet _ hne fun b hb => ih (Value.bin b) (hall b hb))
        | exact nomatch hT
    · cases v <;> first
        | exact .arr _ fun x hx => ih x (hT x hx)
        | exact nomatch hT
    · cases v <;> first
        | exact .map _ _ fun k => ih _ (hT k)
        | exact nomatch hT

/-- `opaqCodecω`'s held set — the union over all fuels — still lands in §3's `Uν`. -/
theorem opaq_TSubω (lossy : Bool) (v : Value) :
    (opaqCodecω lossy).T v → HOpaque lossy v := by
  intro h
  obtain ⟨n, hn⟩ := h
  exact opaq_TSub n lossy v hn

/-- A union option's held set is one of the rule's. -/
theorem TypedListμ.mem : ∀ {ts Ts μs}, TypedListμ ts Ts μs →
    ∀ t ∈ ts, ∃ T ∈ Ts, ∃ μ, Typed t T μ
  | _, _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, List.mem_cons_self _ _, _, h⟩
      · obtain ⟨T', hT', μ', hty⟩ := TypedListμ.mem hs t ht'
        exact ⟨T', List.mem_cons_of_mem _ hT', μ', hty⟩

theorem TypedListM.mem : ∀ {ts Ts}, TypedListM ts Ts →
    ∀ t ∈ ts, ∃ T ∈ Ts, Typed t T (some .M)
  | _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, List.mem_cons_self _ _, h⟩
      · obtain ⟨T', hT', hty⟩ := TypedListM.mem hs t ht'
        exact ⟨T', List.mem_cons_of_mem _ hT', hty⟩

/-- The denotation's held set is inside the judgement's, at every fuel. -/
theorem typed_TSub : ∀ (fuel : Nat) {t T μ}, Typed t T μ →
    ∀ v, (denote fuel t).T v → T v
  | 0, _, _, _, _, _, h => nomatch h
  | fuel+1, t, T, μ, h, v, hv => by
    cases h with
    | string | number | decimal | boolean | binary | null => exact hv
    | literal w μ hok hμ =>
      cases w <;> cases v <;> simp_all [denote, literalCodec, Codec.restrict, stringCodec,
        rawNumberCodec, booleanCodec, binaryCodec, nullCodec, literalOK]
    | literalS _ _ _ | literalN _ _ _ _ => exact hv
    | custom _ _ => exact hv
    | opaq lossy => exact opaq_TSubω lossy v hv
    | @set t' T' μ₀ μS h' hs =>
      cases v <;> first
        | (obtain ⟨hne, hall⟩ := hv
           exact Or.inl ⟨_, rfl, hne, fun x hx => typed_TSub fuel h' _ (hall x hx)⟩)
        | (obtain ⟨hne, hall⟩ := hv
           exact Or.inr (Or.inl ⟨_, rfl, hne, fun x hx => typed_TSub fuel h' _ (hall x hx)⟩))
        | (obtain ⟨hne, hall⟩ := hv
           exact Or.inr (Or.inr ⟨_, rfl, hne, fun x hx => typed_TSub fuel h' _ (hall x hx)⟩))
        | exact nomatch hv
    | @array t' T' μ' h' =>
      cases v <;> first
        | exact ⟨_, rfl, fun x hx => typed_TSub fuel h' x (hv x hx)⟩
        | exact nomatch hv
    | @record t' T' μ' h' =>
      cases v <;> first
        | exact ⟨_, _, rfl, fun k => typed_TSub fuel h' _ (hv k)⟩
        | exact nomatch hv
    | @tuple ts Ts tail Tt hlist hopt =>
      cases v <;> first
        | (obtain ⟨ps, hal, hall⟩ := hv
           exact ⟨_, rfl, align_TSub (fun hty => typed_TSub fuel hty) hopt
             hlist hal hall⟩)
        | exact nomatch hv
    | @held t' I' T' μ' f g h' hT =>
      exact (hT v).mpr (typed_TSub fuel h' (f v) hv)
    | @refine t' T' μ' q h' => exact ⟨typed_TSub fuel h' v hv.1, hv.2⟩
    | @legacy t' T' μ' r h' => exact typed_TSub fuel h' v hv
    | @nullable t' T' μ' h' =>
      rcases hv with hv' | rfl
      · exact Or.inl (typed_TSub fuel h' v hv')
      · exact Or.inr rfl
    | @lazy γ T' μ' h' => exact typed_TSub fuel h' v hv
    | @object fields ff b rest R μs hfields hrest =>
      -- No case split on `v`: the object's `T` is `carriedCodec`'s, so it *hands over*
      -- the payload — a key set and a function on it, which is exactly `HObject`'s
      -- witness. The list representation had to take `v` apart to find one.
      obtain ⟨⟨keys, kvs⟩, hvp, hval, hall⟩ := hv
      refine ⟨keys, kvs, hvp, ?_, ?_⟩
      · -- every required binding's name is present, because its field is not `opt`
        intro k hreq
        have hty := hfields k
        have hno : ∀ c, fieldSemOf (denote fuel) (ff k) ≠ FieldSem.opt c := by
          intro c hc
          obtain ⟨t', -, hshape⟩ := TypedField.term hty
          rcases hshape with heq | heq | ⟨v, heq⟩
          · rw [heq] at hc; exact nomatch hc
          · exact TypedField.not_optional hty hreq t' heq
          · rw [heq] at hc; exact nomatch hc
        exact valPresentB_spec hval (MapOf.at_of_mem (m := ⟨fields, _⟩) k) hno
      · -- and every present name holds what its binding, or the open part, says
        intro k
        have hentry := hall k
        by_cases hk : k.1 ∈ fields
        · -- declared: the entry holds its field's set, and the binding is at the same key
          rw [dif_pos hk]
          simp only [objEntryT,
            MapOf.at_of_mem (m := (⟨fields, fun k => fieldSemOf (denote fuel) (ff k)⟩ :
              MapOf FieldSem)) ⟨k.1, hk⟩] at hentry
          obtain ⟨t', hty', hshape⟩ := TypedField.term (hfields ⟨k.1, hk⟩)
          rcases hshape with heq | heq | ⟨v₀, heq⟩ <;> rw [heq] at hentry <;>
            exact typed_TSub fuel hty' _ hentry
        · -- undeclared: it falls to the open part
          rw [dif_neg hk]
          simp only [objEntryT, MapOf.at, dif_neg hk] at hentry
          obtain ⟨rc, hrc, hrcT⟩ := hentry
          cases hrest with
          | drop => exact nomatch hrc
          | refuse => exact nomatch hrc
          | @codec t' T'' μ'' hty' =>
            replace hrc : some (denote fuel t') = some rc := hrc
            cases hrc
            exact ⟨T'', rfl, typed_TSub fuel hty' _ hrcT⟩
    | @union opts Ts μs hlist _ =>
      obtain ⟨o, ho, hT⟩ := hv
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      obtain ⟨T', hT', μ', hty⟩ := TypedListμ.mem hlist tx htx
      rw [optionSemOf_c] at hT
      exact ⟨T', hT', typed_TSub fuel hty v hT⟩
    | @dunion d opts Ts hlistM htags hdisj =>
      obtain ⟨o, ho, hT⟩ := hv
      simp only [List.mem_map] at ho
      obtain ⟨-, ⟨tx, htx, rfl⟩, rfl⟩ := ho
      obtain ⟨T', hT', hty⟩ := TypedListM.mem hlistM tx htx
      exact ⟨T', hT', typed_TSub fuel hty v hT⟩

/-- Every derivable term denotes a pair **on its carrier** — §3's `e : T ⇀ 𝔸`,
    `p : 𝔸 ⇀ T`. One walk of the derivation, dispatching to the `Carrier` lemmas, with
    `soundness_both` supplying the lawfulness the `held` and `custom` cases need. -/
theorem carrier_denote : ∀ (fuel : Nat) {t T μ}, Typed t T μ → Obligations fuel t →
    Carrier (denote fuel t)
  | 0, _, _, _, _, _ => carrier_dead
  | fuel+1, t, T, μ, h, hob => by
    cases h with
    | literal v μ hok hμ => exact carrier_literalCodec hok
    | string => exact carrier_stringCodec
    | number => exact carrier_numberCodec
    | decimal => exact carrier_decimalCodec
    | boolean => exact carrier_booleanCodec
    | null => exact carrier_nullCodec
    | binary => exact carrier_binaryCodec
    | literalS ls _ _ => exact carrier_literalSCodec ls
    | literalN ls _ _ => exact carrier_literalNCodec ls
    | @set t' T' μ₀ μS h' hs =>
      exact carrier_setCodec (carrier_denote fuel h' hob.set)
    | @array t' T' μ' h' =>
      exact carrier_arrayCodec (carrier_denote fuel h' hob.array)
    | @record t' T' μ' h' =>
      exact carrier_recordCodec (carrier_denote fuel h' hob.record)
    | @tuple ts Ts tail Tt hlist hopt =>
      refine carrier_tupleCodec (forall_mem_map ?_) (forall_mem_map_option ?_)
      · intro t' ht'
        obtain ⟨T', μ', hty⟩ := TypedList.forall hlist t' ht'
        exact carrier_denote fuel hty (hob.1 t' ht')
      · intro t' ht'
        cases tail with
        | none => exact nomatch ht'
        | some tx =>
          replace ht' : some tx = some t' := ht'
          cases ht'
          cases hopt with
          | some hty => exact carrier_denote fuel hty (hob.2 t' rfl)
    | @held t' I' T' μ' f g h' hT =>
      exact carrier_through (carrier_denote fuel h' hob.1)
        (soundness_both fuel h' hob.1).1 hob.2.2
    | @refine t' T' μ' q h' =>
      exact carrier_restrict (carrier_denote fuel h' hob.refine) q
    | @legacy t' T' μ' r h' =>
      exact carrier_extendRead (carrier_denote fuel h' hob.1) hob.2.1
    | @nullable t' T' μ' h' =>
      exact carrier_withNull (carrier_denote fuel h' hob)
    | @lazy γ T' μ' h' =>
      have ih := carrier_denote fuel h' hob.lazy
      exact ⟨fun he => ih.domE he, fun hp => ih.ranP hp⟩
    | custom ce cp =>
      refine ⟨?_, ?_⟩
      · intro v a he
        replace he : ce v = some a := he
        show (ce v).isSome = true
        rw [he]
        rfl
      · intro a v hp
        replace hp : cp a = some v := hp
        exact hob.canon hp
    | opaq lossy => exact carrier_opaqCodecω lossy
    | @object fields ff b rest R μs hfields hrest =>
      have hsems : ∀ k : {k // k ∈ fields},
          Carrier (fieldSemOf (denote fuel) (ff k)).codec := by
        intro k
        have hobf := hob.1 k
        obtain ⟨t', hty', hshape⟩ := TypedField.term (hfields k)
        rcases hshape with heq | heq | ⟨v, heq⟩ <;> rw [heq] at hobf ⊢
        · exact carrier_denote fuel hty' hobf
        · exact carrier_denote fuel hty' hobf
        · exact carrier_denote fuel hty' (Obligations.fallback hobf).1
      have hfb := fieldSems_fb hob.1
      have hrc : ∀ rc, rcOf (restSemOf (denote fuel) rest) = some rc → Carrier rc := by
        intro rc hcr
        cases hrest with
        | drop => exact nomatch hcr
        | refuse => exact nomatch hcr
        | @codec t' T' μ' hty =>
          replace hcr : some (denote fuel t') = some rc := hcr
          cases hcr
          exact carrier_denote fuel hty hob.2
      -- the name filter never discards a declared name, under any rest policy
      have hkeep : ∀ k, (MapOf.at (⟨fields, fun k => fieldSemOf (denote fuel) (ff k)⟩ :
          MapOf FieldSem) k).isSome →
          keepB (restSemOf (denote fuel) rest)
            ⟨fields, fun k => fieldSemOf (denote fuel) (ff k)⟩ k = true := by
        intro k hk
        cases rest with
        | drop => exact hk
        | refuse => rfl
        | codec _ => rfl
      exact carrier_objectCodecCore hsems hrc hfb hkeep
    | @union opts Ts μs hlist _ =>
      refine carrier_altCodec (forall_mem_map fun t' ht' => ?_)
      obtain ⟨T', μ', hty⟩ := TypedListμ.forall hlist t' ht'
      exact (optionSemOf_c _ _) ▸ carrier_denote fuel hty (hob.1 t' ht')
    | @dunion d opts Ts hlistM htags hdisj =>
      refine carrier_altCodec (forall_mem_map (forall_mem_map fun t' ht' => ?_))
      obtain ⟨T', hty⟩ := TypedListM.forall hlistM t' ht'
      exact carrier_denote fuel hty (hob t' ht')

/-- §3's `e : T ⇀ 𝔸`, at the judgement's own index: a derivable term writes only
    values of the held set it names. -/
theorem typed_e_mem (fuel : Nat) {t T μ} (h : Typed t T μ) (hob : Obligations fuel t)
    {v a} (he : (denote fuel t).e v = some a) : T v :=
  typed_TSub fuel h v ((carrier_denote fuel h hob).domE he)

/-- §3's `p : 𝔸 ⇀ T`, at the judgement's own index: a derivable term reads only into
    the held set it names. -/
theorem typed_p_mem (fuel : Nat) {t T μ} (h : Typed t T μ) (hob : Obligations fuel t)
    {a v} (hp : (denote fuel t).p a = some v) : T v :=
  typed_TSub fuel h v ((carrier_denote fuel h hob).ranP hp)

/-- §5 Theorem (soundness), core half: (R), (C), (W) for every derivable term — the
    `legacy` case included, which is exactly where this differs from `soundness`. -/
theorem soundness_core (fuel : Nat) {t T μ} (h : Typed t T μ)
    (hob : Obligations fuel t) : LawfulCore (denote fuel t) :=
  (soundness_both fuel h hob).1

/-- §5 Theorem (soundness), full: all four laws where the derivation is legacy-free —
    the doc's (MP) exemption, made a hypothesis. Each case dispatches to its
    combinator lemma; the grouping is the doc's proof, machine-checked. -/
theorem soundness (fuel : Nat) {t T μ} (h : Typed t T μ)
    (hob : Obligations fuel t) (hmp : MPOk fuel t) : Lawful (denote fuel t) :=
  (soundness_both fuel h hob).2 hmp

end Calculus
