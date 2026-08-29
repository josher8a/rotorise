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
    that option alone, on both sides. The theorem's residue; the disjointness
    dischargers are proved in `Calculus.Discharge` (`uAtCan_of_disjoint`). -/
def UAtCan (fuel : Nat) (opts : List Term) : Prop :=
  UniqueAdmission (semsOf fuel opts)

/-- The doc's semantic rule premises, at each fuel. Fuel 0 asks nothing — the
    denotation there is `Codec.empty`, whose laws are vacuous. -/
def Obligations : Nat → Term → Prop
  | 0, _ => True
  | fuel+1, t =>
    match t with
    | .string | .number | .decimal | .boolean | .binary | .null
    | .numeric _ | .literalS _ | .literalN _ | .opaq _ => True
    | .set t' | .array t' | .record t' | .refine t' _ => Obligations fuel t'
    | .tuple ts tail =>
      (∀ t' ∈ ts, Obligations fuel t') ∧ (∀ t' ∈ tail, Obligations fuel t')
    | .held t' f g =>
      Obligations fuel t' ∧
      -- the iso cancels on the carriers (§3 (held), T ≃ I): g ∘ f = id where f lands
      -- writable, f ∘ g = id on the writable values themselves
      (∀ v, ((denote fuel t').e (f v)).isSome → g (f v) = v) ∧
      (∀ v, ((denote fuel t').e v).isSome → f (g v) = v)
    | .legacy t' r =>
      Obligations fuel t' ∧
      -- ran(r) ⊆ dom(e): a migration lands on writable values
      (∀ a v, r a = some v → ((denote fuel t').e v).isSome) ∧
      -- coherence: the legacy reading agrees with the current one on the overlap
      (∀ a v, r a = some v → ∀ v', (denote fuel t').p a = some v' → v = v')
    | .nullable t' =>
      Obligations fuel t' ∧
      -- write-honesty: NULL is written for null alone
      (∀ v a, (denote fuel t').e v = some a → a = .null → v = .null) ∧
      -- read-honesty: null is read from NULL alone
      (∀ a v, (denote fuel t').p a = some v → v = .null → a = .null)
    | .lazy t' => Obligations fuel t'
    | .custom ce cp =>
      Lawful { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp }
    | .object fields rest =>
      (∀ kf ∈ fields,
        match kf.2 with
        | .req t' => Obligations fuel t'
        | .optional t' => Obligations fuel t'
        | .fallback t' v =>
          Obligations fuel t' ∧ ((denote fuel t').e v).isSome) ∧
      (match rest with | .codec t' => Obligations fuel t' | _ => True)
    | .union opts =>
      (∀ t' ∈ opts, Obligations fuel t') ∧ UAtCan fuel opts
    | .dunion _ opts => ∀ t' ∈ opts, Obligations fuel t'

/-- Legacy-free to depth `fuel`: where (MP) holds without exemption. -/
def MPOk : Nat → Term → Prop
  | 0, _ => True
  | fuel+1, t =>
    match t with
    | .legacy _ _ => False
    | .string | .number | .decimal | .boolean | .binary | .null
    | .numeric _ | .literalS _ | .literalN _ | .opaq _ | .custom _ _ => True
    | .set t' | .array t' | .record t' | .refine t' _ | .nullable t'
    | .held t' _ _ => MPOk fuel t'
    | .tuple ts tail =>
      (∀ t' ∈ ts, MPOk fuel t') ∧ (∀ t' ∈ tail, MPOk fuel t')
    | .lazy t' => MPOk fuel t'
    | .object fields rest =>
      (∀ kf ∈ fields,
        match kf.2 with
        | .req t' => MPOk fuel t'
        | .optional t' => MPOk fuel t'
        | .fallback t' _ => MPOk fuel t') ∧
      (match rest with | .codec t' => MPOk fuel t' | _ => True)
    | .union opts => ∀ t' ∈ opts, MPOk fuel t'
    | .dunion _ opts => ∀ t' ∈ opts, MPOk fuel t'

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

theorem lawful_numeric (q : Double → Bool) : ∀ fuel, Lawful (denote fuel (.numeric q))
  | 0 => lawful_dead
  | _+1 => by simp only [denote]; exact lawful_numericCodec q

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

theorem TypedFields.forall : ∀ {fs binds}, TypedFields fs binds →
    ∀ kf ∈ fs, ∃ T π μ, TypedField kf.2 T π μ
  | _, _, .nil, kf, h => absurd h (by simp)
  | _, _, .cons hf hs, kf, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨_, _, _, hf⟩
      · exact TypedFields.forall hs kf h'

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

theorem lookup_map {α β : Type} (g : α → β) :
    ∀ (l : List (Name × α)) (k),
      (l.map fun kv => (kv.1, g kv.2)).lookup k = (l.lookup k).map g
  | [], _ => rfl
  | (k₁, v₁) :: l, k => by
      simp only [List.map, List.lookup]
      cases hbe : (k == k₁) with
      | true => rfl
      | false => exact lookup_map g l k

/-- A lookup transports through a name-preserving traversal to the same name. -/
theorem traverse_lookup {α β : Type} {f : Name × α → Option (Name × β)}
    (hfst : ∀ kv kb, f kv = some kb → kb.1 = kv.1) :
    ∀ {kvs : List (Name × α)} {ds}, traverse f kvs = some ds →
      ∀ k v, kvs.lookup k = some v →
        ∃ b, ds.lookup k = some b ∧ f (k, v) = some (k, b)
  | [], _, _, _, _, hv => nomatch hv
  | (k₁, v₁) :: kvs, ds, ht, k, v, hv => by
      simp only [traverse] at ht
      cases hf₁ : f (k₁, v₁) with
      | none => rw [hf₁] at ht; exact nomatch ht
      | some kb =>
        obtain ⟨kbk, kbb⟩ := kb
        have hkb1 : kbk = k₁ := hfst _ _ hf₁
        subst hkb1
        rw [hf₁] at ht
        cases hts : traverse f kvs with
        | none => rw [hts] at ht; exact nomatch ht
        | some ds' =>
          rw [hts] at ht
          replace ht : some ((kbk, kbb) :: ds') = some ds := ht
          cases ht
          simp only [List.lookup] at hv
          cases hbe : (k == kbk) with
          | true =>
            rw [hbe] at hv
            replace hv : some v₁ = some v := hv
            cases hv
            have hkk : k = kbk := eq_of_beq hbe
            subst hkk
            refine ⟨kbb, ?_, hf₁⟩
            simp [List.lookup]
          | false =>
            rw [hbe] at hv
            replace hv : List.lookup k kvs = some v := hv
            obtain ⟨b, hb, hfb⟩ := traverse_lookup hfst hts k v hv
            refine ⟨b, ?_, hfb⟩
            simp only [List.lookup]
            rw [hbe]
            exact hb

/-! ## The member index is fuel-free -/

mutual

theorem denote_μ : ∀ (fuel : Nat) (t : Term), (denote fuel t).μ = μSyn t
  | 0, _ => rfl
  | fuel+1, t => by
    cases t with
    | string => rfl
    | number => rfl
    | decimal => rfl
    | boolean => rfl
    | binary => rfl
    | null => rfl
    | numeric q => rfl
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
  | _, _, _, .string => rfl
  | _, _, _, .number => rfl
  | _, _, _, .decimal => rfl
  | _, _, _, .boolean => rfl
  | _, _, _, .null => rfl
  | _, _, _, .binary => rfl
  | _, _, _, .numeric _ => rfl
  | _, _, _, .literalS _ _ _ => rfl
  | _, _, _, .literalN _ _ _ => rfl
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
  | _, _, _, .object _ _ _ => rfl
  | _, _, _, .union h => by
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
    ∃ fields rest ls, t = .object fields rest ∧
      fields.lookup d = some (.req (.literalS ls)) ∧ tagsOf d t = ls := by
  cases t
  case object fields rest =>
    cases hlk : fields.lookup d with
    | none => exact absurd (by simp only [tagsOf]; rw [hlk]) h
    | some fd =>
      cases fd with
      | optional _ => exact absurd (by simp only [tagsOf]; rw [hlk]) h
      | fallback _ _ => exact absurd (by simp only [tagsOf]; rw [hlk]) h
      | req tlit =>
        cases tlit
        case literalS ls => exact ⟨fields, rest, ls, rfl, hlk, by
          simp only [tagsOf]; rw [hlk]⟩
        all_goals exact absurd (by simp only [tagsOf]; rw [hlk]) h
  all_goals exact absurd rfl h

/-- Typing's nonempty-tags premise forces each `(dunion)` option to be an object whose
    discriminator is a `req literalS`, and object-encode then stamps the tag on both
    sides of every canonical pair — exactly the `hstamp` the sum lemmas consume.
    Shared by both halves of the theorem. -/
theorem dunion_stamp (fuel : Nat) {d : Name} {opts : List Term}
    (htags : ∀ t' ∈ opts, tagsOf d t' ≠ []) :
    ∀ o ∈ opts.map fun t' => (tagsOf d t', denote fuel t'), ∀ t' a, o.2.e t' = some a →
      ∃ tag ∈ o.1, (∃ kvs, a = .m kvs ∧ kvs.lookup d = some (.s tag)) ∧
        (∃ kvs, t' = .map kvs ∧ kvs.lookup d = some (.str tag)) := by
  refine forall_mem_map fun tx htx t' a he' => ?_
  replace he' : (denote fuel tx).e t' = some a := he'
  obtain ⟨fields, rest, ls, rfl, hlk, htagsls⟩ := tagsOf_ne_nil (htags tx htx)
  cases fuel with
  | zero => exact nomatch he'
  | succ f =>
    replace he' : (objectCodec
        (fields.map fun kf => (kf.1, fieldSemOf (denote f) kf.2))
        (restSemOf (denote f) rest)).e t' = some a := he'
    obtain ⟨kvs, ds, rfl, rfl, hval, htr⟩ := objectCodecCore_e_inv he'
    -- the discriminator is declared and non-`opt`, so the row carries it…
    have hslk : ((fields.map fun kf => (kf.1, fieldSemOf (denote f) kf.2)).lookup d) =
        some (FieldSem.req (denote f (Term.literalS ls))) := by
      rw [lookup_map (fieldSemOf (denote f)) fields d, hlk]
      rfl
    obtain ⟨vd, hvd⟩ := Option.isSome_iff_exists.mp (lookup_isSome_of_mem_fst
      (mem_of_contains (valPresentB_spec hval (mem_of_lookup hslk)
        (fun _ h' => nomatch h'))))
    -- …and `literal` writes it verbatim, which is the stamp on both sides
    obtain ⟨b, hbds, hbenc⟩ := traverse_lookup encEntry_fst htr d vd hvd
    simp only [encEntry] at hbenc
    rw [hslk] at hbenc
    replace hbenc : ((denote f (Term.literalS ls)).e vd).map ((d, ·)) = some (d, b) :=
      hbenc
    cases f with
    | zero =>
      replace hbenc : (Option.map ((d, ·)) (none : Option Attr)) = some (d, b) := hbenc
      exact nomatch hbenc
    | succ f' =>
      replace hbenc : ((literalSCodec ls).e vd).map ((d, ·)) = some (d, b) := hbenc
      cases vd
      case str tagv =>
        replace hbenc : ((if tagv ∈ ls then some (Attr.s tagv)
          else none)).map ((d, ·)) = some (d, b) := hbenc
        split at hbenc
        · replace hbenc : some (d, Attr.s tagv) = some (d, b) := hbenc
          cases hbenc
          rename_i hin
          exact ⟨tagv, htagsls ▸ hin, ⟨ds, rfl, hbds⟩, ⟨kvs, rfl, hvd⟩⟩
        · exact nomatch hbenc
      all_goals exact nomatch hbenc

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
theorem fieldSems_fb {fuel : Nat} {fields : List (Name × Field)}
    (hob : ∀ kf ∈ fields, match kf.2 with
      | .req t' => Obligations fuel t'
      | .optional t' => Obligations fuel t'
      | .fallback t' v => Obligations fuel t' ∧ ((denote fuel t').e v).isSome) :
    ∀ kf ∈ fields.map fun kf => (kf.1, fieldSemOf (denote fuel) kf.2),
      ∀ c v, kf.2 = .fb c v → (c.e v).isSome := by
  refine forall_mem_map ?_
  rintro ⟨k, f⟩ hmem c v hcv
  have hobf := hob (k, f) hmem
  cases f with
  | req t' => exact nomatch hcv
  | optional t' => exact nomatch hcv
  | fallback t' v₀ =>
    replace hobf : Obligations fuel t' ∧ ((denote fuel t').e v₀).isSome := hobf
    replace hcv : FieldSem.fb (denote fuel t') v₀ = FieldSem.fb c v := hcv
    cases hcv
    exact hobf.2

/-- Denoting the fields does not touch their names, so `(object)`'s distinctness
    premise transports too. -/
theorem fieldSems_nodup {fuel : Nat} {fields : List (Name × Field)}
    (hnd : (fields.map (·.1)).Nodup) :
    (((fields.map fun kf => (kf.1, fieldSemOf (denote fuel) kf.2)).map (·.1))).Nodup := by
  rw [List.map_map]; exact hnd

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
    | string => exact sound_ground lawful_stringCodec
    | number => exact sound_ground lawful_numberCodec
    | decimal => exact sound_ground lawful_decimalCodec
    | boolean => exact sound_ground lawful_booleanCodec
    | null => exact sound_ground lawful_nullCodec
    | binary => exact sound_ground lawful_binaryCodec
    | numeric q => exact sound_ground (lawful_numericCodec q)
    | literalS ls hne hnd => exact sound_ground (lawful_literalSCodec ls)
    | literalN ls hne hnd => exact sound_ground (lawful_literalNCodec ls)
    | opaq lossy => exact sound_ground (lawful_opaqCodecω lossy)
    | custom ce cp =>
      replace hob : Lawful { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp } :=
        hob
      exact sound_ground hob
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
      replace hob : Obligations fuel t' ∧
        (∀ v, ((denote fuel t').e (f v)).isSome → g (f v) = v) ∧
        (∀ v, ((denote fuel t').e v).isSome → f (g v) = v) := hob
      exact sound_wrap (t := t') (ih h' hob.1) (LawfulCore.through · hob.2.1 hob.2.2)
        (Lawful.through · hob.2.1 hob.2.2)
    | @nullable t' T' μ' h' =>
      replace hob : Obligations fuel t' ∧
        (∀ v a, (denote fuel t').e v = some a → a = .null → v = .null) ∧
        (∀ a v, (denote fuel t').p a = some v → v = .null → a = .null) := hob
      exact sound_wrap (t := t') (ih h' hob.1) (LawfulCore.orNull · hob.2.1 hob.2.2)
        (Lawful.orNull · hob.2.1 hob.2.2)
    | @legacy t' T' μ' r h' =>
      -- (MP) is off here by design: `MPOk` is `False` at a `legacy`, so the second
      -- half is vacuous and only the core laws survive. §5's first residue.
      replace hob : Obligations fuel t' ∧
        (∀ a v, r a = some v → ((denote fuel t').e v).isSome) ∧
        (∀ a v, r a = some v → ∀ v', (denote fuel t').p a = some v' → v = v') := hob
      exact ⟨LawfulCore.extendRead (ih h' hob.1).1 hob.2.1, fun hmp => hmp.elim⟩
    | @tuple ts Ts tail Tt hlist hopt =>
      replace hob : (∀ t' ∈ ts, Obligations fuel t') ∧
        (∀ t' ∈ tail, Obligations fuel t') := hob
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
    | @object fields binds rest R hfields hndf hrest =>
      -- a field's codec is its term's denotation, and (MP) reaches it unchanged
      have ihf : ∀ kf ∈ fields,
          LawfulCore (fieldSemOf (denote fuel) kf.2).codec ∧
          ((match kf.2 with
            | .req t' | .optional t' | .fallback t' _ => MPOk fuel t') →
            Lawful (fieldSemOf (denote fuel) kf.2).codec) := by
        rintro ⟨k, f⟩ hmem
        obtain ⟨T', π', μ', hμ'⟩ := TypedFields.forall hfields (k, f) hmem
        have hobf := hob.1 (k, f) hmem
        cases f with
        | req t' => cases hμ' with
          | req hty => exact ih hty hobf
        | optional t' => cases hμ' with
          | optional hty => exact ih hty hobf
        | fallback t' v => cases hμ' with
          | fallback hty =>
            replace hobf : Obligations fuel t' ∧ ((denote fuel t').e v).isSome := hobf
            exact ih hty hobf.1
      have hfb := fieldSems_fb hob.1
      have hnd' := fieldSems_nodup (fuel := fuel) hndf
      have ihr : ∀ c, restSemOf (denote fuel) rest = .codec c →
          LawfulCore c ∧ (MPOk (fuel+1) (.object fields rest) → Lawful c) := by
        intro c hcr
        cases hrest with
        | drop => exact nomatch hcr
        | refuse => exact nomatch hcr
        | @codec t' T' μ' hty =>
          replace hcr : RestSem.codec (denote fuel t') = RestSem.codec c := hcr
          cases hcr
          replace hob2 : Obligations fuel t' := hob.2
          exact ⟨(ih hty hob2).1, fun hmp => (ih hty hob2).2 hmp.2⟩
      exact ⟨lawfulCore_objectCodec
          (forall_mem_map fun kf hkf => (ihf kf hkf).1)
          hfb hnd' (fun c hcr => (ihr c hcr).1),
        fun hmp => lawful_objectCodec
          (forall_mem_map fun kf hkf => (ihf kf hkf).2 (hmp.1 kf hkf))
          hfb hnd' (fun c hcr => (ihr c hcr).2 hmp)⟩
    | @union opts Ts μs hlist =>
      replace hob : (∀ t' ∈ opts, Obligations fuel t') ∧ UAtCan fuel opts := hob
      have ihs : ∀ t' ∈ opts, Sound fuel t' := fun t' ht' => by
        obtain ⟨T', μ', hμ'⟩ := TypedListμ.forall hlist t' ht'
        exact ih hμ' (hob.1 t' ht')
      have hU : UniqueAdmission
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
      replace hob : ∀ t' ∈ opts, Obligations fuel t' := hob
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

/-- A field's binding is looked up where its semantics is. -/
theorem TypedFields.lookup_bind : ∀ {fields binds}, TypedFields fields binds →
    ∀ k, (fields.lookup k).isSome = (binds.lookup k).isSome ∧
      ∀ f, fields.lookup k = some f →
        ∃ T π μ, binds.lookup k = some (π, T) ∧ TypedField f T π μ
  | _, _, .nil, _ => ⟨rfl, fun _ h => nomatch h⟩
  | _, _, @TypedFields.cons k₁ f₁ fs binds T₁ π₁ μ₁ hf hs, k => by
      simp only [List.lookup]
      cases hbe : (k == k₁) with
      | true => exact ⟨rfl, fun f h => by cases h; exact ⟨T₁, π₁, μ₁, rfl, hf⟩⟩
      | false => exact TypedFields.lookup_bind hs k

/-- `opaque`'s fixpoint carries §3's `Uν` at every fuel. -/
theorem opaq_TSub : ∀ (fuel : Nat) (lossy : Bool) (v : Value),
    (opaqCodec fuel lossy).T v → HOpaque lossy v
  | 0, _, _, h => nomatch h
  | fuel+1, lossy, v, h => by
    obtain ⟨o, ho, hT⟩ := h
    have ih := opaq_TSub fuel lossy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨s, rfl⟩ := hT; exact .str s
    · obtain ⟨b, rfl⟩ := hT; exact .bool b
    · obtain ⟨b, rfl⟩ := hT; exact .bin b
    · cases hT; exact .null
    · cases hl : lossy with
      | false => rw [hl] at hT; exact nomatch hT
      | true =>
        rw [hl] at hT
        obtain ⟨d, rfl⟩ := hT
        exact .num d rfl
    · cases v <;> first
        | (obtain ⟨hne, hall⟩ := hT; exact .set _ hne fun x hx => ih x (hall x hx))
        | exact nomatch hT
    · cases v <;> first
        | exact .arr _ fun x hx => ih x (hT x hx)
        | exact nomatch hT
    · cases v <;> first
        | exact .map _ fun kv hkv => ih kv.2 (hT kv hkv)
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

/-- Every binding comes from a field, with its presence and held set. -/
theorem TypedFields.mem_bind : ∀ {fields binds}, TypedFields fields binds →
    ∀ nb ∈ binds, ∃ f, (nb.1, f) ∈ fields ∧ ∃ μ, TypedField f nb.2.2 nb.2.1 μ
  | _, _, .nil, nb, h => absurd h (by simp)
  | _, _, @TypedFields.cons k₁ f₁ fs binds T₁ π₁ μ₁ hf hs, nb, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨f₁, List.mem_cons_self _ _, μ₁, hf⟩
      · obtain ⟨f, hmem, μ, hty⟩ := TypedFields.mem_bind hs nb h'
        exact ⟨f, List.mem_cons_of_mem _ hmem, μ, hty⟩

/-- The denotation's held set is inside the judgement's, at every fuel. -/
theorem typed_TSub : ∀ (fuel : Nat) {t T μ}, Typed t T μ →
    ∀ v, (denote fuel t).T v → T v
  | 0, _, _, _, _, _, h => nomatch h
  | fuel+1, t, T, μ, h, v, hv => by
    cases h with
    | string | number | decimal | boolean | binary | numeric _ | null => exact hv
    | literalS _ _ _ | literalN _ _ _ => exact hv
    | custom _ _ => exact hv
    | opaq lossy => exact opaq_TSubω lossy v hv
    | @set t' T' μ₀ μS h' hs =>
      cases v <;> first
        | (obtain ⟨hne, hall⟩ := hv
           exact ⟨_, rfl, hne, fun x hx => typed_TSub fuel h' x (hall x hx)⟩)
        | exact nomatch hv
    | @array t' T' μ' h' =>
      cases v <;> first
        | exact ⟨_, rfl, fun x hx => typed_TSub fuel h' x (hv x hx)⟩
        | exact nomatch hv
    | @record t' T' μ' h' =>
      cases v <;> first
        | exact ⟨_, rfl, fun kv hkv => typed_TSub fuel h' kv.2 (hv kv hkv)⟩
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
    | @object fields binds rest R hfields hnd hrest =>
      cases v
      case map kvs =>
        obtain ⟨hval, hall⟩ := hv
        refine ⟨kvs, rfl, ?_, ?_⟩
        · -- every required binding's name is present, because its field is not `opt`
          intro nb hnb hreq
          obtain ⟨nk, nπ, nT⟩ := nb
          obtain ⟨f, hmem, μf, hty⟩ := TypedFields.mem_bind hfields (nk, nπ, nT) hnb
          have hsem : (nk, fieldSemOf (denote fuel) f) ∈
              fields.map fun kf => (kf.1, fieldSemOf (denote fuel) kf.2) :=
            List.mem_map.mpr ⟨(nk, f), hmem, rfl⟩
          have hno : ∀ c, fieldSemOf (denote fuel) f ≠ FieldSem.opt c := by
            intro c hc
            cases hty with
            | req _ => exact nomatch hc
            | fallback _ => exact nomatch hc
            | optional _ => exact nomatch hreq
          exact lookup_isSome_of_mem_fst
            (mem_of_contains (valPresentB_spec hval hsem hno))
        · -- and every present name holds what its binding, or the open part, says
          intro k x hlk
          have hentry := hall (k, x) (mem_of_lookup hlk)
          have hsl : (fields.map fun kf =>
              (kf.1, fieldSemOf (denote fuel) kf.2)).lookup k =
              (fields.lookup k).map (fieldSemOf (denote fuel)) :=
            lookup_map _ fields k
          cases hf : fields.lookup k with
          | some f =>
            obtain ⟨T', π', μ', hbl, htyf⟩ :=
              (TypedFields.lookup_bind hfields k).2 f hf
            rw [hbl]
            simp only [objEntryT, hsl, hf, Option.map] at hentry
            cases htyf with
            | req hty' => exact typed_TSub fuel hty' x hentry
            | optional hty' => exact typed_TSub fuel hty' x hentry
            | fallback hty' => exact typed_TSub fuel hty' x hentry
          | none =>
            have hbn : binds.lookup k = none := by
              have := (TypedFields.lookup_bind hfields k).1
              rw [hf] at this
              cases hb : binds.lookup k with
              | none => rfl
              | some b => rw [hb] at this; exact nomatch this
            rw [hbn]
            simp only [objEntryT, hsl, hf, Option.map] at hentry
            obtain ⟨rc, hrc, hrcT⟩ := hentry
            cases hrest with
            | drop => exact nomatch hrc
            | refuse => exact nomatch hrc
            | @codec t' T'' μ'' hty' =>
              replace hrc : some (denote fuel t') = some rc := hrc
              cases hrc
              exact ⟨T'', rfl, typed_TSub fuel hty' x hrcT⟩
      all_goals exact nomatch hv
    | @union opts Ts μs hlist =>
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
    | string => exact carrier_stringCodec
    | number => exact carrier_numberCodec
    | decimal => exact carrier_decimalCodec
    | boolean => exact carrier_booleanCodec
    | null => exact carrier_nullCodec
    | binary => exact carrier_binaryCodec
    | numeric q => exact carrier_numericCodec q
    | literalS ls _ _ => exact carrier_literalSCodec ls
    | literalN ls _ _ => exact carrier_literalNCodec ls
    | @set t' T' μ₀ μS h' hs =>
      replace hob : Obligations fuel t' := hob
      exact carrier_setCodec (carrier_denote fuel h' hob)
    | @array t' T' μ' h' =>
      replace hob : Obligations fuel t' := hob
      exact carrier_arrayCodec (carrier_denote fuel h' hob)
    | @record t' T' μ' h' =>
      replace hob : Obligations fuel t' := hob
      exact carrier_recordCodec (carrier_denote fuel h' hob)
    | @tuple ts Ts tail Tt hlist hopt =>
      replace hob : (∀ t' ∈ ts, Obligations fuel t') ∧
        (∀ t' ∈ tail, Obligations fuel t') := hob
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
      replace hob : Obligations fuel t' ∧
        (∀ v, ((denote fuel t').e (f v)).isSome → g (f v) = v) ∧
        (∀ v, ((denote fuel t').e v).isSome → f (g v) = v) := hob
      exact carrier_through (carrier_denote fuel h' hob.1)
        (soundness_both fuel h' hob.1).1 hob.2.2
    | @refine t' T' μ' q h' =>
      replace hob : Obligations fuel t' := hob
      exact carrier_restrict (carrier_denote fuel h' hob) q
    | @legacy t' T' μ' r h' =>
      replace hob : Obligations fuel t' ∧
        (∀ a v, r a = some v → ((denote fuel t').e v).isSome) ∧
        (∀ a v, r a = some v → ∀ v', (denote fuel t').p a = some v' → v = v') := hob
      exact carrier_extendRead (carrier_denote fuel h' hob.1) hob.2.1
    | @nullable t' T' μ' h' =>
      replace hob : Obligations fuel t' ∧
        (∀ v a, (denote fuel t').e v = some a → a = .null → v = .null) ∧
        (∀ a v, (denote fuel t').p a = some v → v = .null → a = .null) := hob
      exact carrier_orNull (carrier_denote fuel h' hob.1)
    | @lazy γ T' μ' h' =>
      replace hob : Obligations fuel γ := hob
      have ih := carrier_denote fuel h' hob
      exact ⟨fun he => ih.domE he, fun hp => ih.ranP hp⟩
    | custom ce cp =>
      replace hob : Lawful
        { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp } := hob
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
    | @object fields binds rest R hfields hndf hrest =>
      have hsems : ∀ kf ∈ fields.map fun kf => (kf.1, fieldSemOf (denote fuel) kf.2),
          Carrier kf.2.codec := by
        refine forall_mem_map ?_
        rintro ⟨k, f⟩ hmem
        obtain ⟨T', π', μ', hty⟩ := TypedFields.forall hfields (k, f) hmem
        have hobf := hob.1 (k, f) hmem
        cases f with
        | req t' =>
          cases hty with
          | req hty' =>
            replace hobf : Obligations fuel t' := hobf
            exact carrier_denote fuel hty' hobf
        | optional t' =>
          cases hty with
          | optional hty' =>
            replace hobf : Obligations fuel t' := hobf
            exact carrier_denote fuel hty' hobf
        | fallback t' v =>
          cases hty with
          | fallback hty' =>
            replace hobf : Obligations fuel t' ∧ ((denote fuel t').e v).isSome := hobf
            exact carrier_denote fuel hty' hobf.1
      have hfb := fieldSems_fb hob.1
      have hnd' := fieldSems_nodup (fuel := fuel) hndf
      have hrc : ∀ rc, rcOf (restSemOf (denote fuel) rest) = some rc → Carrier rc := by
        intro rc hcr
        cases hrest with
        | drop => exact nomatch hcr
        | refuse => exact nomatch hcr
        | @codec t' T' μ' hty =>
          replace hcr : some (denote fuel t') = some rc := hcr
          cases hcr
          replace hob2 : Obligations fuel t' := hob.2
          exact carrier_denote fuel hty hob2
      -- the name filter never discards a declared name, under any rest policy
      have hkeep : ∀ k, ((fields.map fun kf =>
          (kf.1, fieldSemOf (denote fuel) kf.2)).lookup k).isSome →
          keepB (restSemOf (denote fuel) rest)
            (fields.map fun kf => (kf.1, fieldSemOf (denote fuel) kf.2)) k = true := by
        intro k hk
        cases rest with
        | drop => exact hk
        | refuse => rfl
        | codec _ => rfl
      exact carrier_objectCodecCore hsems hrc hfb hnd' hkeep
    | @union opts Ts μs hlist =>
      replace hob : (∀ t' ∈ opts, Obligations fuel t') ∧ UAtCan fuel opts := hob
      refine carrier_altCodec (forall_mem_map fun t' ht' => ?_)
      obtain ⟨T', μ', hty⟩ := TypedListμ.forall hlist t' ht'
      exact (optionSemOf_c _ _) ▸ carrier_denote fuel hty (hob.1 t' ht')
    | @dunion d opts Ts hlistM htags hdisj =>
      replace hob : ∀ t' ∈ opts, Obligations fuel t' := hob
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
