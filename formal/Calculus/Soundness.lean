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
    that option alone, on both sides. The theorem's residue; (D), (K) and `ident` are
    its decidable dischargers (TODO lemmas, see README). -/
def UAtCan (fuel : Nat) (opts : List Term) : Prop :=
  UniqueAdmission (semsOf fuel opts)

/-- The doc's semantic rule premises, at each fuel. Fuel 0 asks nothing — the
    denotation there is `Codec.empty`, whose laws are vacuous. -/
def Obligations : Nat → Term → Prop
  | 0, _ => True
  | fuel+1, t =>
    match t with
    | .string | .number | .decimal | .boolean | .binary
    | .numeric _ | .literalS _ | .literalN _ | .opaq _ => True
    | .set t' | .array t' | .record t' | .refine t' _ => Obligations fuel t'
    | .tuple ts tail =>
      (∀ t' ∈ ts, Obligations fuel t') ∧ (∀ t' ∈ tail, Obligations fuel t')
    | .held t' _ _ => Obligations fuel t'
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
    | .lazy γ => Obligations fuel (γ ())
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
    | .string | .number | .decimal | .boolean | .binary
    | .numeric _ | .literalS _ | .literalN _ | .opaq _ | .custom _ _ => True
    | .set t' | .array t' | .record t' | .refine t' _ | .nullable t'
    | .held t' _ _ => MPOk fuel t'
    | .tuple ts tail =>
      (∀ t' ∈ ts, MPOk fuel t') ∧ (∀ t' ∈ tail, MPOk fuel t')
    | .lazy γ => MPOk fuel (γ ())
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

theorem TypedList.forall : ∀ {ts}, TypedList ts → ∀ t ∈ ts, ∃ μ, Typed t μ
  | _, .nil, t, ht => absurd ht (by simp)
  | _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, h⟩
      · exact TypedList.forall hs t ht'

theorem TypedListM.forall : ∀ {ts}, TypedListM ts → ∀ t ∈ ts, Typed t (some .M)
  | _, .nil, t, ht => absurd ht (by simp)
  | _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact h
      · exact TypedListM.forall hs t ht'

theorem TypedFields.forall : ∀ {fs}, TypedFields fs → ∀ kf ∈ fs, ∃ μ, TypedField kf.2 μ
  | _, .nil, kf, h => absurd h (by simp)
  | _, .cons hf hs, kf, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨_, hf⟩
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

/-- Typing's `some`-side member agrees with the syntactic member. -/
theorem typed_μSyn : ∀ {t μ'}, Typed t μ' → ∀ {μ}, μ' = some μ → μSyn t = some μ
  | _, _, .string, _, heq => by cases heq; rfl
  | _, _, .number, _, heq => by cases heq; rfl
  | _, _, .decimal, _, heq => by cases heq; rfl
  | _, _, .boolean, _, heq => by cases heq; rfl
  | _, _, .binary, _, heq => by cases heq; rfl
  | _, _, .numeric q, _, heq => by cases heq; rfl
  | _, _, .literalS ls hne hnd, _, heq => by cases heq; rfl
  | _, _, .literalN ls hne hnd, _, heq => by cases heq; rfl
  | _, _, .set h' hs, _, heq => by
      cases heq
      show (μSyn _).bind setMember = _
      rw [typed_μSyn h' rfl]
      exact hs
  | _, _, .array h', _, heq => by cases heq; rfl
  | _, _, .tuple hl ho, _, heq => by cases heq; rfl
  | _, _, .record h', _, heq => by cases heq; rfl
  | _, _, .held h' hgf hfg, _, heq => typed_μSyn h' heq
  | _, _, .refine h', _, heq => typed_μSyn h' heq
  | _, _, .legacy h', _, heq => typed_μSyn h' heq
  | _, _, .nullable h', _, heq => nomatch heq
  | _, _, .lazy h', _, heq => nomatch heq
  | _, _, .custom ce cp, _, heq => nomatch heq
  | _, _, .opaq lossy, _, heq => nomatch heq
  | _, _, .object hf hnd hr, _, heq => by cases heq; rfl
  | _, _, .union hl, _, heq => nomatch heq
  | _, _, .dunion hl htags hdisj, _, heq => by cases heq; rfl

/-! ## The theorem -/

/-- §5 Theorem (soundness), core half: (R), (C), (W) for every derivable term — the
    `legacy` case included, which is exactly where this differs from `soundness`. -/
theorem soundness_core : ∀ (fuel : Nat) {t μ}, Typed t μ →
    Obligations fuel t → LawfulCore (denote fuel t)
  | 0, _, _, _, _ => lawful_dead.core
  | fuel+1, t, μ, h, hob => by
    cases h with
    | string => simp only [denote]; exact lawful_stringCodec.core
    | number => simp only [denote]; exact lawful_numberCodec.core
    | decimal => simp only [denote]; exact lawful_decimalCodec.core
    | boolean => simp only [denote]; exact lawful_booleanCodec.core
    | binary => simp only [denote]; exact lawful_binaryCodec.core
    | numeric q => simp only [denote]; exact (lawful_numericCodec q).core
    | literalS ls hne hnd => simp only [denote]; exact (lawful_literalSCodec ls).core
    | literalN ls hne hnd => simp only [denote]; exact (lawful_literalNCodec ls).core
    | @set t' μ₀ μS h' hs =>
      simp only [denote]
      replace hob : Obligations fuel t' := hob
      refine lawfulCore_setCodec (soundness_core fuel h' hob) ?_ hs
      rw [denote_μ]
      exact typed_μSyn h' rfl
    | @array t' μ' h' =>
      simp only [denote]
      replace hob : Obligations fuel t' := hob
      exact lawfulCore_arrayCodec (soundness_core fuel h' hob)
    | @record t' μ' h' =>
      simp only [denote]
      replace hob : Obligations fuel t' := hob
      exact lawfulCore_recordCodec (soundness_core fuel h' hob)
    | @tuple ts tail hlist hopt =>
      simp only [denote]
      replace hob : (∀ t' ∈ ts, Obligations fuel t') ∧
        (∀ t' ∈ tail, Obligations fuel t') := hob
      refine lawfulCore_tupleCodec ?_ ?_
      · intro c hc
        simp only [List.mem_map] at hc
        obtain ⟨t', ht', rfl⟩ := hc
        obtain ⟨μ', hμ'⟩ := TypedList.forall hlist t' ht'
        exact soundness_core fuel hμ' (hob.1 t' ht')
      · intro c hc
        cases tail with
        | none => exact nomatch hc
        | some t' =>
          replace hc : some (denote fuel t') = some c := hc
          cases hc
          cases hopt with
          | some hμ' => exact soundness_core fuel hμ' (hob.2 t' rfl)
    | @held t' μ' f g h' hgf hfg =>
      simp only [denote]
      replace hob : Obligations fuel t' := hob
      exact LawfulCore.through (soundness_core fuel h' hob) hgf hfg
    | @refine t' μ' q h' =>
      simp only [denote]
      replace hob : Obligations fuel t' := hob
      exact LawfulCore.restrict (soundness_core fuel h' hob) q
    | @legacy t' μ' r h' =>
      simp only [denote]
      replace hob : Obligations fuel t' ∧
        (∀ a v, r a = some v → ((denote fuel t').e v).isSome) ∧
        (∀ a v, r a = some v → ∀ v', (denote fuel t').p a = some v' → v = v') := hob
      exact LawfulCore.extendRead (soundness_core fuel h' hob.1) hob.2.1
    | @nullable t' μ' h' =>
      simp only [denote]
      replace hob : Obligations fuel t' ∧
        (∀ v a, (denote fuel t').e v = some a → a = .null → v = .null) ∧
        (∀ a v, (denote fuel t').p a = some v → v = .null → a = .null) := hob
      exact LawfulCore.orNull (soundness_core fuel h' hob.1) hob.2.1 hob.2.2
    | @lazy γ μ' h' =>
      simp only [denote]
      replace hob : Obligations fuel (γ ()) := hob
      exact (soundness_core fuel h' hob).μNone
    | custom ce cp =>
      simp only [denote]
      replace hob : Lawful { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp } :=
        hob
      exact hob.core
    | opaq lossy =>
      simp only [denote]
      exact (lawful_opaqCodec (fuel+1) lossy).core
    | @object fields rest hfields hndf hrest =>
      simp only [denote]
      refine lawfulCore_objectCodec ?_ ?_ ?_ ?_
      · intro kf hkf
        simp only [List.mem_map] at hkf
        obtain ⟨⟨k, f⟩, hmem, rfl⟩ := hkf
        obtain ⟨μ', hμ'⟩ := TypedFields.forall hfields (k, f) hmem
        have hobf := hob.1 (k, f) hmem
        cases f with
        | req t' =>
          cases hμ' with
          | req hty =>
            replace hobf : Obligations fuel t' := hobf
            exact soundness_core fuel hty hobf
        | optional t' =>
          cases hμ' with
          | optional hty =>
            replace hobf : Obligations fuel t' := hobf
            exact soundness_core fuel hty hobf
        | fallback t' v =>
          cases hμ' with
          | fallback hty =>
            replace hobf : Obligations fuel t' ∧ ((denote fuel t').e v).isSome := hobf
            exact soundness_core fuel hty hobf.1
      · intro kf hkf c v hcv
        simp only [List.mem_map] at hkf
        obtain ⟨⟨k, f⟩, hmem, rfl⟩ := hkf
        have hobf := hob.1 (k, f) hmem
        cases f with
        | req t' => exact nomatch hcv
        | optional t' => exact nomatch hcv
        | fallback t' v₀ =>
          replace hobf : Obligations fuel t' ∧ ((denote fuel t').e v₀).isSome := hobf
          replace hcv : FieldSem.fb (denote fuel t') v₀ = FieldSem.fb c v := hcv
          cases hcv
          exact hobf.2
      · rw [List.map_map]
        exact hndf
      · intro c hcr
        cases hrest with
        | drop => exact nomatch hcr
        | refuse => exact nomatch hcr
        | @codec t' μ' hty =>
          replace hcr : RestSem.codec (denote fuel t') = RestSem.codec c := hcr
          cases hcr
          replace hob2 : Obligations fuel t' := hob.2
          exact soundness_core fuel hty hob2
    | @union opts hlist =>
      simp only [denote]
      replace hob : (∀ t' ∈ opts, Obligations fuel t') ∧ UAtCan fuel opts := hob
      have hlaw : ∀ t' ∈ opts, LawfulCore (denote fuel t') := fun t' ht' => by
        obtain ⟨μ', hμ'⟩ := TypedList.forall hlist t' ht'
        exact soundness_core fuel hμ' (hob.1 t' ht')
      refine lawfulCore_altCodec ?_ ?_ ?_
      · intro o ho
        simp only [List.mem_map] at ho
        obtain ⟨t', ht', rfl⟩ := ho
        show LawfulCore (optionSemOf (denote fuel t') (specOf t')).c
        rw [optionSemOf_c]
        exact hlaw t' ht'
      · have hU : UniqueAdmission
            (opts.map fun t' => optionSemOf (denote fuel t') (specOf t')) := hob.2
        exact hU
      · intro m hm o ho t' a he'
        simp only [List.mem_map] at ho
        obtain ⟨tx, htx, rfl⟩ := ho
        rw [optionSemOf_c] at he'
        have hmem : (denote fuel tx).μ ∈ opts.map (fun t'' => (denote fuel t'').μ) :=
          List.mem_map.mpr ⟨tx, htx, rfl⟩
        have hμx := unanimous_spec hm _ hmem
        exact (hlaw tx htx).writes hμx he'
    | @dunion d opts hlistM htags hdisj =>
      simp only [denote]
      replace hob : ∀ t' ∈ opts, Obligations fuel t' := hob
      have hlaw : ∀ t' ∈ opts, LawfulCore (denote fuel t') := fun t' ht' =>
        soundness_core fuel (TypedListM.forall hlistM t' ht') (hob t' ht')
      refine lawfulCore_dunionCodec ?_ ?_ ?_
      · intro o ho
        simp only [List.mem_map] at ho
        obtain ⟨tx, htx, rfl⟩ := ho
        exact hlaw tx htx
      · intro o ho t' a he'
        simp only [List.mem_map] at ho
        obtain ⟨tx, htx, rfl⟩ := ho
        replace he' : (denote fuel tx).e t' = some a := he'
        have htag := htags tx htx
        cases tx
        case object fields rest =>
          cases hlk : fields.lookup d with
          | none =>
            refine absurd ?_ htag
            simp only [tagsOf]
            rw [hlk]
          | some fd =>
            cases fd
            case optional tf =>
              refine absurd ?_ htag
              simp only [tagsOf]
              rw [hlk]
            case fallback tf vf =>
              refine absurd ?_ htag
              simp only [tagsOf]
              rw [hlk]
            case req tlit =>
              cases tlit
              case literalS ls =>
                have htagsls : tagsOf d (Term.object fields rest) = ls := by
                  simp only [tagsOf]
                  rw [hlk]
                cases fuel with
                | zero => exact nomatch he'
                | succ f =>
                  replace he' : (objectCodec
                      (fields.map fun kf => (kf.1, fieldSemOf (denote f) kf.2))
                      (restSemOf (denote f) rest)).e t' = some a := he'
                  obtain ⟨kvs, ds, rfl, rfl, hval, htr⟩ := objectCodecCore_e_inv he'
                  have hslk : ((fields.map fun kf =>
                      (kf.1, fieldSemOf (denote f) kf.2)).lookup d) =
                      some (FieldSem.req (denote f (Term.literalS ls))) := by
                    rw [lookup_map (fieldSemOf (denote f)) fields d, hlk]
                    rfl
                  have hcd : (kvs.map (·.1)).contains d = true :=
                    valPresentB_spec hval (mem_of_lookup hslk)
                      (fun _ h' => nomatch h')
                  obtain ⟨vd, hvd⟩ := Option.isSome_iff_exists.mp
                    (lookup_isSome_of_mem_fst (mem_of_contains hcd))
                  obtain ⟨b, hbds, hbenc⟩ := traverse_lookup encEntry_fst htr d vd hvd
                  simp only [encEntry] at hbenc
                  rw [hslk] at hbenc
                  replace hbenc : ((denote f (Term.literalS ls)).e vd).map
                    ((d, ·)) = some (d, b) := hbenc
                  cases f with
                  | zero =>
                    replace hbenc : (Option.map ((d, ·)) (none : Option Attr)) =
                      some (d, b) := hbenc
                    exact nomatch hbenc
                  | succ f' =>
                    replace hbenc : ((literalSCodec ls).e vd).map ((d, ·)) =
                      some (d, b) := hbenc
                    cases vd
                    case str tagv =>
                      replace hbenc : ((if tagv ∈ ls then some (Attr.s tagv)
                        else none)).map ((d, ·)) = some (d, b) := hbenc
                      split at hbenc
                      · replace hbenc : some (d, Attr.s tagv) = some (d, b) := hbenc
                        cases hbenc
                        rename_i hin
                        refine ⟨tagv, ?_, ⟨ds, rfl, hbds⟩, ⟨kvs, rfl, hvd⟩⟩
                        show tagv ∈ tagsOf d (Term.object fields rest)
                        rw [htagsls]
                        exact hin
                      · exact nomatch hbenc
                    all_goals exact nomatch hbenc
              all_goals
                refine absurd ?_ htag
                simp only [tagsOf]
                rw [hlk]
        all_goals exact absurd rfl htag
      · exact List.pairwise_map.mpr hdisj

/-- §5 Theorem (soundness), full: all four laws where the derivation is legacy-free —
    the doc's (MP) exemption, made a hypothesis. Each case dispatches to its
    combinator lemma; the grouping is the doc's proof, machine-checked. -/
theorem soundness : ∀ (fuel : Nat) {t μ}, Typed t μ →
    Obligations fuel t → MPOk fuel t → Lawful (denote fuel t)
  | 0, _, _, _, _, _ => lawful_dead
  | fuel+1, t, μ, h, hob, hmp => by
    cases h with
    | string => simp only [denote]; exact lawful_stringCodec
    | number => simp only [denote]; exact lawful_numberCodec
    | decimal => simp only [denote]; exact lawful_decimalCodec
    | boolean => simp only [denote]; exact lawful_booleanCodec
    | binary => simp only [denote]; exact lawful_binaryCodec
    | numeric q => simp only [denote]; exact lawful_numericCodec q
    | literalS ls hne hnd => simp only [denote]; exact lawful_literalSCodec ls
    | literalN ls hne hnd => simp only [denote]; exact lawful_literalNCodec ls
    | @set t' μ₀ μS h' hs =>
      simp only [denote]
      replace hob : Obligations fuel t' := hob
      replace hmp : MPOk fuel t' := hmp
      exact lawful_setCodec (soundness fuel h' hob hmp)
    | @array t' μ' h' =>
      simp only [denote]
      replace hob : Obligations fuel t' := hob
      replace hmp : MPOk fuel t' := hmp
      exact lawful_arrayCodec (soundness fuel h' hob hmp)
    | @record t' μ' h' =>
      simp only [denote]
      replace hob : Obligations fuel t' := hob
      replace hmp : MPOk fuel t' := hmp
      exact lawful_recordCodec (soundness fuel h' hob hmp)
    | @tuple ts tail hlist hopt =>
      simp only [denote]
      replace hob : (∀ t' ∈ ts, Obligations fuel t') ∧
        (∀ t' ∈ tail, Obligations fuel t') := hob
      replace hmp : (∀ t' ∈ ts, MPOk fuel t') ∧ (∀ t' ∈ tail, MPOk fuel t') := hmp
      refine lawful_tupleCodec ?_ ?_
      · intro c hc
        simp only [List.mem_map] at hc
        obtain ⟨t', ht', rfl⟩ := hc
        obtain ⟨μ', hμ'⟩ := TypedList.forall hlist t' ht'
        exact soundness fuel hμ' (hob.1 t' ht') (hmp.1 t' ht')
      · intro c hc
        cases tail with
        | none => exact nomatch hc
        | some t' =>
          replace hc : some (denote fuel t') = some c := hc
          cases hc
          cases hopt with
          | some hμ' => exact soundness fuel hμ' (hob.2 t' rfl) (hmp.2 t' rfl)
    | @held t' μ' f g h' hgf hfg =>
      simp only [denote]
      replace hob : Obligations fuel t' := hob
      replace hmp : MPOk fuel t' := hmp
      exact Lawful.through (soundness fuel h' hob hmp) hgf hfg
    | @refine t' μ' q h' =>
      simp only [denote]
      replace hob : Obligations fuel t' := hob
      replace hmp : MPOk fuel t' := hmp
      exact Lawful.restrict (soundness fuel h' hob hmp) q
    | @legacy t' μ' r h' =>
      replace hmp : False := hmp
      exact hmp.elim
    | @nullable t' μ' h' =>
      simp only [denote]
      replace hob : Obligations fuel t' ∧
        (∀ v a, (denote fuel t').e v = some a → a = .null → v = .null) ∧
        (∀ a v, (denote fuel t').p a = some v → v = .null → a = .null) := hob
      replace hmp : MPOk fuel t' := hmp
      exact Lawful.orNull (soundness fuel h' hob.1 hmp) hob.2.1 hob.2.2
    | @lazy γ μ' h' =>
      simp only [denote]
      replace hob : Obligations fuel (γ ()) := hob
      replace hmp : MPOk fuel (γ ()) := hmp
      exact (soundness fuel h' hob hmp).μNone
    | custom ce cp =>
      simp only [denote]
      replace hob : Lawful { T := fun v => (ce v).isSome, μ := none, e := ce, p := cp } :=
        hob
      exact hob
    | opaq lossy =>
      simp only [denote]
      exact lawful_opaqCodec (fuel+1) lossy
    | @object fields rest hfields hndf hrest =>
      simp only [denote]
      refine lawful_objectCodec ?_ ?_ ?_ ?_
      · intro kf hkf
        simp only [List.mem_map] at hkf
        obtain ⟨⟨k, f⟩, hmem, rfl⟩ := hkf
        obtain ⟨μ', hμ'⟩ := TypedFields.forall hfields (k, f) hmem
        have hobf := hob.1 (k, f) hmem
        have hmpf := hmp.1 (k, f) hmem
        cases f with
        | req t' =>
          cases hμ' with
          | req hty =>
            replace hobf : Obligations fuel t' := hobf
            replace hmpf : MPOk fuel t' := hmpf
            exact soundness fuel hty hobf hmpf
        | optional t' =>
          cases hμ' with
          | optional hty =>
            replace hobf : Obligations fuel t' := hobf
            replace hmpf : MPOk fuel t' := hmpf
            exact soundness fuel hty hobf hmpf
        | fallback t' v =>
          cases hμ' with
          | fallback hty =>
            replace hobf : Obligations fuel t' ∧ ((denote fuel t').e v).isSome := hobf
            replace hmpf : MPOk fuel t' := hmpf
            exact soundness fuel hty hobf.1 hmpf
      · intro kf hkf c v hcv
        simp only [List.mem_map] at hkf
        obtain ⟨⟨k, f⟩, hmem, rfl⟩ := hkf
        have hobf := hob.1 (k, f) hmem
        cases f with
        | req t' => exact nomatch hcv
        | optional t' => exact nomatch hcv
        | fallback t' v₀ =>
          replace hobf : Obligations fuel t' ∧ ((denote fuel t').e v₀).isSome := hobf
          replace hcv : FieldSem.fb (denote fuel t') v₀ = FieldSem.fb c v := hcv
          cases hcv
          exact hobf.2
      · rw [List.map_map]
        exact hndf
      · intro c hcr
        cases hrest with
        | drop => exact nomatch hcr
        | refuse => exact nomatch hcr
        | @codec t' μ' hty =>
          replace hcr : RestSem.codec (denote fuel t') = RestSem.codec c := hcr
          cases hcr
          replace hob2 : Obligations fuel t' := hob.2
          replace hmp2 : MPOk fuel t' := hmp.2
          exact soundness fuel hty hob2 hmp2
    | @union opts hlist =>
      simp only [denote]
      replace hob : (∀ t' ∈ opts, Obligations fuel t') ∧ UAtCan fuel opts := hob
      replace hmp : ∀ t' ∈ opts, MPOk fuel t' := hmp
      have hlaw : ∀ t' ∈ opts, Lawful (denote fuel t') := fun t' ht' => by
        obtain ⟨μ', hμ'⟩ := TypedList.forall hlist t' ht'
        exact soundness fuel hμ' (hob.1 t' ht') (hmp t' ht')
      refine lawful_altCodec ?_ ?_ ?_
      · intro o ho
        simp only [List.mem_map] at ho
        obtain ⟨t', ht', rfl⟩ := ho
        show Lawful (optionSemOf (denote fuel t') (specOf t')).c
        rw [optionSemOf_c]
        exact hlaw t' ht'
      · have hU : UniqueAdmission
            (opts.map fun t' => optionSemOf (denote fuel t') (specOf t')) := hob.2
        exact hU
      · intro m hm o ho t' a he'
        simp only [List.mem_map] at ho
        obtain ⟨tx, htx, rfl⟩ := ho
        rw [optionSemOf_c] at he'
        have hmem : (denote fuel tx).μ ∈ opts.map (fun t'' => (denote fuel t'').μ) :=
          List.mem_map.mpr ⟨tx, htx, rfl⟩
        have hμx := unanimous_spec hm _ hmem
        exact (hlaw tx htx).writes hμx he'
    | @dunion d opts hlistM htags hdisj =>
      simp only [denote]
      replace hob : ∀ t' ∈ opts, Obligations fuel t' := hob
      replace hmp : ∀ t' ∈ opts, MPOk fuel t' := hmp
      have hlaw : ∀ t' ∈ opts, Lawful (denote fuel t') := fun t' ht' =>
        soundness fuel (TypedListM.forall hlistM t' ht') (hob t' ht') (hmp t' ht')
      refine lawful_dunionCodec ?_ ?_ ?_
      · intro o ho
        simp only [List.mem_map] at ho
        obtain ⟨tx, htx, rfl⟩ := ho
        exact hlaw tx htx
      · intro o ho t' a he'
        simp only [List.mem_map] at ho
        obtain ⟨tx, htx, rfl⟩ := ho
        replace he' : (denote fuel tx).e t' = some a := he'
        have htag := htags tx htx
        cases tx
        case object fields rest =>
          cases hlk : fields.lookup d with
          | none =>
            refine absurd ?_ htag
            simp only [tagsOf]
            rw [hlk]
          | some fd =>
            cases fd
            case optional tf =>
              refine absurd ?_ htag
              simp only [tagsOf]
              rw [hlk]
            case fallback tf vf =>
              refine absurd ?_ htag
              simp only [tagsOf]
              rw [hlk]
            case req tlit =>
              cases tlit
              case literalS ls =>
                have htagsls : tagsOf d (Term.object fields rest) = ls := by
                  simp only [tagsOf]
                  rw [hlk]
                cases fuel with
                | zero => exact nomatch he'
                | succ f =>
                  replace he' : (objectCodec
                      (fields.map fun kf => (kf.1, fieldSemOf (denote f) kf.2))
                      (restSemOf (denote f) rest)).e t' = some a := he'
                  obtain ⟨kvs, ds, rfl, rfl, hval, htr⟩ := objectCodecCore_e_inv he'
                  have hslk : ((fields.map fun kf =>
                      (kf.1, fieldSemOf (denote f) kf.2)).lookup d) =
                      some (FieldSem.req (denote f (Term.literalS ls))) := by
                    rw [lookup_map (fieldSemOf (denote f)) fields d, hlk]
                    rfl
                  have hcd : (kvs.map (·.1)).contains d = true :=
                    valPresentB_spec hval (mem_of_lookup hslk)
                      (fun _ h' => nomatch h')
                  obtain ⟨vd, hvd⟩ := Option.isSome_iff_exists.mp
                    (lookup_isSome_of_mem_fst (mem_of_contains hcd))
                  obtain ⟨b, hbds, hbenc⟩ := traverse_lookup encEntry_fst htr d vd hvd
                  simp only [encEntry] at hbenc
                  rw [hslk] at hbenc
                  replace hbenc : ((denote f (Term.literalS ls)).e vd).map
                    ((d, ·)) = some (d, b) := hbenc
                  cases f with
                  | zero =>
                    replace hbenc : (Option.map ((d, ·)) (none : Option Attr)) =
                      some (d, b) := hbenc
                    exact nomatch hbenc
                  | succ f' =>
                    replace hbenc : ((literalSCodec ls).e vd).map ((d, ·)) =
                      some (d, b) := hbenc
                    cases vd
                    case str tagv =>
                      replace hbenc : ((if tagv ∈ ls then some (Attr.s tagv)
                        else none)).map ((d, ·)) = some (d, b) := hbenc
                      split at hbenc
                      · replace hbenc : some (d, Attr.s tagv) = some (d, b) := hbenc
                        cases hbenc
                        rename_i hin
                        refine ⟨tagv, ?_, ⟨ds, rfl, hbds⟩, ⟨kvs, rfl, hvd⟩⟩
                        show tagv ∈ tagsOf d (Term.object fields rest)
                        rw [htagsls]
                        exact hin
                      · exact nomatch hbenc
                    all_goals exact nomatch hbenc
              all_goals
                refine absurd ?_ htag
                simp only [tagsOf]
                rw [hlk]
        all_goals exact absurd rfl htag
      · exact List.pairwise_map.mpr hdisj

end Calculus
