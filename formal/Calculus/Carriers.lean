import Calculus.Sums

/-!
# Carriers — the pair is on `T`

§3 reads `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T`. One `Carrier` lemma per combinator, mirroring the
lawfulness lemmas, so the judgement's held-set index is the domain of the pair.
-/

namespace Calculus

noncomputable section
/-! ## Carriers — the pair is on `T` (§3 `e : T ⇀ 𝔸`, `p : 𝔸 ⇀ T`)

    One `Carrier` lemma per combinator, mirroring the lawfulness lemmas below. Together
    with `typed_TSub` (Soundness.lean) these make the judgement's held-set index a
    checked claim: what a derivable term writes and reads lies in the `T` it names. -/


/-- The carrier, likewise: `e` only writes what `V` matched, `p` only reads what `V`
    built. -/
theorem carrier_pointCodec {α : Type} {V : Ctor α Value} {A : Ctor α Attr} {μ₀ : Member} :
    Carrier (pointCodec V A μ₀) := by
  refine ⟨?_, ?_⟩
  · intro v a h
    obtain ⟨x, hx, _⟩ := Option.map_eq_some_iff.mp h
    exact ⟨x, V.into_out hx⟩
  · intro a v h
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨x, rfl⟩

/-- The four point ground codecs are on their carriers for one reason, the same one that
    made them lawful: `e` only writes what the value prism matched, and `p` only reads what
    it built. See `carrier_pointCodec`. -/
theorem carrier_stringCodec : Carrier stringCodec :=
  Carrier.congr (d := pointCodec strV sC .S)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl)
    (fun _ h => h) carrier_pointCodec

theorem carrier_booleanCodec : Carrier booleanCodec :=
  Carrier.congr (d := pointCodec boolV boolA .BOOL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl)
    (fun _ h => h) carrier_pointCodec

theorem carrier_binaryCodec : Carrier binaryCodec :=
  Carrier.congr (d := pointCodec binV bC .B)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl)
    (fun _ h => h) carrier_pointCodec

theorem carrier_nullCodec : Carrier nullCodec :=
  Carrier.congr (d := pointCodec nullV nullA .NULL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl)
    (fun _ h => h.elim fun _ hh => hh) carrier_pointCodec

/-- **Both halves are total at `N` now**, so neither direction has a gate to split on: the
    carrier is the held set. -/
theorem carrier_numberCodec : Carrier numberCodec := by
  refine ⟨?_, ?_⟩
  · intro v a h
    cases v with
    | num x => exact ⟨x, rfl⟩
    | _ => exact nomatch h
  · intro a v h
    cases a with
    | n x => rw [numberCodec_p_n] at h; cases h; exact ⟨x, rfl⟩
    | _ => exact nomatch h

/-! ### Sums -/

/-! ### How a union resolves

`altCodec`'s two halves are the same shape: the first option that acts answers. -/

/-- **What a selection produces**: the first option that acts answered. -/
theorem select_eq_some {A B : Type} {os : List Codec} {run : Codec → A → Option B} {x : A}
    {y : B} :
    select os run x = some y ↔
      ∃ o, os.find? (fun c => (run c x).isSome) = some o ∧ run o x = some y := by
  unfold select
  cases os.find? (fun c => (run c x).isSome) <;> simp

/-- …and it routes through an option that acts. -/
theorem select_admits {A B : Type} {os : List Codec} {run : Codec → A → Option B} {x : A}
    {y : B} (h : select os run x = some y) :
    ∃ o ∈ os, (run o x).isSome = true ∧ run o x = some y := by
  obtain ⟨o, hf, hr⟩ := select_eq_some.mp h
  exact ⟨o, List.mem_of_find?_eq_some hf, List.find?_some (p := fun c => (run c x).isSome) hf, hr⟩

/-- **What a union writes**: the first option that writes the value wrote. -/
theorem altCodec_e {os : List Codec} {μA : Option Member} {v a} :
    (altCodec os μA).e v = some a ↔
      ∃ o, os.find? (fun c => (c.e v).isSome) = some o ∧ o.e v = some a := select_eq_some

/-- **What a union reads**: the same theorem, on the attribute side. -/
theorem altCodec_p {os : List Codec} {μA : Option Member} {a v} :
    (altCodec os μA).p a = some v ↔
      ∃ o, os.find? (fun c => (c.p a).isSome) = some o ∧ o.p a = some v := select_eq_some

/-- A sum's encode routes through an option that writes. -/
theorem altCodec_e_admits {os : List Codec} {μA : Option Member} {v a}
    (he : (altCodec os μA).e v = some a) :
    ∃ o ∈ os, (o.e v).isSome = true ∧ o.e v = some a := select_admits he

/-- A sum's decode routes through an option that reads — the same theorem again. -/
theorem altCodec_p_admits {os : List Codec} {μA : Option Member} {a v}
    (hp : (altCodec os μA).p a = some v) :
    ∃ o ∈ os, (o.p a).isSome = true ∧ o.p a = some v := select_admits hp

/-! ### Wrappers -/

theorem carrier_through {c : Codec} {f g : Value → Value} (hc : Carrier c)
    (hlaw : LawfulCore c) (hfg : ∀ v, (c.e v).isSome → f (g v) = v) :
    Carrier (c.through f g) where
  domE he := hc.domE (through_e.mp he)
  ranP hp := by
    obtain ⟨w, hw, rfl⟩ := through_p.mp hp
    show c.T (f (g w))
    rw [hfg w (hlaw.canon hw)]
    exact hc.ranP hw

theorem carrier_restrict {c : Codec} (hc : Carrier c) (q : Value → Bool) :
    Carrier (c.restrict q) where
  domE he := let ⟨hq, hcv⟩ := restrict_e.mp he; ⟨hc.domE hcv, hq⟩
  ranP hp := let ⟨hcv, hq⟩ := restrict_p.mp hp; ⟨hc.ranP hcv, hq⟩


/-- Every base is on its carrier — the six lemmas above, indexed. -/
theorem carrier_baseCodec : ∀ k : GroundKind, Carrier (baseCodec k)
  | .string  => carrier_stringCodec
  | .number  => carrier_numberCodec
  | .boolean => carrier_booleanCodec
  | .binary  => carrier_binaryCodec
  | .null    => carrier_nullCodec

/-- …and each set base's element pair is on its carrier too. -/
theorem carrier_setBase : ∀ b : SetBase, Carrier b.elem
  | .string  => carrier_stringCodec
  | .number  => carrier_numberCodec
  | .binary  => carrier_binaryCodec

/-! ### The refinement ground codecs, on their carriers -/

/-- **One theorem where there were two, and the numeric one was twenty-six lines.**

    ~~literalNCodec~~'s carrier used to be proved by hand — unfolding the host's decimal reader, splitting on
    `Numeral.WF`, then on membership — because the codec was a hand-written pair that only
    *agreed* with a restriction. It now **is** the restriction, so `carrier_restrict` supplies
    everything and all that remains is the held set being no smaller than the restriction's,
    which is `hLit_of_inL`. -/
theorem carrier_literalCodec (k : GroundKind) (x : k.Carrier) :
    Carrier (literalCodec k x) :=
  Carrier.congr (d := (baseCodec k).restrict (inL k x)) rfl rfl
    (fun _ hv => hLit_of_inL k x _ hv.2)
    (carrier_restrict (carrier_baseCodec k) (inL k x))

/-- `alternate reader`: the migration lands in `T` because §3's `ran(r) ⊆ dom(e)` puts it in
    `dom(e)`, and `e`'s domain is `T`. The doc writes `r : 𝔸 ⇀ T` directly; this is the
    same premise arrived at through the one the proof already needs. -/
theorem carrier_extendRead {c : Codec} {r : Attr → Option Value} (hc : Carrier c)
    (hran : ∀ a v, r a = some v → (c.e v).isSome) :
    Carrier (c.extendRead r) where
  domE he := hc.domE (extendRead_e.mp he)
  ranP hp := by
    rcases extendRead_p.mp hp with hcv | ⟨-, hrv⟩
    · exact hc.ranP hcv
    · obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hran _ _ hrv)
      exact hc.domE ha'

/-- `set`: non-emptiness comes from the codec refusing an empty set on both sides, and
    membership in the held set from the element codec's own carrier. Uniqueness and order
    are no longer conditions at all — the `Finset` carries them. -/
theorem carrier_setCodec {c : Codec} (hc : Carrier c) : Carrier (setCodec c) where
  domE he := by
    rcases setCodec_e_eq.mp he with ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ <;>
      refine fun x hx => ?_ <;>
      · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (encSet_elem hE x hx)
        exact hc.domE hb
  ranP hp := by
    rcases setCodec_p_eq.mp hp with ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩ <;>
      · rcases decSet_mem hD with ⟨T, rfl, hm⟩ | ⟨T, rfl, hm⟩ | ⟨T, rfl, hm⟩ <;>
        · refine fun y hy => ?_
          obtain ⟨x, -, hx⟩ := hm y hy
          exact hc.ranP hx

/-! ### Sums -/

theorem carrier_altCodec {os : List Codec} {μA : Option Member}
    (h : ∀ o ∈ os, Carrier o) : Carrier (altCodec os μA) := by
  refine ⟨?_, ?_⟩
  · intro v a he
    obtain ⟨o, ho, -, hoe⟩ := altCodec_e_admits he
    exact ⟨o, ho, (h o ho).domE hoe⟩
  · intro a v hp
    obtain ⟨o, ho, -, hop⟩ := altCodec_p_admits hp
    exact ⟨o, ho, (h o ho).ranP hop⟩


/-- One layer of `opaque` is on its carrier when the layer below is — `HOpaque`, one option per
    kind. -/
theorem carrier_opaqStep {c : Codec} (ih : Carrier c) : Carrier (opaqStep c) := by
  refine carrier_altCodec ?_
  intro o ho
  simp only [opaqOptions, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact carrier_stringCodec
  · exact carrier_booleanCodec
  · exact carrier_binaryCodec
  · exact carrier_nullCodec
  · exact carrier_numberCodec
  · exact carrier_setCodec ih
  · exact carrier_arrayCodec ih
  · exact carrier_recordCodec ih

end

end Calculus
