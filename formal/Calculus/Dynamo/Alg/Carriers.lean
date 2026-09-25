import Calculus.Dynamo.Alg.Sums

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

/-- Every base is on its carrier — the six lemmas above, indexed. -/
theorem carrier_baseCodec : ∀ k : GroundKind, Carrier (baseCodec k)
  | .string  => carrier_stringCodec
  | .number  => carrier_numberCodec
  | .boolean => carrier_booleanCodec
  | .binary  => carrier_binaryCodec
  | .null    => carrier_nullCodec

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
