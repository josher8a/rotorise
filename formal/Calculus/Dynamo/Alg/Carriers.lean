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


/-- **Every base is on its carrier**: `e` only writes what the prism matched, and `p` only
    reads what it built (`carrier_pointCodec`). -/
theorem carrier_baseCodec (k : GroundKind) : Carrier (baseCodec k) := carrier_pointCodec

/-! ### The refinement ground codecs, on their carriers -/

/-- **One theorem where there were two, and the numeric one was twenty-six lines.**

    ~~literalNCodec~~'s carrier used to be proved by hand — unfolding the host's decimal reader, splitting on
    `Numeral.WF`, then on membership — because the codec was a hand-written pair that only
    *agreed* with a restriction. It now **is** the restriction, so `carrier_restrict` supplies
    everything and all that remains is the held set being the restriction's, which is
    `HLit_iff_restrict`. -/
theorem carrier_literalCodec (k : GroundKind) (x : k.Carrier) :
    Carrier (literalCodec k x) :=
  Carrier.congr (d := (baseCodec k).restrict (inL k x)) rfl rfl
    (fun v hv => (HLit_iff_restrict k x v).mpr hv)
    (carrier_restrict (carrier_baseCodec k) (inL k x))

/-- `set`: non-emptiness comes from the codec refusing an empty set on both sides, and
    membership in the held set from the element codec's own carrier. Uniqueness and order
    are no longer conditions at all — the `Finset` carries them. -/
theorem carrier_setCodec {c : Codec} (hc : Carrier c) : Carrier (setCodec c) where
  domE he := by
    obtain ⟨k, S, rfl, hE⟩ := setCodec_f_eq.mp he
    refine setCodec_T_wire.mpr fun x hx => ?_
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (setAt_elem hE x hx)
    exact hc.domE hb
  ranP hp := by
    obtain ⟨k, S, rfl, hD⟩ := setCodec_f_eq.mp hp
    obtain ⟨k', T, rfl, hm⟩ := setAt_mem hD
    refine setCodec_T_wire.mpr fun y hy => ?_
    obtain ⟨x, -, hx⟩ := hm y hy
    exact hc.ranP hx

end

end Calculus
