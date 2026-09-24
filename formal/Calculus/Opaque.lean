import Calculus.Frontier
import Calculus.Recursion

/-!
# `opaque` is a recursive codec

`opaque` is `muCodec opaqStep`: the guarded recursion of `Recursion.lean` at the body `opaqStep`,
which is one layer of everything self-identifying over the layer below. Its regress is not on a
term: `opaqStep` rebuilds `opaque` under `set`/`array`/`record`, and each input budgets its own
depth.

Each container option reads the layer below at inputs one layer down, so the body is contractive
(`contractive_opaqStep`). Stability, the fixed point and the laws of the limit are then the general
theorems, and this file proves none of them a second time.

Its eight options are pairwise **kind-disjoint**, so at most one ever admits: the first
admitter is the only admitter. That makes each layer lawful (`compat_opaque`, then
`lawful_opaqStep`), and it lets each unfolding below reduce the union to one option. The guard
does not need kind-disjointness.

This file is §3's `(opaque)` rule, and nothing here is about a term other than `opaque`.

Structure:

* `opaqStep_e_*` / `opaqStep_p_*` — the unfoldings, one per container constructor of the
  domain each side ranges over. Each reduces `altCodec` to a single option by
  kind-disjointness, and is where the "at most one admits" argument is actually cashed. Five a
  side: the three wire sets (`strSet`/`numSet`/`binSet` against `ss`/`ns`/`bs`), the list and
  the map. A scalar needs no unfolding, because its row at the limit reduces by `rfl`. On the
  read side three members route to one option, which is a fact about `Kind` (`Domain.lean`).
* `contractive_opaqStep`, `lawful_opaq`, `carrier_opaq` — the guard, and the laws it carries to
  the limit.
* `Ωe_fix`, `Ωp_fix` and the container rows after them — `opaque` writes and reads each
  container through itself.
-/

namespace Calculus

/-! ## The unfoldings — §3 `(opaque)`, one per container constructor of each domain

Each says: at this value's kind, exactly one option admits, so the union's answer *is* that
option's. This is kind-disjointness cashed — the property `union` in general does not have
(`onKind_*` is what `opaque` has and `union` does not).

Stated against the option's own codec rather than its literal encoding, so they stay
true if a primitive's shape changes. Every one of them computes through the same ten
definitions, so those are a local `simp` set for the section. -/

section Unfoldings
attribute [local simp] opaqStep opaqOptions altCodec select stringCodec booleanCodec
  binaryCodec nullCodec numberCodec setCodec arrayCodec recordCodec

/-- §3 `(opaque)`, write side at kind `set`: the wire member is computed from the elements (`setCodec`), which is why one option covers `SS`, `NS` and `BS`. -/
theorem opaqStep_e_strSet (c : Codec) (S : NEFinset String) :
    (opaqStep c).e (.strSet S)
      = (setCodec c).e (.strSet S) := by
  cases he : (setCodec c).e (.strSet S) <;>
    simp [-setCodec, he]

/-- §3 `(opaque)`, write side at kind `set`, number elements. -/
theorem opaqStep_e_numSet (c : Codec) (S : NEFinset WFNumeral) :
    (opaqStep c).e (.numSet S)
      = (setCodec c).e (.numSet S) := by
  cases he : (setCodec c).e (.numSet S) <;>
    simp [-setCodec, he]

/-- §3 `(opaque)`, write side at kind `set`, byte-string elements. -/
theorem opaqStep_e_binSet (c : Codec) (S : NEFinset Bytes) :
    (opaqStep c).e (.binSet S)
      = (setCodec c).e (.binSet S) := by
  cases he : (setCodec c).e (.binSet S) <;>
    simp [-setCodec, he]

/-- §3 `(opaque)`, write side at kind `array`: the `L` option, recursing through `c`. -/
theorem opaqStep_e_arr (c : Codec) (vs : List Value) :
    (opaqStep c).e (.arr vs)
      = (arrayCodec c).e (.arr vs) := by
  cases he : (arrayCodec c).e (.arr vs) <;>
    simp [-arrayCodec, he]

/-- §3 `(opaque)`, write side at kind `map`: the `M` option, recursing through `c`. -/
theorem opaqStep_e_map (c : Codec) (keys : Finset Name)
    (f : {k // k ∈ keys} → Value) :
    (opaqStep c).e (.map keys f)
      = (recordCodec c).e (.map keys f) := by
  cases he : (recordCodec c).e (.map keys f) <;>
    simp [-recordCodec, he]

end Unfoldings

/-! ## The read side

The wire sets split into `SS`/`NS`/`BS`, all three handled by the `set` option.
Kind-disjointness is the same argument — each attribute constructor is accepted by at most one
of the eight. -/

section UnfoldingsA
attribute [local simp] opaqStep opaqOptions altCodec select stringCodec booleanCodec
  binaryCodec nullCodec numberCodec setCodec arrayCodec recordCodec

/-- §3 `(opaque)`, read side at member `SS` — one of the three members routing to the single `set` option. -/
theorem opaqStep_p_ss (c : Codec) (vs : NEFinset String) :
    (opaqStep c).p (.ss vs) = (setCodec c).p (.ss vs) := by
  cases hp : (setCodec c).p (.ss vs) <;>
    simp [-setCodec, hp]

/-- §3 `(opaque)`, read side at member `NS`. -/
theorem opaqStep_p_ns (c : Codec) (vs : NEFinset WFNumeral) :
    (opaqStep c).p (.ns vs) = (setCodec c).p (.ns vs) := by
  cases hp : (setCodec c).p (.ns vs) <;>
    simp [-setCodec, hp]

/-- §3 `(opaque)`, read side at member `BS`. -/
theorem opaqStep_p_bs (c : Codec) (vs : NEFinset Bytes) :
    (opaqStep c).p (.bs vs) = (setCodec c).p (.bs vs) := by
  cases hp : (setCodec c).p (.bs vs) <;>
    simp [-setCodec, hp]

/-- §3 `(opaque)`, read side at member `L`. -/
theorem opaqStep_p_l (c : Codec) (as : List Attr) :
    (opaqStep c).p (.l as) = (arrayCodec c).p (.l as) := by
  cases hp : (arrayCodec c).p (.l as) <;>
    simp [-arrayCodec, hp]

/-- §3 `(opaque)`, read side at member `M`. -/
theorem opaqStep_p_m (c : Codec) (keys : Finset Name)
    (g : {k // k ∈ keys} → Attr) :
    (opaqStep c).p (.m keys g)
      = (recordCodec c).p (.m keys g) := by
  cases hp : (recordCodec c).p (.m keys g) <;>
    simp [-recordCodec, hp]

end UnfoldingsA

/-! ## The limit -/

/-- **The guard, at `opaque`.** Each container option reads the layer below one layer down, and
    no scalar option reads it. -/
theorem contractive_opaqStep : Contractive opaqStep := fun _ _ _ h =>
  agreeLe_altCodec none none
    (.cons (.refl _ _) (.cons (.refl _ _) (.cons (.refl _ _) (.cons (.refl _ _) (.cons (.refl _ _)
      (.cons (agreeLe_setCodec h) (.cons (agreeLe_arrayCodec h)
        (.cons (agreeLe_recordCodec h) .nil))))))))

/-- `opaque`'s codec, under the short name that the inclusion lemmas use. -/
noncomputable abbrev Ω : Codec := muCodec opaqStep

/-- `opaque` is lawful: every layer is (`lawful_opaqStep`), and the guard carries the laws to the
    limit. -/
theorem lawful_opaq : Lawful Ω :=
  lawful_muCodec contractive_opaqStep (muStage_induct Lawful.empty fun _ => lawful_opaqStep)

/-- `opaque` is on its held set, which is its write domain. -/
theorem carrier_opaq : Carrier Ω := carrier_muCodec lawful_opaq

/-- **The fixed point, write side**: `opaque` writes what one layer over `opaque` writes. -/
theorem Ωe_fix (v : Value) : Ω.e v = (opaqStep Ω).e v := muCodec_e_fix contractive_opaqStep v

/-- **The fixed point, read side.** -/
theorem Ωp_fix (a : Attr) : Ω.p a = (opaqStep Ω).p a := muCodec_p_fix contractive_opaqStep a

/-- `Ω` writes an array element by element, through `Ω` itself. -/
theorem Ωe_arr (vs : List Value) : Ω.e (.arr vs) = (traverse Ω.e vs).map Attr.l := by
  rw [Ωe_fix, opaqStep_e_arr]; rfl

/-- `Ω` reads a list element by element, through `Ω` itself. -/
theorem Ωp_l (as : List Attr) : Ω.p (.l as) = (traverse Ω.p as).map Value.arr := by
  rw [Ωp_fix, opaqStep_p_l]; rfl

/-- `Ω` writes a map entry by entry, through `Ω` itself. -/
theorem Ωe_map (keys : Finset Name) (g : {k // k ∈ keys} → Value) :
    Ω.e (.map keys g) = (funImage fun k => Ω.e (g k)).map (Attr.m keys) := by
  rw [Ωe_fix, opaqStep_e_map]; rfl

/-- `Ω` reads a map entry by entry, through `Ω` itself. -/
theorem Ωp_m (keys : Finset Name) (g : {k // k ∈ keys} → Attr) :
    Ω.p (.m keys g) = (funImage fun k => Ω.p (g k)).map (Value.map keys) := by
  rw [Ωp_fix, opaqStep_p_m]; rfl

/-- `Ω` writes a string set through `encSet` over `Ω` itself. -/
theorem Ωe_strSet (S : NEFinset String) : Ω.e (.strSet S) = encSet Ω Value.str S := by
  rw [Ωe_fix, opaqStep_e_strSet]; rfl
/-- `Ω` writes a number set through `encSet` over `Ω` itself. -/
theorem Ωe_numSet (S : NEFinset WFNumeral) : Ω.e (.numSet S) = encSet Ω Value.num S := by
  rw [Ωe_fix, opaqStep_e_numSet]; rfl
/-- `Ω` writes a binary set through `encSet` over `Ω` itself. -/
theorem Ωe_binSet (S : NEFinset Bytes) : Ω.e (.binSet S) = encSet Ω Value.bin S := by
  rw [Ωe_fix, opaqStep_e_binSet]; rfl
/-- `Ω` reads `SS` through `decSet` over `Ω` itself. -/
theorem Ωp_ss (S : NEFinset String) : Ω.p (.ss S) = decSet Ω Attr.s S := by
  rw [Ωp_fix, opaqStep_p_ss]; rfl
/-- `Ω` reads `NS` through `decSet` over `Ω` itself. -/
theorem Ωp_ns (S : NEFinset WFNumeral) : Ω.p (.ns S) = decSet Ω Attr.n S := by
  rw [Ωp_fix, opaqStep_p_ns]; rfl
/-- `Ω` reads `BS` through `decSet` over `Ω` itself. -/
theorem Ωp_bs (S : NEFinset Bytes) : Ω.p (.bs S) = decSet Ω Attr.b S := by
  rw [Ωp_fix, opaqStep_p_bs]; rfl

end Calculus
