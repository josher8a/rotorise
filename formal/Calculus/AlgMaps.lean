-- `Finset` and `Fintype`, for the key set of a map: a map writes where every entry writes, and
-- `Fintype` decides that quantifier. No other declaration of the algebra needs the two.
import Mathlib.Data.Fintype.Basic

/-!
# The image of a map, over any key type

A map codec moves the values of a map and keeps its keys. `funImage` is that move on the
partial side: the image is defined when every entry is defined. The keys are a `Finset` of any
type, so the statement reads no fact of a store.
-/

namespace Calculus.Alg

/-- **The map analogue of `setImage`, and much simpler.** A set codec can collide two
    elements onto one; a map cannot, because the names are fixed and the codec only moves
    the values. So all this has to do is demand that every value succeeds. -/
noncomputable def funImage {κ β : Type} {keys : Finset κ}
    (g : {k // k ∈ keys} → Option β) : Option ({k // k ∈ keys} → β) :=
  if h : ∀ k, (g k).isSome = true then some (fun k => (g k).get (h k)) else none

theorem funImage_some {κ β : Type} {keys : Finset κ} {g : {k // k ∈ keys} → Option β}
    {f : {k // k ∈ keys} → β} (h : funImage g = some f) : ∀ k, g k = some (f k) := by
  unfold funImage at h
  split at h
  · next hall =>
      intro k
      have := Option.some.inj h
      subst this
      exact (Option.some_get (hall k)).symm
  · exact nomatch h

theorem funImage_isSome {κ β : Type} {keys : Finset κ} {g : {k // k ∈ keys} → Option β}
    (hall : ∀ k, (g k).isSome = true) : (funImage g).isSome = true := by
  unfold funImage; rw [dif_pos hall]; rfl

/-- …and exactly when, which is what the exactness rows need: `funImage` is defined at a
    key set precisely where every entry is. -/
theorem funImage_isSome_iff {κ β : Type} {keys : Finset κ}
    {g : {k // k ∈ keys} → Option β} :
    (funImage g).isSome = true ↔ ∀ k, (g k).isSome = true := by
  refine ⟨fun h k => ?_, funImage_isSome⟩
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp h
  rw [funImage_some hf k]; rfl

theorem funImage_eq {κ β : Type} {keys : Finset κ} {g : {k // k ∈ keys} → Option β}
    {f : {k // k ∈ keys} → β} (h : ∀ k, g k = some (f k)) : funImage g = some f := by
  unfold funImage
  rw [dif_pos (fun k => by rw [h k]; rfl)]
  congr 1
  funext k
  exact Option.some.inj ((Option.some_get _).trans (h k))

end Calculus.Alg
