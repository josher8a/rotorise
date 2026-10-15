import Calculus.Dynamo.Alg.Sums
import Calculus.Alg.Recursion
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Agreement below a depth

The solution of a system reads each input at the stage that the depth of the input names,
`Attr.depth`, at both orientations. The budget is a structural recursion on the input, so a closed
term still reduces by `rfl`.

A container reads its element codecs one layer down, because an element is one layer below its
container. So a container turns agreement below `d` into agreement below `d + 1`.
-/

namespace Calculus

/-! ## Depth: the budget of a recursive codec -/

mutual

/-- The stage a recursive codec needs to see all of a datum: leaves need `1`, and each
    container layer needs one more. A set holds scalars, so it is one layer deep whatever its
    size. `M` is a key set with a function on it, so a map's layer is the largest entry
    budget over the key set. -/
def Attr.depth : Attr → Nat
  | .s _ | .n _ | .b _ | .bool _ | .null => 1
  | .ss _ | .ns _ | .bs _ => 2
  | .l as => Attr.depthL as + 1
  | .m keys f => (keys.attach.sup fun k => Attr.depth (f k)) + 1

def Attr.depthL : List Attr → Nat
  | [] => 1
  | a :: as => max (Attr.depth a) (Attr.depthL as)

end

/-- Every datum has depth at least one, so a stage at depth zero reads nothing. -/
theorem Attr.depth_pos (a : Attr) : 0 < Attr.depth a := by
  cases a <;> simp [Attr.depth]

/-- An element of a list is no deeper than the list's budget. -/
theorem Attr.depth_le_depthL : ∀ {as : List Attr} {a : Attr}, a ∈ as →
    Attr.depth a ≤ Attr.depthL as
  | _ :: _, _, .head _ => Nat.le_max_left _ _
  | _ :: _, _, .tail _ h => le_trans (Attr.depth_le_depthL h) (Nat.le_max_right _ _)

/-- Every entry of a map is one layer shallower than the map. -/
theorem Attr.depth_map_entry {keys : Finset Name} {f : {k // k ∈ keys} → Attr}
    (k : {k // k ∈ keys}) : Attr.depth (f k) + 1 <= Attr.depth (.m keys f) :=
  Nat.succ_le_succ
    (Finset.le_sup (f := fun k => Attr.depth (f k)) (Finset.mem_attach _ k))

/-! ## Agreement below a depth

Agreement reads the universe only through one depth on the carrier, so it is the generic
layer's. Here it sits at `Attr.depth`.
The aliases give the names that callers write in full; field notation (`h.mono`, `h.trans`)
reaches the generic lemmas through the abbreviation. -/

/-- Two codecs agree on every input of depth at most `d`, on both sides. -/
abbrev AgreeLe (d : Nat) (c₁ c₂ : Codec) : Prop := Alg.AgreeLe Attr.depth d c₁ c₂

namespace AgreeLe
/-- Every input has depth at least one, so any two codecs agree below depth zero. -/
theorem zero (c₁ c₂ : Codec) : AgreeLe 0 c₁ c₂ :=
  Alg.AgreeLe.zero Attr.depth_pos c₁ c₂

end AgreeLe

export Alg (agreeLe_altCodec)

/-! ## The combinators keep agreement

A container reads its element codecs one layer down, so it turns agreement below `d` into
agreement below `d + 1`. A sum, a restriction and a relabelling read the same input, so they
keep the depth. -/

/-- A `list` reads each element one layer down, so it turns agreement below `d` into agreement
    below `d + 1`. -/
theorem agreeLe_listCodec {d : Nat} {pre₁ pre₂ suf₁ suf₂ : List Codec}
    {sp₁ sp₂ : Option Codec} (hpre : List.Forall₂ (AgreeLe d) pre₁ pre₂)
    (hsp : Option.Rel (AgreeLe d) sp₁ sp₂) (hsuf : List.Forall₂ (AgreeLe d) suf₁ suf₂) :
    AgreeLe (d + 1) (listCodec pre₁ sp₁ suf₁) (listCodec pre₂ sp₂ suf₂) :=
  Alg.agreeLe_listCodec (sL := lS)
    (fun _ _ hx => Nat.succ_le_succ (Attr.depth_le_depthL hx)) hpre hsp hsuf

/-- A set reads its element codec at scalars, which are one layer below the set. -/
theorem agreeLe_setCodec {d : Nat} {c₁ c₂ : Codec} (h : AgreeLe d c₁ c₂) :
    AgreeLe (d + 1) (setCodec c₁) (setCodec c₂) := by
  refine ⟨fun o v hv => ?_⟩
  cases v with
  | ss S => exact setAt_congr fun x _ => h.f o _ (by simp only [Attr.depth] at hv ⊢; omega)
  | ns S => exact setAt_congr fun x _ => h.f o _ (by simp only [Attr.depth] at hv ⊢; omega)
  | bs S => exact setAt_congr fun x _ => h.f o _ (by simp only [Attr.depth] at hv ⊢; omega)
  | _ => rfl

/-! ### Objects

An object reads its entry codecs at the entries of a map, one layer below the map. -/

end Calculus
