import Calculus.Dynamo.Alg.Sums
import Calculus.Alg.Recursion
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Guarded recursion

A recursive codec is the limit of its stages. A **body** `B : Codec → Codec` builds one stage
from the one before, and the stages start at `Codec.empty`. The limit reads each input at the
stage its own depth names: `Value.depth` on the write side and `Attr.depth` on the read side.
The budget is a structural recursion on the input, so a closed term still reduces by `rfl`.

The one premise is `Contractive`: the body reads its argument only at inputs strictly shallower
than its own input. A container gives that, because an element is one layer below its container.
From it alone the stages agree past the depth of the input (`muStage_agree`), the limit is a
fixed point of the body (`muCodec_fix`), and lawful stages give a lawful limit
(`lawful_muCodec`). No option of the body has to be disjoint from another for these three.

`opaque` is `muCodec opaqStep`, and `Term.mu` denotes `muCodec` of its body.
-/

namespace Calculus

/-! ## Depth: the budget of a recursive codec -/

mutual

/-- The stage a recursive codec needs to see all of `v`: leaves need `1`, and each container
    layer needs one more. -/
def Value.depth : Value → Nat
  | .str _ | .num _ | .bool _ | .bin _ | .null => 1
  -- A value set holds scalars, so it is one layer deep whatever its size — the same
  -- reason `SS`/`NS`/`BS` are `2` on the attribute side.
  | .strSet _ | .numSet _ | .binSet _ => 2
  | .arr vs => Value.depthL vs + 1
  -- §1's `M` is a key *set* with a function on it, so a map's layer is the largest
  -- entry budget over the key set — a `Finset.sup`, where the array's is a list fold.
  | .map keys f => (keys.attach.sup fun k => Value.depth (f k)) + 1

def Value.depthL : List Value → Nat
  | [] => 1
  | v :: vs => max (Value.depth v) (Value.depthL vs)

end

mutual

/-- The read-side budget. Wire sets carry payloads, not attributes, so `SS`/`NS`/`BS`
    are one layer deep regardless of length. -/
def Attr.depth : Attr → Nat
  | .s _ | .n _ | .b _ | .bool _ | .null => 1
  | .ss _ | .ns _ | .bs _ => 2
  | .l as => Attr.depthL as + 1
  | .m keys f => (keys.attach.sup fun k => Attr.depth (f k)) + 1

def Attr.depthL : List Attr → Nat
  | [] => 1
  | a :: as => max (Attr.depth a) (Attr.depthL as)

end

/-- Every value has depth at least one, so a stage at depth zero reads nothing. -/
theorem Value.depth_pos (v : Value) : 0 < Value.depth v := by
  cases v <;> simp [Value.depth]

/-- Every attribute has depth at least one. -/
theorem Attr.depth_pos (a : Attr) : 0 < Attr.depth a := by
  cases a <;> simp [Attr.depth]

/-- An element of an array is no deeper than the array's list budget. -/
theorem Value.depth_le_depthL : ∀ {vs : List Value} {v : Value}, v ∈ vs →
    Value.depth v ≤ Value.depthL vs
  | _ :: _, _, .head _ => Nat.le_max_left _ _
  | _ :: _, _, .tail _ h => le_trans (Value.depth_le_depthL h) (Nat.le_max_right _ _)

/-- …and the read side of the same. -/
theorem Attr.depth_le_depthL : ∀ {as : List Attr} {a : Attr}, a ∈ as →
    Attr.depth a ≤ Attr.depthL as
  | _ :: _, _, .head _ => Nat.le_max_left _ _
  | _ :: _, _, .tail _ h => le_trans (Attr.depth_le_depthL h) (Nat.le_max_right _ _)

/-- Every entry of a map is one layer shallower than the map. -/
theorem Value.depth_map_entry {keys : Finset Name} {f : {k // k ∈ keys} → Value}
    (k : {k // k ∈ keys}) : Value.depth (f k) + 1 <= Value.depth (.map keys f) :=
  Nat.succ_le_succ
    (Finset.le_sup (f := fun k => Value.depth (f k)) (Finset.mem_attach _ k))

/-- …and the read side of the same. -/
theorem Attr.depth_map_entry {keys : Finset Name} {f : {k // k ∈ keys} → Attr}
    (k : {k // k ∈ keys}) : Attr.depth (f k) + 1 <= Attr.depth (.m keys f) :=
  Nat.succ_le_succ
    (Finset.le_sup (f := fun k => Attr.depth (f k)) (Finset.mem_attach _ k))

/-! ## Agreement below a depth

Agreement, the guard, the recursive codec and its laws read the universe only through a depth on
each carrier, so they are the generic layer's. Here they sit at `Value.depth` and `Attr.depth`.
The aliases give the names that callers write in full; field notation (`h.mono`, `h.trans`)
reaches the generic lemmas through the abbreviation. -/

/-- Two codecs agree on every input of depth at most `d`, on both sides. -/
abbrev AgreeLe (d : Nat) (c₁ c₂ : Codec) : Prop := Alg.AgreeLe Value.depth Attr.depth d c₁ c₂

namespace AgreeLe
/-- Every input has depth at least one, so any two codecs agree below depth zero. -/
theorem zero (c₁ c₂ : Codec) : AgreeLe 0 c₁ c₂ :=
  Alg.AgreeLe.zero Value.depth_pos Attr.depth_pos c₁ c₂

end AgreeLe

/-! ## The construct -/

/-- **The guard, on a body.** The body reads its argument only at inputs strictly shallower than
    its own input, on both sides. -/
abbrev Contractive (B : Codec → Codec) : Prop := Alg.Contractive Value.depth Attr.depth B

export Alg (muStage muStage_induct carrier_muCodec agreeLe_altCodec)

/-- **The recursive codec**: each input read at the stage its own depth names. -/
abbrev muCodec (B : Codec → Codec) : Codec := Alg.muCodec Value.depth Attr.depth B

/-- **Stability.** Past the depth of the input, a later stage changes nothing. -/
theorem muStage_agree {B : Codec → Codec} (hB : Contractive B) {d : Nat} :
    ∀ k, AgreeLe d (muStage B d) (muStage B (d + k)) :=
  Alg.muStage_agree Value.depth_pos Attr.depth_pos hB

/-- **The fixed point.** The limit sends what its body sends over the limit, at each
    orientation. -/
theorem muCodec_fix {B : Codec → Codec} (hB : Contractive B) (o : Alg.Orient)
    (x : Alg.Side Value o.c) : (muCodec B).f o x = (B (muCodec B)).f o x :=
  Alg.muCodec_fix Value.depth_pos Attr.depth_pos hB o x

/-- **Lawful stages give a lawful limit.** -/
theorem lawful_muCodec {B : Codec → Codec} (hB : Contractive B)
    (hs : ∀ n, Lawful (muStage B n)) : Lawful (muCodec B) :=
  Alg.lawful_muCodec Value.depth_pos Attr.depth_pos hB hs

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
  Alg.agreeLe_listCodec (pV := arrV) (pA := lA) (μL := .L)
    (fun _ _ hx => Nat.succ_le_succ (Value.depth_le_depthL hx))
    (fun _ _ hx => Nat.succ_le_succ (Attr.depth_le_depthL hx)) hpre hsp hsuf

/-- An array is the spread-only `list`, and so reads its elements one layer down. -/
theorem agreeLe_arrayCodec {d : Nat} {c₁ c₂ : Codec} (h : AgreeLe d c₁ c₂) :
    AgreeLe (d + 1) (arrayCodec c₁) (arrayCodec c₂) := by
  rw [arrayCodec_eq_listCodec, arrayCodec_eq_listCodec]
  exact agreeLe_listCodec .nil (.some h) .nil

/-- A record reads each entry one layer below the map. -/
theorem agreeLe_recordCodec {d : Nat} {c₁ c₂ : Codec} (h : AgreeLe d c₁ c₂) :
    AgreeLe (d + 1) (recordCodec c₁) (recordCodec c₂) := by
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · cases v with
    | m keys f =>
      have hk : ∀ k, c₁.e (f k) = c₂.e (f k) := fun k =>
        h.e _ (by have := Value.depth_map_entry (f := f) k; simp only [Value.map] at this; omega)
      simp only [recordCodec, hk, Alg.Codec.ofEP_e]
    | _ => rfl
  · cases a with
    | m keys g =>
      have hk : ∀ k, c₁.p (g k) = c₂.p (g k) := fun k =>
        h.p _ (by have := Attr.depth_map_entry (f := g) k; omega)
      simp only [recordCodec, hk, Alg.Codec.ofEP_p]
    | _ => rfl

/-- A set reads its element codec at scalars, which are one layer below the set. -/
theorem agreeLe_setCodec {d : Nat} {c₁ c₂ : Codec} (h : AgreeLe d c₁ c₂) :
    AgreeLe (d + 1) (setCodec c₁) (setCodec c₂) := by
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · cases v with
    | ss S => exact encSet_congr fun x _ => h.e _ (by simp only [Value.depth] at hv ⊢; omega)
    | ns S => exact encSet_congr fun x _ => h.e _ (by simp only [Value.depth] at hv ⊢; omega)
    | bs S => exact encSet_congr fun x _ => h.e _ (by simp only [Value.depth] at hv ⊢; omega)
    | _ => rfl
  · cases a with
    | ss S => exact decSet_congr fun x _ => h.p _ (by simp only [Attr.depth] at ha ⊢; omega)
    | ns S => exact decSet_congr fun x _ => h.p _ (by simp only [Attr.depth] at ha ⊢; omega)
    | bs S => exact decSet_congr fun x _ => h.p _ (by simp only [Attr.depth] at ha ⊢; omega)
    | _ => rfl

/-! ### Objects

An object reads its entry codecs at the entries of a map, one layer below the map. -/

end Calculus
