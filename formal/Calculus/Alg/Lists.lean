import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Basic
import Calculus.Alg.Combinators

/-!
# The list plumbing and the carried products, over any carriers

The traversal of a list, its laws, and the `filter` facts that the sum proofs consume. None of
them reads a codec. The codec carried by a prism, `carriedCodec`, and its instance at a
traversal, `entrywise`, read only the prism laws, the payload map and the member. So each one
takes the carrier `V` and the members `M` as parameters.

The bar for adding a list fact here is that mathlib lacks the fact, or states it in a shape the
use sites cannot consume.
-/

namespace List

/-- A pointwise relation exhibits a partner for every member of the right-hand list. -/
theorem Forall₂.mem_right {α β : Type _} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → ∀ {y}, y ∈ ys → ∃ x ∈ xs, R x y
  | _, _, .cons hxy hxs, _, hy => by
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact ⟨_, List.mem_cons_self, hxy⟩
      · obtain ⟨x, hx, hR⟩ := hxs.mem_right hy'
        exact ⟨x, List.mem_cons_of_mem _ hx, hR⟩

/-- …and for every member of the left-hand one. -/
theorem Forall₂.mem_left {α β : Type _} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → ∀ {x}, x ∈ xs → ∃ y ∈ ys, R x y
  | _, _, .cons hxy hxs, _, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨_, List.mem_cons_self, hxy⟩
      · obtain ⟨y, hy, hR⟩ := hxs.mem_left hx'
        exact ⟨y, List.mem_cons_of_mem _ hy, hR⟩

end List

namespace Calculus.Alg

/-! ## Traversal — §5's Lemma, clause by clause

This section **is** §5's Lemma (traversal), which five rules — `array`, `tuple`, `record`,
`object`, `set` — are instantiations of.

> *Let a step be an entrywise pair between the entries of two lists, and lift it entrywise —
> defined where every entry is, positions preserved. If the step satisfies a law pointwise,
> the lift satisfies it listwise.*

| §5's clause | here | how |
| --- | --- | --- |
| the lift itself, positions preserved | `traverse_eq_some` | the pivot: a successful traversal **is** `Forall₂ (f · = some ·)`, which is positional by construction |
| defined where every entry is | `traverse_isSome_of_all` | no partner list — only that every entry is writable |
| **(R)**, "positions re-read in place" | `traverse_roundTrip` | the relation, reversed |
| **(C)**, "each entry re-encodes" | `traverse_isSome` | the relation, forgotten down to definedness |
| "lengths survive both directions" | `traverse_length` | one direction; the other is `traverse_roundTrip` and this again | -/

/-- A list traversed by an entrywise partial function: all-or-nothing. -/
def traverse {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs =>
    match f x, traverse f xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

section Traverse
variable {α β γ : Type} {f : α → Option β} {g : β → Option α}

@[simp] theorem traverse_nil : traverse f [] = some [] := rfl

/-- `traverse` of `some` is `some`: the identity, element by element. -/
theorem traverse_some : ∀ xs : List α, traverse some xs = some xs
  | [] => rfl
  | x :: xs => by simp only [traverse, traverse_some xs]

/-- The `cons` step in `Option`'s monad, which is the form `simp` can reason with. -/
theorem traverse_cons {x : α} {xs : List α} :
    traverse f (x :: xs) = (f x).bind fun y => (traverse f xs).map (y :: ·) := by
  simp only [traverse]; cases f x <;> cases traverse f xs <;> rfl

/-- **The pivot** (§5, Lemma (traversal): the lift, positions preserved). A traversal
    succeeds exactly when the entrywise function relates the two lists position by position.
    Everything below is a corollary of this and mathlib's `Forall₂` API. -/
theorem traverse_eq_some {xs : List α} {ys : List β} :
    traverse f xs = some ys ↔ List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [eq_comm]
  | cons x xs ih => cases ys with
    | nil => simp [traverse_cons, Option.bind_eq_some_iff, ih]
    | cons y ys => simp [traverse_cons, Option.bind_eq_some_iff, ih, List.forall₂_cons]

/-- §5, Lemma (traversal): "lengths survive both directions". This is one of them; the
    other is this applied to `traverse_roundTrip`'s conclusion. -/
theorem traverse_length :
    ∀ (xs : List α) (ys : List β), traverse f xs = some ys → xs.length = ys.length :=
  fun _ _ ht => (traverse_eq_some.mp ht).length_eq

/-- A traversal of two parts is defined exactly where both parts are. `list`'s alignment
    splits at the suffix, so the two halves are traversed independently. -/
theorem traverse_append_isSome :
    ∀ (xs ys : List α),
      (traverse f (xs ++ ys)).isSome = ((traverse f xs).isSome && (traverse f ys).isSome)
  | [], ys => by simp
  | x :: xs, ys => by
      simp only [List.cons_append, traverse_cons]
      rw [show (traverse f (xs ++ ys)) = (traverse f (xs ++ ys)) from rfl]
      cases hx : f x <;> simp [traverse_append_isSome xs ys]

/-- §5, Lemma (traversal), **(R)** — "positions re-read in place". Pointwise (R) lifts to
    the traversal: reverse the relation. -/
theorem traverse_roundTrip (h : ∀ x y, f x = some y → g y = some x) :
    ∀ (xs : List α) (ys : List β), traverse f xs = some ys → traverse g ys = some xs :=
  fun _ _ ht => traverse_eq_some.mpr ((traverse_eq_some.mp ht).imp h).flip

/-- §5, Lemma (traversal): "defined where every entry is". Definedness needs no partner
    list — only that every entry is writable. -/
theorem traverse_isSome_of_all {xs : List α} (h : ∀ x ∈ xs, (f x).isSome) :
    (traverse f xs).isSome := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h x (by simp))
      obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.mp (ih fun z hz => h z (by simp [hz]))
      simp [traverse_cons, hy, hys]

/-- §5, Lemma (traversal), **(C)** — "each entry re-encodes". Pointwise (C) lifts to the
    traversal: forget the partner, keep definedness. -/
theorem traverse_isSome {f : α → Option γ} (h : ∀ y x, g y = some x → (f x).isSome) :
    ∀ (ys : List β) (xs : List α), traverse g ys = some xs → (traverse f xs).isSome :=
  fun _ _ ht => traverse_isSome_of_all fun _ hx =>
    let ⟨_, _, hR⟩ := (traverse_eq_some.mp ht).mem_right hx; h _ _ hR

/-- Every output is witnessed by an input it was written from. -/
theorem traverse_mem₂ {xs : List α} {ys} (h : traverse f xs = some ys) :
    ∀ y ∈ ys, ∃ x ∈ xs, f x = some y :=
  fun _ hy => (traverse_eq_some.mp h).mem_right hy

/-- A property of the outputs, established entrywise. -/
theorem traverse_mem {P : β → Prop} (hP : ∀ x y, f x = some y → P y) {xs ys}
    (h : traverse f xs = some ys) : ∀ y ∈ ys, P y :=
  fun _ hy => let ⟨_, _, hf⟩ := traverse_mem₂ h _ hy; hP _ _ hf

/-- A property of the inputs, established entrywise — a traversal only succeeds on a list
    whose every entry the function accepted. -/
theorem traverse_mem_input {P : α → Prop} (hP : ∀ x y, f x = some y → P x) {xs ys}
    (h : traverse f xs = some ys) : ∀ x ∈ xs, P x :=
  fun _ hx => let ⟨_, _, hf⟩ := (traverse_eq_some.mp h).mem_left hx; hP _ _ hf

end Traverse

/-- A property of each image under `g` holds at each element of `x?.map g`. A uniform tail is
    carried by `Option.map`. -/
theorem forall_mem_map_option {α β : Type} {x? : Option α} {g : α → β} {P : β → Prop}
    (h : ∀ x ∈ x?, P (g x)) : ∀ y ∈ x?.map g, P y := by
  cases x? <;> simp_all


variable {V M : Type} {member : V → M}

/-! ### A codec carried by a prism

The shape underneath every product in §3–§4. A payload map works on *payloads* — lists of
entries, mostly — at each orientation, and one prism says which constructor holds them. §2's
laws split cleanly along that seam: the prism is discharged once, here, and each construction
is left with only its payload map's own inverse law and agreement.

`pointCodec` above is the degenerate case, where the payload passes through untouched.
The three below are the products: `entrywise` (a traversal, hence `array` and `record`),
`tuple` (`align`, then a traversal) and `object` (a guard, a filter, then a traversal).

`set` is the one product that is *not* an instance, and for a reason worth stating: its
attribute side is a choice among three wire sets, not one constructor. It is argued on
its own below. -/

/-- **A codec carried by a prism.** `P` is the held set's condition on the payload, and `F o`
    is the payload map at the orientation `o`. -/
def carriedCodec {γ : Type} (s : Summand γ V M member) (P : γ → Prop)
    (F : Orient → γ → Option γ) : Codec V M where
  T v := ∃ x, v = s.p.into x ∧ P x
  μ := some s.μ
  f o v := ((s.p.out v).bind (F o)).map s.p.into

section Carried
variable {γ : Type} {s : Summand γ V M member} {P : γ → Prop} {F : Orient → γ → Option γ}

/-- What it sends at an orientation: only a datum the prism matches, and only what `F o`
    accepts. -/
theorem carried_f {o : Orient} {v a} :
    (carriedCodec s P F).f o v = some a ↔
      ∃ x y, s.p.out v = some x ∧ F o x = some y ∧ a = s.p.into y := by
  simp [carriedCodec, Option.bind_eq_some_iff, Option.map_eq_some_iff, eq_comm (a := a)]

/-- What it writes. -/
theorem carried_e {v a} :
    (carriedCodec s P F).e v = some a ↔
      ∃ x y, s.p.out v = some x ∧ F .host x = some y ∧ a = s.p.into y := carried_f

/-- What it reads. -/
theorem carried_p {a v} :
    (carriedCodec s P F).p a = some v ↔
      ∃ y x, s.p.out a = some y ∧ F .dual y = some x ∧ v = s.p.into x := carried_f

/-- **§2's laws are the payload map's own**: `F o` inverted by `F o.op`. The summand contributes
    its two prism laws and the member that it stamps. -/
theorem lawful_carried
    (hinv : ∀ o x y, F o x = some y → F o.op y = some x) :
    Lawful member (carriedCodec s P F) where
  inv {o _ _} h := by
    obtain ⟨x, y, hv, hx, rfl⟩ := carried_f.mp h
    exact carried_f.mpr ⟨y, x, s.p.out_into y, hinv o x y hx, s.p.into_out hv⟩
  writes := by
    intro μ hμ' t a he
    obtain ⟨_, y, _, _, rfl⟩ := carried_e.mp he
    exact (s.hμ y).trans (Option.some.inj hμ')

/-- `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T`: the held set's condition has to hold of whatever
    payload either half of the pair accepts. -/
theorem carrier_carried
    (hdom : ∀ {x y}, F .host x = some y → P x)
    (hran : ∀ {y x}, F .dual y = some x → P x) :
    Carrier (carriedCodec s P F) where
  domE he := by
    obtain ⟨x, y, hv, hx, _⟩ := carried_e.mp he
    exact ⟨x, s.p.into_out hv, hdom hx⟩
  ranP hp := by
    obtain ⟨y, x, _, hy, rfl⟩ := carried_p.mp hp
    exact ⟨x, rfl, hran hy⟩

end Carried

/-! ### The entrywise product, named once

`array` and `record` are `carriedCodec` where the payload map is one entry map traversed: a
prism holding a list of entries. Named once, §2's laws are discharged once. -/

/-- **The entrywise product**: `carriedCodec` at a traversal of the entry map `h o`. -/
def entrywise {α : Type} (s : Summand (List α) V M member) (P : List α → Prop)
    (h : Orient → α → Option α) : Codec V M :=
  carriedCodec s P fun o => traverse (h o)

section Entrywise
variable {α : Type} {s : Summand (List α) V M member} {P : List α → Prop}
  {h : Orient → α → Option α}

/-- The laws, entry by entry. -/
theorem lawful_entrywise
    (hinv : ∀ o x y, h o x = some y → h o.op y = some x) :
    Lawful member (entrywise s P h) :=
  lawful_carried fun o => traverse_roundTrip (hinv o)

theorem carrier_entrywise
    (hdom : ∀ {xs ys}, traverse (h .host) xs = some ys → P xs)
    (hran : ∀ {ys xs}, traverse (h .dual) ys = some xs → P xs) :
    Carrier (entrywise s P h) :=
  carrier_carried hdom hran

end Entrywise

end Calculus.Alg
