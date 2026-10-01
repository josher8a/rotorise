import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Basic
import Calculus.Alg.Combinators

/-!
# The list plumbing and the carried products, over any carriers

The traversal of a list, its laws, and the `filter` facts that the sum proofs consume. None of
them reads a codec. The codec carried between two prisms, `carriedCodec`, and its instance at a
traversal, `entrywise`, read only the prism laws, the payload pair and the member. So each one
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

/-- Constructive on purpose: mathlib's `filter_eq_nil_iff` routes through
    `Classical.choice`, and this module keeps choice out even though the advertised base
    admits it through `Finset`. -/
theorem filter_nil_of {α : Type _} {p : α → Bool} :
    ∀ {l : List α}, (∀ y ∈ l, p y = false) → l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
      have ha := h a (List.mem_cons_self)
      simp only [List.filter, ha]
      exact filter_nil_of fun y hy => h y (List.mem_cons_of_mem a hy)





/-- **Separation.** Suppose a predicate family `adm` pins each list entry to a key: an
    entry admits `x` only when `key x` is that entry's key. If the keys are pairwise
    distinct, then whatever one entry admits, no other does — so filtering by admission
    leaves exactly that entry. This is the shape every disjointness discharger has. -/
theorem filter_eq_singleton_of_disjoint {β α : Type} {adm : β → α → Bool} {x : α} :
    ∀ {os : List β} {Ss : List (α → Prop)},
      List.Forall₂ (fun o S => ∀ y, adm o y = true → S y) os Ss →
      List.Pairwise (fun S T => ∀ y, S y → ¬ T y) Ss →
      ∀ o ∈ os, adm o x = true → os.filter (adm · x) = [o]
  | [], _, .nil, _, _, ho, _ => nomatch ho
  | o₀ :: os', S₀ :: Ss', .cons h₀ hz, hp, o, ho, hx => by
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    by_cases h0 : adm o₀ x = true
    · have hnone : ∀ o' ∈ os', adm o' x = false := by
        intro o' ho'
        cases hq : adm o' x with
        | false => rfl
        | true =>
          obtain ⟨S', hS'mem, hrel⟩ := hz.mem_left ho'
          exact absurd (hrel x hq) (hhead S' hS'mem x (h₀ x h0))
      obtain rfl : o = o₀ := by
        rcases List.mem_cons.mp ho with rfl | ho'
        · rfl
        · exact absurd hx (by rw [hnone o ho']; exact Bool.noConfusion)
      rw [List.filter_cons_of_pos (p := (adm · x)) h0, filter_nil_of hnone]
    · have ho' : o ∈ os' := by
        rcases List.mem_cons.mp ho with rfl | h
        · exact absurd hx (by simp_all)
        · exact h
      rw [List.filter_cons_of_neg (p := (adm · x)) (by simpa using h0)]
      exact filter_eq_singleton_of_disjoint hz htail o ho' hx

/-- A projection is not a different condition — it is a way of *building* the sets. Pull
    each option's label set back along the projection and the sets are disjoint again,
    because an input has at most one label. -/
theorem filter_eq_singleton_of_labels {β α ι : Type}
    {adm : β → α → Bool} {key : α → Option ι} {x : α} {os : List β} {Ss : List (ι → Prop)}
    (hz : List.Forall₂ (fun o S => ∀ y, adm o y = true → ∃ l, key y = some l ∧ S l) os Ss)
    (hp : List.Pairwise (fun S T => ∀ l, S l → ¬ T l) Ss)
    (o : β) (ho : o ∈ os) (hx : adm o x = true) : os.filter (adm · x) = [o] := by
  refine filter_eq_singleton_of_disjoint
    (Ss := Ss.map (fun S y => ∃ l, key y = some l ∧ S l)) ?_ ?_ o ho hx
  · rw [List.forall₂_map_right_iff]; exact hz
  · rw [List.pairwise_map]
    refine hp.imp fun h y hy hy' => ?_
    obtain ⟨l, hk, hS⟩ := hy
    obtain ⟨l', hk', hS'⟩ := hy'
    rw [hk] at hk'; cases hk'
    exact h l hS hS'


/-- …and the same for `Option.map`, which is how a uniform tail is carried. -/
theorem forall_mem_map_option {α β : Type} {x? : Option α} {g : α → β} {P : β → Prop}
    (h : ∀ x ∈ x?, P (g x)) : ∀ y ∈ x?.map g, P y := by
  cases x? <;> simp_all


variable {V M : Type} {member : V → M}

/-! ### A codec carried between two prisms

The shape underneath every product in §3–§4. A pair works on *payloads* — lists of
entries, mostly — and two prisms say which value and which attribute constructor hold
them. Retract, canon and writes split cleanly along that seam: the prism halves are discharged once,
here, and each construction is left with only its payload pair's own round trip,
definedness and agreement.

`pointCodec` above is the degenerate case, where the payload passes through untouched.
The three below are the products: `entrywise` (a traversal, hence `array` and `record`),
`tuple` (`align`, then a traversal) and `object` (a guard, a filter, then a traversal).

`set` is the one product that is *not* an instance, and for a reason worth stating: its
attribute side is a choice among three wire sets, not one constructor. It is argued on
its own below. -/

/-- **A codec between two prisms.** `P` is the held set's condition on the payload;
    `E`/`D` are the payload pair. -/
def carriedCodec {γ δ : Type} (pV : Ctor γ V) (pA : Ctor δ V) (μ₀ : M)
    (P : γ → Prop) (E : γ → Option δ) (D : δ → Option γ) : Codec V M :=
  Codec.ofEP (T := fun v => ∃ x, v = pV.into x ∧ P x)
    (μ := some μ₀)
    (e := fun v => ((pV.out v).bind E).map pA.into)
    (p := fun a => ((pA.out a).bind D).map pV.into)

section Carried
variable {γ δ : Type} {pV : Ctor γ V} {pA : Ctor δ V} {μ₀ : M}
  {P : γ → Prop} {E : γ → Option δ} {D : δ → Option γ}

/-- What it writes: only a value the prism matches, and only what `E` accepts. -/
theorem carried_e {v a} :
    (carriedCodec pV pA μ₀ P E D).e v = some a ↔
      ∃ x y, pV.out v = some x ∧ E x = some y ∧ a = pA.into y := by
  simp [carriedCodec, Option.bind_eq_some_iff, Option.map_eq_some_iff, eq_comm (a := a)]

/-- What it reads: the mirror. -/
theorem carried_p {a v} :
    (carriedCodec pV pA μ₀ P E D).p a = some v ↔
      ∃ y x, pA.out a = some y ∧ D y = some x ∧ v = pV.into x :=
  carried_e (pV := pA) (pA := pV) (μ₀ := ()) (P := fun _ => True) (E := D) (D := E)

/-- (R), (C) and (W) are the payload pair's own, plus the member the attribute
    constructor stamps. The prisms contribute nothing but their two laws. -/
theorem lawfulCore_carried (hμ : ∀ y, member (pA.into y) = μ₀)
    (hr : ∀ x y, E x = some y → D y = some x)
    (hc : ∀ y x, D y = some x → (E x).isSome) :
    LawfulCore member (carriedCodec pV pA μ₀ P E D) where
  retract he := by
    obtain ⟨x, y, hv, hx, rfl⟩ := carried_e.mp he
    exact carried_p.mpr ⟨y, x, pA.out_into y, hr x y hx, pV.into_out hv⟩
  canon hp := by
    obtain ⟨y, x, _, hy, rfl⟩ := carried_p.mp hp
    obtain ⟨y', h'⟩ := Option.isSome_iff_exists.mp (hc y x hy)
    exact Option.isSome_iff_exists.mpr ⟨_, carried_e.mpr ⟨x, y', pV.out_into x, h', rfl⟩⟩
  writes := by
    intro μ hμ' t a he
    obtain ⟨_, y, _, _, rfl⟩ := carried_e.mp he
    exact (hμ y).trans (Option.some.inj hμ')

/-- Canonical reads are the payload pair's own too. -/
theorem lawful_carried (hμ : ∀ y, member (pA.into y) = μ₀)
    (hr : ∀ x y, E x = some y → D y = some x)
    (hcan : ∀ y x, D y = some x → E x = some y) :
    Lawful member (carriedCodec pV pA μ₀ P E D) :=
  have hc := lawfulCore_carried (P := P) hμ hr (fun y x h => by rw [hcan y x h]; rfl)
  .ofRC hc.retract
    (by
      intro a t hp
      obtain ⟨y, x, ha, hy, rfl⟩ := carried_p.mp hp
      exact carried_e.mpr ⟨x, y, pV.out_into x, hcan y x hy, pA.into_out ha⟩)
    hc.writes

/-- `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T`: the held set's condition has to hold of whatever
    payload either half of the pair accepts. -/
theorem carrier_carried
    (hdom : ∀ {x y}, E x = some y → P x)
    (hran : ∀ {y x}, D y = some x → P x) :
    Carrier (carriedCodec pV pA μ₀ P E D) where
  domE he := by
    obtain ⟨x, y, hv, hx, _⟩ := carried_e.mp he
    exact ⟨x, pV.into_out hv, hdom hx⟩
  ranP hp := by
    obtain ⟨y, x, _, hy, rfl⟩ := carried_p.mp hp
    exact ⟨x, rfl, hran hy⟩

end Carried

/-! ### The entrywise product, named once

`array` and `record` are `carriedCodec` where the payload pair is one entry function
traversed: a value constructor holding a list of entries, an attribute constructor
holding a list of wire entries. Named once, §2's laws are discharged once. -/

/-- **The entrywise product**: `carriedCodec` at a traversal. -/
def entrywise {α β : Type} (pV : Ctor (List α) V) (pA : Ctor (List β) V)
    (μ₀ : M) (P : List α → Prop) (f : α → Option β) (g : β → Option α) : Codec V M :=
  carriedCodec pV pA μ₀ P (traverse f) (traverse g)

section Entrywise
variable {α β : Type} {pV : Ctor (List α) V} {pA : Ctor (List β) V}
  {μ₀ : M} {P : List α → Prop} {f : α → Option β} {g : β → Option α}

/-- Canonical reads, entry by entry. -/
theorem lawful_entrywise (hμ : ∀ ys, member (pA.into ys) = μ₀)
    (hr : ∀ x y, f x = some y → g y = some x)
    (hcan : ∀ y x, g y = some x → f x = some y) :
    Lawful member (entrywise pV pA μ₀ P f g) :=
  lawful_carried hμ (traverse_roundTrip hr) (traverse_roundTrip hcan)

theorem carrier_entrywise
    (hdom : ∀ {xs ys}, traverse f xs = some ys → P xs)
    (hran : ∀ {ys xs}, traverse g ys = some xs → P xs) :
    Carrier (entrywise pV pA μ₀ P f g) :=
  carrier_carried hdom hran

end Entrywise

end Calculus.Alg
