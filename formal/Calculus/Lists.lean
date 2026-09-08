import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Basic
import Calculus.Domain

/-!
# The list plumbing

Everything in this file is a statement about lists and `Option` — no codec, no law, no
member. It lives apart so that `Combinators.lean` reads as codec vocabulary and nothing
else: when a proof there cites a name from this file, that is the signal that the step is
plumbing rather than content.

Three groups:

* Three additions to mathlib's `Forall₂` — `mem_left`, `mem_right`, `compose` — which is
  where the file starts because the next group rests on them.
* `traverse` and its laws — the one proof shape every product consumes. It rests on a
  single pivot, `traverse_eq_some`: **a successful traversal *is* the pointwise relation**
  `List.Forall₂ (f · = some ·)`. Each law is then that relation pushed around — reversed
  for (R), forgotten for (C), composed for (MP) — which is what mathlib's `Forall₂` API
  is for.
* A handful of `filter` facts stated in the form the sum proofs want, mostly about a
  `filter` that resolves to a singleton or to nil.

The bar for adding here is that mathlib genuinely lacks the fact, or states it in a shape
the use sites cannot consume. Anything mathlib has outright should be cited under mathlib's
own name at the use site instead.
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

/-- Chaining two pointwise relations through a shared middle list. A read-then-rewrite
    pair is exactly this: `p` relates attributes to values, `e` relates those values to
    attributes, and the composite relates the two attribute lists. -/
theorem Forall₂.compose {α β γ : Type _} {R : α → β → Prop} {S : β → γ → Prop}
    {T : α → γ → Prop} (h : ∀ x y z, R x y → S y z → T x z) :
    ∀ {xs ys zs}, Forall₂ R xs ys → Forall₂ S ys zs → Forall₂ T xs zs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons hxy hxs, .cons hyz hys => .cons (h _ _ _ hxy hyz) (hxs.compose h hys)

end List

namespace Calculus

/-! ## Traversal — §5's Lemma, clause by clause

This section **is** §5's Lemma (traversal), which five rules — `array`, `tuple`, `record`,
`object`, `set` — are instantiations of. The correspondence was stated nowhere.

> *Let a step be an entrywise pair between the entries of two lists, and lift it entrywise —
> defined where every entry is, positions preserved. If the step satisfies a law pointwise,
> the lift satisfies it listwise.*

| §5's clause | here | how |
| --- | --- | --- |
| the lift itself, positions preserved | `traverse_eq_some` | the pivot: a successful traversal **is** `Forall₂ (f · = some ·)`, which is positional by construction |
| defined where every entry is | `traverse_isSome_of_all` | no partner list — only that every entry is writable |
| **(R)**, "positions re-read in place" | `traverse_roundTrip` | the relation, reversed |
| **(C)**, "each entry re-encodes" | `traverse_isSome` | the relation, forgotten down to definedness |
| **`≼`**, "a shared position decodes and re-encodes through the same step" | `traverse_rel` | the relation, composed — read-then-rewrite is two traversals, so `Forall₂.compose` |
| "lengths survive both directions" | `traverse_length` | one direction; the other is `traverse_roundTrip` and this again |

§5's keyed refinement — *"entries are dispatched and compared by name, first occurrence
first"* — is **gone from this file**, along with the whole association-list section that
served it. It was a statement about `M` as a `List (Name × Attr)`: a clause needed because
a keyed list has an order and can repeat a key. `M` is now a name set with a function on
it, so `Agree.m` compares at a shared key and there is no first occurrence to prefer.
`traverse_fst` survives because `L` really is a list. -/

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

/-- §5, Lemma (traversal), **`≼`** — "a shared position decodes and re-encodes through the
    same step", which is every product's (MP). Read-then-rewrite is a composite of two
    traversals, so `Forall₂.compose`; the zip is what `Agree.l`/`Agree.m` consume. -/
theorem traverse_rel {f : α → Option γ} {R : γ → β → Prop}
    (h : ∀ y x z, g y = some x → f x = some z → R z y) :
    ∀ (ys : List β) (xs : List α) (zs : List γ),
      traverse g ys = some xs → traverse f xs = some zs →
      ∀ q ∈ zs.zip ys, R q.1 q.2 :=
  fun _ _ _ hg hf q hq =>
    List.forall₂_iff_zip.mp
        (((traverse_eq_some.mp hg).compose h (traverse_eq_some.mp hf)).flip)
      |>.2 (by cases q; exact hq)

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




/-- §5, Lemma (traversal), keyed clause: names survive. A traversal that preserves each
    entry's name preserves the list of names. -/
theorem traverse_fst {f : Name × α → Option (Name × β)}
    (hf : ∀ kv kb, f kv = some kb → kb.1 = kv.1) {kvs : List (Name × α)} {ds}
    (h : traverse f kvs = some ds) : ds.map (·.1) = kvs.map (·.1) := by
  induction kvs generalizing ds with
  | nil => cases traverse_eq_some.mp h; rfl
  | cons kv kvs ih =>
      simp only [traverse_cons, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨kb, hkb, ds', hds', rfl⟩ := h
      simp [hf kv kb hkb, ih hds']

end Traverse

theorem contains_of_mem {l : List String} {s : String} (h : s ∈ l) : l.contains s = true :=
  List.contains_iff_mem.mpr h

theorem mem_of_contains {l : List String} {s : String} (h : l.contains s = true) : s ∈ l :=
  List.contains_iff_mem.mp h


/-- Constructive on purpose: mathlib's `filter_eq_nil_iff` routes through
    `Classical.choice`, and §3 of the formalization doc advertises an axiom base without
    it. `Calculus/Axioms.lean` is what keeps that claim honest. -/
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


/-- Filtering to a singleton names an element of the list that satisfies the
    predicate — how a resolved choice is read back. -/
theorem mem_of_filter_eq_singleton {α : Type} {l : List α} {p : α → Bool} {x : α}
    (h : l.filter p = [x]) : x ∈ l ∧ p x = true :=
  List.mem_filter.mp (h ▸ List.mem_cons_self)

/-! Two options resolve to four cases, and a two-option union is where §5's conditions
    are argued. These four state that split once, in both directions. Distinctness is
    needed only to read a singleton back: `[y] = [x]` is otherwise no contradiction. -/

/-- A pair filters to its head when the head passes and the tail does not — §5's
    two-option resolution, one case of four. -/
theorem filter_pair_left {α : Type} {p : α → Bool} {x y : α}
    (hx : p x = true) (hy : p y = false) : List.filter p [x, y] = [x] := by
  simp only [List.filter, hx, hy]

/-- …and to its tail, dually. -/
theorem filter_pair_right {α : Type} {p : α → Bool} {x y : α}
    (hx : p x = false) (hy : p y = true) : List.filter p [x, y] = [y] := by
  simp only [List.filter, hx, hy]

/-- Reading a head-singleton back: exactly the head passed. §5's resolution, inverted. -/
theorem filter_pair_left_inv {α : Type} {p : α → Bool} {x y : α} (hne : x ≠ y)
    (h : List.filter p [x, y] = [x]) : p x = true ∧ p y = false := by
  cases hx : p x <;> cases hy : p y <;>
    simp only [List.filter, hx, hy] at h <;> simp_all

/-- …and a tail-singleton. -/
theorem filter_pair_right_inv {α : Type} {p : α → Bool} {x y : α} (hne : x ≠ y)
    (h : List.filter p [x, y] = [y]) : p x = false ∧ p y = true := by
  cases hx : p x <;> cases hy : p y <;>
    simp only [List.filter, hx, hy] at h <;> simp_all

/-- A property of every image is a property of every member of the mapped list — the
    step every case over a list of subterms begins with. -/
theorem forall_mem_map {α β : Type} {xs : List α} {g : α → β} {P : β → Prop}
    (h : ∀ x ∈ xs, P (g x)) : ∀ y ∈ xs.map g, P y := by
  rintro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact h x hx

/-- …and the same for `Option.map`, which is how a uniform tail is carried. -/
theorem forall_mem_map_option {α β : Type} {x? : Option α} {g : α → β} {P : β → Prop}
    (h : ∀ x ∈ x?, P (g x)) : ∀ y ∈ x?.map g, P y := by
  cases x? <;> simp_all

