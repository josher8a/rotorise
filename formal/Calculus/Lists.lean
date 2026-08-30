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

* `traverse` and its laws — the one proof shape every product consumes. It rests on a
  single pivot, `traverse_eq_some`: **a successful traversal *is* the pointwise relation**
  `List.Forall₂ (f · = some ·)`. Each law is then that relation pushed around — reversed
  for (R), forgotten for (C), composed for (MP) — which is what mathlib's `Forall₂` API
  is for.
* `List.lookup` on association lists, which mathlib develops only for `AList`/`dlookup`.
  The pivot is `lookup_cons`, after which `simp`/`split` decides the family.
* A handful of `filter` and `zip` facts stated in the form the object codec wants.

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
      · exact ⟨_, List.mem_cons_self _ _, hxy⟩
      · obtain ⟨x, hx, hR⟩ := hxs.mem_right hy'
        exact ⟨x, List.mem_cons_of_mem _ hx, hR⟩

/-- …and for every member of the left-hand one. -/
theorem Forall₂.mem_left {α β : Type _} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → ∀ {x}, x ∈ xs → ∃ y ∈ ys, R x y
  | _, _, .cons hxy hxs, _, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨_, List.mem_cons_self _ _, hxy⟩
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

/-- The `cons` step of `List.lookup`, as an `if` — the pivot for the family below.
    Mathlib develops `lookup` only for `AList`/`dlookup`, so this is stated here. -/
theorem lookup_cons_eq {κ α : Type _} [BEq κ] [LawfulBEq κ] {k k₁ : κ} {v₁ : α}
    {l : List (κ × α)} :
    List.lookup k ((k₁, v₁) :: l) = if k == k₁ then some v₁ else List.lookup k l := by
  simp only [List.lookup]; split <;> simp_all

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

And the keyed refinement, which §5 adds in one sentence:

> *Keyed lists add one clause: entries are dispatched and compared by name, first occurrence
> first, so the lookup form of `≼`'s `M` clause follows from the pointwise one.*

| | here |
| --- | --- |
| names survive the traversal | `traverse_fst` |
| dispatched and compared by name, **first occurrence first** | `lookup_rel`, in the Lookup section below |

`lookup_rel` earns "first occurrence first" without a `Nodup`: it recurses in lockstep and
demands only that names agree at each position. §1's `M` admits duplicate keys, so that is
load-bearing rather than a convenience. -/

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
    | nil => simp [traverse_cons, Option.bind_eq_some, ih]
    | cons y ys => simp [traverse_cons, Option.bind_eq_some, ih, List.forall₂_cons]

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

theorem traverse_map {g : γ → α} :
    ∀ l : List γ, traverse f (l.map g) = traverse (fun x => f (g x)) l
  | [] => rfl
  | x :: l => by simp only [List.map, traverse_cons, traverse_map l]

theorem traverse_append {l₁ l₂ : List α} {r₁ r₂}
    (h₁ : traverse f l₁ = some r₁) (h₂ : traverse f l₂ = some r₂) :
    traverse f (l₁ ++ l₂) = some (r₁ ++ r₂) :=
  traverse_eq_some.mpr
    (List.rel_append (traverse_eq_some.mp h₁) (traverse_eq_some.mp h₂))

theorem traverse_append_inv :
    ∀ {l₁ l₂ : List α} {r}, traverse f (l₁ ++ l₂) = some r →
      ∃ r₁ r₂, r = r₁ ++ r₂ ∧ traverse f l₁ = some r₁ ∧ traverse f l₂ = some r₂
  | [], _, r, h => ⟨[], r, rfl, rfl, h⟩
  | x :: l₁, l₂, r, h => by
      simp only [List.cons_append, traverse_cons, Option.bind_eq_some,
        Option.map_eq_some'] at h
      obtain ⟨y, hy, r', hr', rfl⟩ := h
      obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := traverse_append_inv hr'
      exact ⟨y :: r₁, r₂, rfl, by simp [traverse_cons, hy, h₁], h₂⟩

/-- §5, Lemma (traversal), keyed clause: names survive. A traversal that preserves each
    entry's name preserves the list of names. -/
theorem traverse_fst {f : Name × α → Option (Name × β)}
    (hf : ∀ kv kb, f kv = some kb → kb.1 = kv.1) {kvs : List (Name × α)} {ds}
    (h : traverse f kvs = some ds) : ds.map (·.1) = kvs.map (·.1) := by
  induction kvs generalizing ds with
  | nil => cases traverse_eq_some.mp h; rfl
  | cons kv kvs ih =>
      simp only [traverse_cons, Option.bind_eq_some, Option.map_eq_some'] at h
      obtain ⟨kb, hkb, ds', hds', rfl⟩ := h
      simp [hf kv kb hkb, ih hds']

end Traverse

/-! ## Association lists

`List.lookup` on `List (Name × α)`. Mathlib develops the theory for `AList`/`dlookup`
instead, so the small part this development needs is proved here, off `lookup_cons_eq`. -/

section Lookup
variable {α β : Type}

theorem mem_of_lookup : ∀ {l : List (Name × α)} {k v}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => nomatch h
  | (k₁, v₁) :: l, k, v, h => by
      rw [List.lookup_cons_eq] at h
      split at h
      · rename_i hbe; cases h; cases eq_of_beq hbe; exact List.mem_cons_self _ _
      · exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem mem_fst_of_lookup {l : List (Name × α)} {k v} (h : l.lookup k = some v) :
    k ∈ l.map (·.1) :=
  List.mem_map.mpr ⟨(k, v), mem_of_lookup h, rfl⟩

theorem exists_of_mem_fst {l : List (Name × α)} {k} (h : k ∈ l.map (·.1)) :
    ∃ x, (k, x) ∈ l := by
  obtain ⟨p, hp, hp1⟩ := List.mem_map.mp h
  exact ⟨p.2, by rw [← hp1]; exact hp⟩

theorem lookup_isSome_of_mem_fst :
    ∀ {l : List (Name × α)} {k}, k ∈ l.map (·.1) → (l.lookup k).isSome = true
  | [], _, h => absurd h (by simp)
  | (k₁, _) :: l, k, h => by
      rw [List.lookup_cons_eq]
      split
      · rfl
      · rename_i hbe
        simp only [List.map, List.mem_cons] at h
        exact lookup_isSome_of_mem_fst (h.resolve_left fun hk => by simp [hk] at hbe)

theorem lookup_eq_of_mem_nodup :
    ∀ {l : List (Name × α)} {k v}, (l.map (·.1)).Nodup → (k, v) ∈ l →
      l.lookup k = some v
  | [], _, _, _, hm => nomatch hm
  | (k₁, v₁) :: l, k, v, hnd, hm => by
      obtain ⟨hnotin, hnd'⟩ := List.nodup_cons.mp hnd
      rw [List.lookup_cons_eq]
      rcases List.mem_cons.mp hm with heq | hm'
      · cases heq; simp
      · split
        · rename_i hbe
          have hk : k = k₁ := eq_of_beq hbe
          subst hk
          exact absurd (List.mem_map.mpr ⟨(k, v), hm', rfl⟩) hnotin
        · exact lookup_eq_of_mem_nodup hnd' hm'

theorem lookup_none_of_not_mem_fst :
    ∀ {l : List (Name × α)} {k}, k ∉ l.map (·.1) → l.lookup k = none
  | [], _, _ => rfl
  | (k₁, _) :: l, k, h => by
      rw [List.lookup_cons_eq]
      split
      · rename_i hbe; cases eq_of_beq hbe; exact absurd (by simp) h
      · exact lookup_none_of_not_mem_fst fun h' => h (by simp [h'])

/-- §5, Lemma (traversal), keyed clause: **"dispatched and compared by name, first
    occurrence first"** — what `Agree.m` consumes on the object codec. No `Nodup`: see the
    section header for why that is the content. -/
theorem lookup_rel {R : α → β → Prop} :
    ∀ (l₁ : List (Name × α)) (l₂ : List (Name × β)),
      l₁.length = l₂.length →
      (∀ q ∈ l₁.zip l₂, q.1.1 = q.2.1 ∧ R q.1.2 q.2.2) →
      ∀ k a b, l₁.lookup k = some a → l₂.lookup k = some b → R a b
  | [], [], _, _, _, _, _, h1, _ => nomatch h1
  | [], _ :: _, hlen, _, _, _, _, _, _ => nomatch hlen
  | _ :: _, [], hlen, _, _, _, _, _, _ => nomatch hlen
  | (k₁, a₁) :: l₁, (k₂, b₁) :: l₂, hlen, hzip, k, a, b, h1, h2 => by
      obtain ⟨hk, hR⟩ := hzip ((k₁, a₁), (k₂, b₁)) (List.mem_cons_self _ _)
      simp only at hk
      subst hk
      rw [List.lookup_cons_eq] at h1 h2
      split at h1
      · rw [if_pos ‹_›] at h2; cases h1; cases h2; exact hR
      · rw [if_neg ‹_›] at h2
        exact lookup_rel l₁ l₂ (by simpa using hlen)
          (fun q hq => hzip q (List.mem_cons_of_mem _ hq)) k a b h1 h2

theorem lookup_append :
    ∀ (l₁ l₂ : List (Name × α)) (k : Name),
      (l₁ ++ l₂).lookup k =
        match l₁.lookup k with
        | some v => some v
        | none => l₂.lookup k
  | [], _, _ => rfl
  | (k₁, v₁) :: l₁, l₂, k => by
      show ((k₁, v₁) :: (l₁ ++ l₂)).lookup k = _
      rw [List.lookup_cons_eq, List.lookup_cons_eq]
      split
      · rfl
      · exact lookup_append l₁ l₂ k

/-- Filtering on the key does not disturb a lookup the filter keeps… -/
theorem lookup_filter_pos {kn : Name → Bool} {k : Name} (hk : kn k = true) :
    ∀ (l : List (Name × α)), (l.filter fun kv => kn kv.1).lookup k = l.lookup k
  | [] => rfl
  | (k₁, v₁) :: l => by
      simp only [List.filter]
      cases hkn₁ : kn k₁ with
      | true => rw [List.lookup_cons_eq, List.lookup_cons_eq]
                split
                · rfl
                · exact lookup_filter_pos hk l
      | false =>
        rw [List.lookup_cons_eq, if_neg]
        · exact lookup_filter_pos hk l
        · intro hbe; cases eq_of_beq hbe; rw [hk] at hkn₁; exact nomatch hkn₁

/-- …and removes every lookup it drops. -/
theorem lookup_filter_neg {kn : Name → Bool} {k : Name} (hk : kn k = false) :
    ∀ (l : List (Name × α)), (l.filter fun kv => kn kv.1).lookup k = none
  | [] => rfl
  | (k₁, v₁) :: l => by
      simp only [List.filter]
      cases hkn₁ : kn k₁ with
      | true =>
        rw [List.lookup_cons_eq, if_neg]
        · exact lookup_filter_neg hk l
        · intro hbe; cases eq_of_beq hbe; rw [hk] at hkn₁; exact nomatch hkn₁
      | false => exact lookup_filter_neg hk l

end Lookup

/-! ## Filters, membership and zips

Stated in the shape the use sites want; each is a line of mathlib underneath. -/

section Misc
variable {α β : Type}

theorem contains_of_mem {l : List String} {s : String} (h : s ∈ l) : l.contains s = true :=
  List.contains_iff_mem.mpr h

theorem mem_of_contains {l : List String} {s : String} (h : l.contains s = true) : s ∈ l :=
  List.contains_iff_mem.mp h

theorem contains_eq_false_of_not_mem {l : List String} {s : String} (h : s ∉ l) :
    l.contains s = false := by
  simpa using fun hc => h (List.contains_iff_mem.mp hc)

/-- Constructive on purpose: mathlib's `filter_eq_nil_iff` routes through
    `Classical.choice`, and §3 of the formalization doc advertises an axiom base without
    it. `Calculus/Axioms.lean` is what keeps that claim honest. -/
theorem filter_nil_of {p : α → Bool} :
    ∀ {l : List α}, (∀ y ∈ l, p y = false) → l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
      have ha := h a (List.mem_cons_self a l)
      simp only [List.filter, ha]
      exact filter_nil_of fun y hy => h y (List.mem_cons_of_mem a hy)

theorem filter_eq_self_of_all {p : α → Bool} {l : List α} (h : ∀ x ∈ l, p x = true) :
    l.filter p = l :=
  List.filter_eq_self.mpr h

/-- The unique survivor of a filter on a duplicate-free list. -/
theorem filter_singleton_of {p : α → Bool} :
    ∀ {l : List α} {x : α}, l.Nodup → x ∈ l → p x = true →
      (∀ y ∈ l, y ≠ x → p y = false) → l.filter p = [x]
  | [], x, _, hx, _, _ => nomatch hx
  | a :: l, x, hnd, hx, hpx, hout => by
      have hnd' := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp hx with rfl | hx'
      · have hnil : l.filter p = [] :=
          filter_nil_of fun y hy =>
            hout y (List.mem_cons_of_mem x hy) (fun h => hnd'.1 (h ▸ hy))
        simp only [List.filter, hpx, hnil]
      · have hax : a ≠ x := fun h => hnd'.1 (h ▸ hx')
        have hpa := hout a (List.mem_cons_self a l) hax
        simp only [List.filter, hpa]
        exact filter_singleton_of hnd'.2 hx' hpx
          (fun y hy hyx => hout y (List.mem_cons_of_mem a hy) hyx)

theorem filter_map_comm (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).filter p = (l.filter fun x => p (f x)).map f :=
  List.filter_map f l

theorem ne_nil_of_isEmpty_false {l : List α} (h : l.isEmpty = false) : l ≠ [] := by
  simpa using h

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

/-- The single-label case: one key per option, keys distinct. An instance of the above at
    a total projection and singleton label sets — `Nodup` is disjointness of singletons. -/
theorem filter_eq_singleton_of_keys {β α ι : Type} [DecidableEq ι]
    {adm : β → α → Bool} {key : α → ι} {x : α} {os : List β} {ks : List ι}
    (hz : List.Forall₂ (fun o k => ∀ y, adm o y = true → key y = k) os ks) (hnd : ks.Nodup)
    (o : β) (ho : o ∈ os) (hx : adm o x = true) : os.filter (adm · x) = [o] := by
  refine filter_eq_singleton_of_labels (key := fun y => some (key y))
    (Ss := ks.map (fun k l => l = k)) ?_ ?_ o ho hx
  · rw [List.forall₂_map_right_iff]
    exact hz.imp fun _ _ h y hy => ⟨key y, rfl, h y hy⟩
  · rw [List.pairwise_map]
    exact hnd.imp fun hne l hl hl' => hne (hl.symm.trans hl')

/-- Filtering to a singleton names an element of the list that satisfies the
    predicate — how a resolved choice is read back. -/
theorem mem_of_filter_eq_singleton {α : Type} {l : List α} {p : α → Bool} {x : α}
    (h : l.filter p = [x]) : x ∈ l ∧ p x = true :=
  List.mem_filter.mp (h ▸ List.mem_cons_self x [])

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

theorem mem_zip_left :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
      ∀ x, x ∈ l₁ → ∃ y, (x, y) ∈ l₁.zip l₂
  | [], _, _, _, hx => nomatch hx
  | _ :: _, [], hlen, _, _ => nomatch hlen
  | a :: l₁, b :: l₂, hlen, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨b, List.mem_cons_self _ _⟩
      · obtain ⟨y, hy⟩ := mem_zip_left l₁ l₂ (by simpa using hlen) x hx'
        exact ⟨y, List.mem_cons_of_mem _ hy⟩

end Misc

end Calculus
