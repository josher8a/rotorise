import Calculus.Combinators

/-!
# `opaque` stabilizes — the last fuel in the denotation

After `Term.lazy` was made finite (`Term.lean`), every case of `denote` recurses on a
strict subterm except one: `opaque`. Its regress is not on the term at all — `opaqCodec`
rebuilds itself under `set`/`array`/`record`, so no term gets smaller and fuel is doing
real work.

It is also the one union in the calculus that *is* continuous. `Continuity.lean` shows
`altCodec` is anti-monotone in general, because two options may both admit; `opaqCodec`'s
eight options are pairwise **kind-disjoint**, so at most one ever admits and the
pathology cannot arise. That is what makes this file possible and `union` hopeless.

The consequence: `opaqCodec` needs only as much fuel as the value is deep, and past that
its answer never changes. So `opaque` can be given a fuel-free denotation by supplying
each input its own budget — `Value.depth` on the write side, `Attr.depth` on the read
side — and the laws transfer from `lawful_opaqCodec` through the stabilization lemmas.

This file is §3's `(opaque)` rule and §3's `Uν`, and the sections below say which part of
each they are. Nothing here is about a term other than `opaque`.

Structure:

* `Value.depth` / `Attr.depth` — structural budgets.
* `traverse_congr` — the missing congruence: pointwise-equal functions traverse equally.
* `opaqCodec_e_*` / `opaqCodec_p_*` — the unfoldings, one per constructor of the domain
  each side ranges over. Each collapses `altCodec`'s filter to a single option by
  kind-disjointness, and is where the "at most one admits" argument is actually cashed.

  **Eight on the write side and ten on the read side**, and the asymmetry is §1's rather
  than an oversight: `Value` has eight constructors and `Attr` has ten, because the three
  wire sets `SS`/`NS`/`BS` are one *kind* and three *members* (`Kind`, `Domain.lean`).
  Kind-disjointness is what the (U) argument needs, so the write side has one unfolding per
  option; the read side has one per member it can be handed, three of which route to the
  same option. An earlier version of this header called them "the eight unfoldings, one per
  kind", which is true of `e` and false of `p`.
-/

namespace Calculus

/-! ## Depth — the budget §3's `(opaque)` fixpoint is measured against -/

mutual

/-- Fuel sufficient for `opaqCodec` to see all of `v`: leaves need `1`, each container
    layer one more. -/
def Value.depth : Value → Nat
  | .str _ | .num _ | .bool _ | .bin _ | .null => 1
  -- A value set holds scalars, so it is one layer deep whatever its size — the same
  -- reason `SS`/`NS`/`BS` are `2` on the attribute side.
  | .strSet _ | .numSet _ | .binSet _ => 2
  | .arr vs => Value.depthL vs + 1
  | .map kvs => Value.depthP kvs + 1

def Value.depthL : List Value → Nat
  | [] => 1
  | v :: vs => max (Value.depth v) (Value.depthL vs)

def Value.depthP : List (Name × Value) → Nat
  | [] => 1
  | kv :: kvs => max (Value.depth kv.2) (Value.depthP kvs)

end

mutual

/-- The read-side budget. Wire sets carry payloads, not attributes, so `SS`/`NS`/`BS`
    are one layer deep regardless of length. -/
def Attr.depth : Attr → Nat
  | .s _ | .n _ | .b _ | .bool _ | .null => 1
  | .ss _ | .ns _ | .bs _ => 2
  | .l as => Attr.depthL as + 1
  | .m kvs => Attr.depthP kvs + 1

def Attr.depthL : List Attr → Nat
  | [] => 1
  | a :: as => max (Attr.depth a) (Attr.depthL as)

def Attr.depthP : List (Name × Attr) → Nat
  | [] => 1
  | kv :: kvs => max (Attr.depth kv.2) (Attr.depthP kvs)

end

theorem Value.depth_pos (v : Value) : 0 < Value.depth v := by
  cases v <;> simp [Value.depth]

theorem Attr.depth_pos (a : Attr) : 0 < Attr.depth a := by
  cases a <;> simp [Attr.depth]

/-! ### The four depth measures are one shape

`Value.depthL`, `Value.depthP`, `Attr.depthL` and `Attr.depthP` are the same fold — the
largest entry measure, or 1 for the empty list. Naming it lets the four depth-preservation
companions cite one traversal fact instead of writing the same cons-unfolding out four
times. -/

/-- The largest entry measure, or 1 for the empty list. -/
def maxOf {α : Type} (m : α → Nat) : List α → Nat
  | [] => 1
  | x :: xs => max (m x) (maxOf m xs)

theorem Value.depthL_eq (vs : List Value) : Value.depthL vs = maxOf Value.depth vs := by
  induction vs <;> simp_all [Value.depthL, maxOf]

theorem Value.depthP_eq (kvs : List (Name × Value)) :
    Value.depthP kvs = maxOf (fun kv => Value.depth kv.2) kvs := by
  induction kvs <;> simp_all [Value.depthP, maxOf]

theorem Attr.depthL_eq (as : List Attr) : Attr.depthL as = maxOf Attr.depth as := by
  induction as <;> simp_all [Attr.depthL, maxOf]

theorem Attr.depthP_eq (kvs : List (Name × Attr)) :
    Attr.depthP kvs = maxOf (fun kv => Attr.depth kv.2) kvs := by
  induction kvs <;> simp_all [Attr.depthP, maxOf]

/-- A traversal whose entry step does not increase the measure does not increase the
    list's maximum. -/
theorem traverse_maxOf_le {α β : Type} {f : α → Option β} {mα : α → Nat} {mβ : β → Nat}
    (h : ∀ x y, f x = some y → mβ y ≤ mα x) :
    ∀ (xs : List α) (ys : List β), traverse f xs = some ys → maxOf mβ ys ≤ maxOf mα xs
  | [], ys, htr => by cases (by simpa using htr : [] = ys); simp [maxOf]
  | x :: xs, ys, htr => by
      rw [traverse_cons] at htr
      obtain ⟨y, hy, hrest⟩ := Option.bind_eq_some.mp htr
      obtain ⟨ys', hys', rfl⟩ := Option.map_eq_some'.mp hrest
      have := h x y hy
      have := traverse_maxOf_le h xs ys' hys'
      simp only [maxOf]; omega

/-! ## Traverse congruence

Missing from `Combinators.lean`, and needed everywhere below: the element function is
`(opaqCodec n).e` at one fuel and `(opaqCodec m).e` at another, and the induction
supplies exactly pointwise agreement. -/

theorem traverse_congr {α β : Type} {f g : α → Option β} :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → traverse f xs = traverse g xs
  | [], _ => rfl
  | x :: xs, h => by
      have hx : f x = g x := h x (by simp)
      have hxs : traverse f xs = traverse g xs :=
        traverse_congr xs (fun y hy => h y (by simp [hy]))
      simp only [traverse, hx, hxs]

/-! ## The unfoldings — §3 `(opaque)`, one per constructor of each domain

Each says: at this value's kind, `altCodec`'s filter collapses to exactly one option, so
the union's answer *is* that option's. This is kind-disjointness cashed — the property
`union` in general does not have (`onKind_*` is what `opaque` has and `union` does not),
and the reason `opaque` escapes `Continuity.lean`.

Stated against the option's own codec rather than its literal encoding, so they stay
true if a primitive's shape changes. Every one of them computes through the same eleven
definitions, so those are a local `simp` set for the section rather than eighteen copies
of one list: what is left in each proof is the case split it actually needs. -/

private theorem opaq_unfold (lossy : Bool) (n : Nat) :
    opaqCodec (n+1) lossy =
      altCodec
        [.byAttempt stringCodec, .byAttempt booleanCodec, .byAttempt binaryCodec,
         .byAttempt nullCodec,
         .byAttempt (if lossy then numberCodec else Codec.empty),
         .byAttempt (setCodec (opaqCodec n lossy)),
         .byAttempt (arrayCodec (opaqCodec n lossy)),
         .byAttempt (recordCodec (opaqCodec n lossy))]
        none := rfl

-- Every unfolding computes through the same eleven definitions.
section Unfoldings
attribute [local simp] opaq_unfold altCodec select OptionSem.byAttempt stringCodec booleanCodec
  binaryCodec nullCodec numberCodec setCodec arrayCodec recordCodec Codec.empty

/-- §3 `(opaque)`, write side at kind `string`: only the `S` option admits, so the filter collapses to it. -/
theorem opaqCodec_e_str (lossy : Bool) (n : Nat) (s : String) :
    (opaqCodec (n+1) lossy).e (.str s) = stringCodec.e (.str s) := by
  cases lossy <;> simp

/-- §3 `(opaque)`, write side at kind `boolean`: only the `BOOL` option admits. -/
theorem opaqCodec_e_bool (lossy : Bool) (n : Nat) (b : Bool) :
    (opaqCodec (n+1) lossy).e (.bool b) = booleanCodec.e (.bool b) := by
  cases lossy <;> simp

/-- §3 `(opaque)`, write side at kind `binary`: only the `B` option admits. -/
theorem opaqCodec_e_bin (lossy : Bool) (n : Nat) (b : Bytes) :
    (opaqCodec (n+1) lossy).e (.bin b) = binaryCodec.e (.bin b) := by
  cases lossy <;> simp

/-- §3 `(opaque)`, write side at kind `null`: only the `NULL` point admits — §1's `𝟙` payload. -/
theorem opaqCodec_e_null (lossy : Bool) (n : Nat) :
    (opaqCodec (n+1) lossy).e .null = nullCodec.e .null := by
  cases lossy <;> simp

/-- §3 `(opaque)`, write side at kind `number`. A double outside `D` is admitted by no
    option, so both sides are `none` — which is why `Uν` carries `HOpaque.num`. -/
theorem opaqCodec_e_num (lossy : Bool) (n : Nat) (d : Double) :
    (opaqCodec (n+1) lossy).e (.num d)
      = (if lossy then numberCodec else Codec.empty).e (.num d) := by
  by_cases hw : Numeral.WF d.toDec = true <;> cases lossy <;>
    simp [numberCodec_e_num, hw]

/-- §3 `(opaque)`, write side at kind `set`: the wire member is computed from the elements (`asWireSet`), which is why one option covers `SS`, `NS` and `BS`. -/
theorem opaqCodec_e_strSet (lossy : Bool) (n : Nat) (S : Finset String) :
    (opaqCodec (n+1) lossy).e (.strSet S)
      = (setCodec (opaqCodec n lossy)).e (.strSet S) := by
  cases he : (setCodec (opaqCodec n lossy)).e (.strSet S) <;>
    cases lossy <;> simp [-setCodec, he]

theorem opaqCodec_e_numSet (lossy : Bool) (n : Nat) (S : Finset Double) :
    (opaqCodec (n+1) lossy).e (.numSet S)
      = (setCodec (opaqCodec n lossy)).e (.numSet S) := by
  cases he : (setCodec (opaqCodec n lossy)).e (.numSet S) <;>
    cases lossy <;> simp [-setCodec, he]

theorem opaqCodec_e_binSet (lossy : Bool) (n : Nat) (S : Finset Bytes) :
    (opaqCodec (n+1) lossy).e (.binSet S)
      = (setCodec (opaqCodec n lossy)).e (.binSet S) := by
  cases he : (setCodec (opaqCodec n lossy)).e (.binSet S) <;>
    cases lossy <;> simp [-setCodec, he]

/-- §3 `(opaque)`, write side at kind `array`: the `L` option, recursing at one less fuel. -/
theorem opaqCodec_e_arr (lossy : Bool) (n : Nat) (vs : List Value) :
    (opaqCodec (n+1) lossy).e (.arr vs)
      = (arrayCodec (opaqCodec n lossy)).e (.arr vs) := by
  cases he : (arrayCodec (opaqCodec n lossy)).e (.arr vs) <;>
    cases lossy <;> simp [-arrayCodec, he]

/-- §3 `(opaque)`, write side at kind `map`: the `M` option, recursing at one less fuel. -/
theorem opaqCodec_e_map (lossy : Bool) (n : Nat) (kvs : List (Name × Value)) :
    (opaqCodec (n+1) lossy).e (.map kvs)
      = (recordCodec (opaqCodec n lossy)).e (.map kvs) := by
  cases he : (recordCodec (opaqCodec n lossy)).e (.map kvs) <;>
    cases lossy <;> simp [-recordCodec, he]

end Unfoldings

/-! ## Stabilization

Past `Value.depth v`, more fuel changes nothing. Stated as agreement between any two
sufficient budgets, which is the form the laws need — the write side picks its fuel from
the value and the read side from the attribute, so the two never coincide.

The list companions recurse on constructor children (not on an arbitrary member), which
is what lets the whole block be structural over `Value`/`List Value` — the same shape as
`μSyn`/`μSynList`. -/

mutual

theorem opaq_e_agree (lossy : Bool) :
    ∀ (v : Value) (n m : Nat), Value.depth v ≤ n → Value.depth v ≤ m →
      (opaqCodec n lossy).e v = (opaqCodec m lossy).e v
  | v, 0, _, hn, _ => absurd hn (by simpa using Nat.not_le.mpr (Value.depth_pos v))
  | v, _+1, 0, _, hm => absurd hm (by simpa using Nat.not_le.mpr (Value.depth_pos v))
  | .str _, n'+1, m'+1, hn, hm => by
      rw [opaqCodec_e_str, opaqCodec_e_str]
  | .bool _, n'+1, m'+1, hn, hm => by
      rw [opaqCodec_e_bool, opaqCodec_e_bool]
  | .bin _, n'+1, m'+1, hn, hm => by
      rw [opaqCodec_e_bin, opaqCodec_e_bin]
  | .null, n'+1, m'+1, hn, hm => by
      rw [opaqCodec_e_null, opaqCodec_e_null]
  | .num _, n'+1, m'+1, hn, hm => by
      rw [opaqCodec_e_num, opaqCodec_e_num]
  | .strSet S, n'+1, m'+1, hn, hm => by
      have hn' : (1:Nat) <= n' := by simp only [Value.depth] at hn; omega
      have hm' : (1:Nat) <= m' := by simp only [Value.depth] at hm; omega
      rw [opaqCodec_e_strSet, opaqCodec_e_strSet]
      simp only [setCodec, encSet,
        show ∀ x : String, (opaqCodec n' lossy).e (Value.str x)
             = (opaqCodec m' lossy).e (Value.str x) from
          fun x => opaq_e_agree lossy (.str x) n' m' hn' hm']
  | .numSet S, n'+1, m'+1, hn, hm => by
      have hn' : (1:Nat) <= n' := by simp only [Value.depth] at hn; omega
      have hm' : (1:Nat) <= m' := by simp only [Value.depth] at hm; omega
      rw [opaqCodec_e_numSet, opaqCodec_e_numSet]
      simp only [setCodec, encSet,
        show ∀ x : Double, (opaqCodec n' lossy).e (Value.num x)
             = (opaqCodec m' lossy).e (Value.num x) from
          fun x => opaq_e_agree lossy (.num x) n' m' hn' hm']
  | .binSet S, n'+1, m'+1, hn, hm => by
      have hn' : (1:Nat) <= n' := by simp only [Value.depth] at hn; omega
      have hm' : (1:Nat) <= m' := by simp only [Value.depth] at hm; omega
      rw [opaqCodec_e_binSet, opaqCodec_e_binSet]
      simp only [setCodec, encSet,
        show ∀ x : Bytes, (opaqCodec n' lossy).e (Value.bin x)
             = (opaqCodec m' lossy).e (Value.bin x) from
          fun x => opaq_e_agree lossy (.bin x) n' m' hn' hm']
  | .arr vs, n'+1, m'+1, hn, hm => by
      have hn' : Value.depthL vs <= n' := by simp only [Value.depth] at hn; omega
      have hm' : Value.depthL vs <= m' := by simp only [Value.depth] at hm; omega
      rw [opaqCodec_e_arr, opaqCodec_e_arr]
      show (traverse (opaqCodec n' lossy).e vs).map Attr.l
         = (traverse (opaqCodec m' lossy).e vs).map Attr.l
      rw [opaq_e_agreeL lossy vs n' m' hn' hm']
  | .map kvs, n'+1, m'+1, hn, hm => by
      have hn' : Value.depthP kvs <= n' := by simp only [Value.depth] at hn; omega
      have hm' : Value.depthP kvs <= m' := by simp only [Value.depth] at hm; omega
      rw [opaqCodec_e_map, opaqCodec_e_map]
      show (traverse (encPair (opaqCodec n' lossy)) kvs).map Attr.m
         = (traverse (encPair (opaqCodec m' lossy)) kvs).map Attr.m
      rw [opaq_e_agreeP lossy kvs n' m' hn' hm']

theorem opaq_e_agreeL (lossy : Bool) :
    ∀ (vs : List Value) (n m : Nat), Value.depthL vs <= n -> Value.depthL vs <= m ->
      traverse (opaqCodec n lossy).e vs = traverse (opaqCodec m lossy).e vs
  | [], _, _, _, _ => rfl
  | v :: vs, n, m, hn, hm => by
      have hvn : Value.depth v <= n := by simp only [Value.depthL] at hn; omega
      have hvm : Value.depth v <= m := by simp only [Value.depthL] at hm; omega
      have hsn : Value.depthL vs <= n := by simp only [Value.depthL] at hn; omega
      have hsm : Value.depthL vs <= m := by simp only [Value.depthL] at hm; omega
      have hv := opaq_e_agree lossy v n m hvn hvm
      have hvs := opaq_e_agreeL lossy vs n m hsn hsm
      simp only [traverse, hv, hvs]

theorem opaq_e_agreeP (lossy : Bool) :
    ∀ (kvs : List (Name × Value)) (n m : Nat),
      Value.depthP kvs <= n -> Value.depthP kvs <= m ->
      traverse (encPair (opaqCodec n lossy)) kvs
        = traverse (encPair (opaqCodec m lossy)) kvs
  | [], _, _, _, _ => rfl
  | kv :: kvs, n, m, hn, hm => by
      have hvn : Value.depth kv.2 <= n := by simp only [Value.depthP] at hn; omega
      have hvm : Value.depth kv.2 <= m := by simp only [Value.depthP] at hm; omega
      have hsn : Value.depthP kvs <= n := by simp only [Value.depthP] at hn; omega
      have hsm : Value.depthP kvs <= m := by simp only [Value.depthP] at hm; omega
      have hv := opaq_e_agree lossy kv.2 n m hvn hvm
      have hkvs := opaq_e_agreeP lossy kvs n m hsn hsm
      simp only [traverse, encPair, hv, hkvs]

end

/-! ## The read side

Ten unfoldings rather than eight: wire sets split into `SS`/`NS`/`BS`, all three handled
by the `set` option. Kind-disjointness is the same argument — each attribute constructor
is accepted by at most one of the eight. -/

section UnfoldingsA
attribute [local simp] opaq_unfold altCodec select OptionSem.byAttempt stringCodec booleanCodec
  binaryCodec nullCodec numberCodec setCodec arrayCodec recordCodec Codec.empty

/-- §3 `(opaque)`, read side at member `S`: distinct members, so at most one option admits. -/
theorem opaqCodec_p_s (lossy : Bool) (n : Nat) (s : String) :
    (opaqCodec (n+1) lossy).p (.s s) = stringCodec.p (.s s) := by
  cases lossy <;> simp

/-- §3 `(opaque)`, read side at member `BOOL`. -/
theorem opaqCodec_p_bool (lossy : Bool) (n : Nat) (b : Bool) :
    (opaqCodec (n+1) lossy).p (.bool b) = booleanCodec.p (.bool b) := by
  cases lossy <;> simp

/-- §3 `(opaque)`, read side at member `B`. -/
theorem opaqCodec_p_b (lossy : Bool) (n : Nat) (b : Bytes) :
    (opaqCodec (n+1) lossy).p (.b b) = binaryCodec.p (.b b) := by
  cases lossy <;> simp

/-- §3 `(opaque)`, read side at member `NULL`. -/
theorem opaqCodec_p_null (lossy : Bool) (n : Nat) :
    (opaqCodec (n+1) lossy).p .null = nullCodec.p .null := by
  cases lossy <;> simp

theorem opaqCodec_p_n (lossy : Bool) (n : Nat) (x : Numeral) :
    (opaqCodec (n+1) lossy).p (.n x)
      = (if lossy then numberCodec else Codec.empty).p (.n x) := by
  cases hd : Double.ofDec x with
  | none => cases lossy <;> simp [numberCodec_p_n, hd]
  | some d =>
    by_cases hw : Numeral.WF d.toDec = true <;> cases lossy <;>
      simp [numberCodec_p_n, hd, hw]

/-- §3 `(opaque)`, read side at member `SS` — one of the three members routing to the single `set` option, which is the ten-versus-eight asymmetry in the header. -/
theorem opaqCodec_p_ss (lossy : Bool) (n : Nat) (vs : List String) :
    (opaqCodec (n+1) lossy).p (.ss vs) = (setCodec (opaqCodec n lossy)).p (.ss vs) := by
  cases hp : (setCodec (opaqCodec n lossy)).p (.ss vs) <;>
    cases lossy <;> simp [-setCodec, hp]

/-- §3 `(opaque)`, read side at member `NS`. -/
theorem opaqCodec_p_ns (lossy : Bool) (n : Nat) (vs : List Numeral) :
    (opaqCodec (n+1) lossy).p (.ns vs) = (setCodec (opaqCodec n lossy)).p (.ns vs) := by
  cases hp : (setCodec (opaqCodec n lossy)).p (.ns vs) <;>
    cases lossy <;> simp [-setCodec, hp]

/-- §3 `(opaque)`, read side at member `BS`. -/
theorem opaqCodec_p_bs (lossy : Bool) (n : Nat) (vs : List Bytes) :
    (opaqCodec (n+1) lossy).p (.bs vs) = (setCodec (opaqCodec n lossy)).p (.bs vs) := by
  cases hp : (setCodec (opaqCodec n lossy)).p (.bs vs) <;>
    cases lossy <;> simp [-setCodec, hp]

/-- §3 `(opaque)`, read side at member `L`. -/
theorem opaqCodec_p_l (lossy : Bool) (n : Nat) (as : List Attr) :
    (opaqCodec (n+1) lossy).p (.l as) = (arrayCodec (opaqCodec n lossy)).p (.l as) := by
  cases hp : (arrayCodec (opaqCodec n lossy)).p (.l as) <;>
    cases lossy <;> simp [-arrayCodec, hp]

/-- §3 `(opaque)`, read side at member `M`. -/
theorem opaqCodec_p_m (lossy : Bool) (n : Nat) (kvs : List (Name × Attr)) :
    (opaqCodec (n+1) lossy).p (.m kvs) = (recordCodec (opaqCodec n lossy)).p (.m kvs) := by
  cases hp : (recordCodec (opaqCodec n lossy)).p (.m kvs) <;>
    cases lossy <;> simp [-recordCodec, hp]

end UnfoldingsA

/-! ### Leaf agreement

`SS`/`NS`/`BS` decode *payloads*, not attributes, so their elements are not subterms of
the attribute being decoded. These three standalone lemmas supply what the wire-set cases
need without a recursive call — which is why `Attr.depth` gives them a flat budget of 2. -/

theorem opaq_p_s_agree (lossy : Bool) (s : String) :
    ∀ (n m : Nat), 1 <= n -> 1 <= m ->
      (opaqCodec n lossy).p (.s s) = (opaqCodec m lossy).p (.s s)
  | n, m, hn, hm => by
      cases n with | zero => exact absurd hn (by decide) | succ n' =>
      cases m with | zero => exact absurd hm (by decide) | succ m' =>
      rw [opaqCodec_p_s, opaqCodec_p_s]

theorem opaq_p_n_agree (lossy : Bool) (x : Numeral) :
    ∀ (n m : Nat), 1 <= n -> 1 <= m ->
      (opaqCodec n lossy).p (.n x) = (opaqCodec m lossy).p (.n x)
  | n, m, hn, hm => by
      cases n with | zero => exact absurd hn (by decide) | succ n' =>
      cases m with | zero => exact absurd hm (by decide) | succ m' =>
      rw [opaqCodec_p_n, opaqCodec_p_n]

theorem opaq_p_b_agree (lossy : Bool) (b : Bytes) :
    ∀ (n m : Nat), 1 <= n -> 1 <= m ->
      (opaqCodec n lossy).p (.b b) = (opaqCodec m lossy).p (.b b)
  | n, m, hn, hm => by
      cases n with | zero => exact absurd hn (by decide) | succ n' =>
      cases m with | zero => exact absurd hm (by decide) | succ m' =>
      rw [opaqCodec_p_b, opaqCodec_p_b]

/-! ### Read-side stabilization -/

mutual

theorem opaq_p_agree (lossy : Bool) :
    ∀ (a : Attr) (n m : Nat), Attr.depth a <= n -> Attr.depth a <= m ->
      (opaqCodec n lossy).p a = (opaqCodec m lossy).p a
  | a, 0, _, hn, _ => absurd hn (by simpa using Nat.not_le.mpr (Attr.depth_pos a))
  | a, _+1, 0, _, hm => absurd hm (by simpa using Nat.not_le.mpr (Attr.depth_pos a))
  | .s _, n'+1, m'+1, hn, hm => by
      rw [opaqCodec_p_s, opaqCodec_p_s]
  | .bool _, n'+1, m'+1, hn, hm => by
      rw [opaqCodec_p_bool, opaqCodec_p_bool]
  | .b _, n'+1, m'+1, hn, hm => by
      rw [opaqCodec_p_b, opaqCodec_p_b]
  | .null, n'+1, m'+1, hn, hm => by
      rw [opaqCodec_p_null, opaqCodec_p_null]
  | .n _, n'+1, m'+1, hn, hm => by
      rw [opaqCodec_p_n, opaqCodec_p_n]
  | .ss vs, n'+1, m'+1, hn, hm => by
      have hn' : 1 <= n' := by simp only [Attr.depth] at hn; omega
      have hm' : 1 <= m' := by simp only [Attr.depth] at hm; omega
      rw [opaqCodec_p_ss, opaqCodec_p_ss]
      show (if vs.isEmpty then none
            else (traverse (fun s => (opaqCodec n' lossy).p (.s s)) vs).map Value.set)
         = (if vs.isEmpty then none
            else (traverse (fun s => (opaqCodec m' lossy).p (.s s)) vs).map Value.set)
      rw [traverse_congr vs (fun s _ => opaq_p_s_agree lossy s n' m' hn' hm')]
  | .ns vs, n'+1, m'+1, hn, hm => by
      have hn' : 1 <= n' := by simp only [Attr.depth] at hn; omega
      have hm' : 1 <= m' := by simp only [Attr.depth] at hm; omega
      rw [opaqCodec_p_ns, opaqCodec_p_ns]
      show (if vs.isEmpty then none
            else (traverse (fun x => (opaqCodec n' lossy).p (.n x)) vs).map Value.set)
         = (if vs.isEmpty then none
            else (traverse (fun x => (opaqCodec m' lossy).p (.n x)) vs).map Value.set)
      rw [traverse_congr vs (fun x _ => opaq_p_n_agree lossy x n' m' hn' hm')]
  | .bs vs, n'+1, m'+1, hn, hm => by
      have hn' : 1 <= n' := by simp only [Attr.depth] at hn; omega
      have hm' : 1 <= m' := by simp only [Attr.depth] at hm; omega
      rw [opaqCodec_p_bs, opaqCodec_p_bs]
      show (if vs.isEmpty then none
            else (traverse (fun b => (opaqCodec n' lossy).p (.b b)) vs).map Value.set)
         = (if vs.isEmpty then none
            else (traverse (fun b => (opaqCodec m' lossy).p (.b b)) vs).map Value.set)
      rw [traverse_congr vs (fun b _ => opaq_p_b_agree lossy b n' m' hn' hm')]
  | .l as, n'+1, m'+1, hn, hm => by
      have hn' : Attr.depthL as <= n' := by simp only [Attr.depth] at hn; omega
      have hm' : Attr.depthL as <= m' := by simp only [Attr.depth] at hm; omega
      rw [opaqCodec_p_l, opaqCodec_p_l]
      show (traverse (opaqCodec n' lossy).p as).map Value.arr
         = (traverse (opaqCodec m' lossy).p as).map Value.arr
      rw [opaq_p_agreeL lossy as n' m' hn' hm']
  | .m kvs, n'+1, m'+1, hn, hm => by
      have hn' : Attr.depthP kvs <= n' := by simp only [Attr.depth] at hn; omega
      have hm' : Attr.depthP kvs <= m' := by simp only [Attr.depth] at hm; omega
      rw [opaqCodec_p_m, opaqCodec_p_m]
      show (traverse (decPair (opaqCodec n' lossy)) kvs).map Value.map
         = (traverse (decPair (opaqCodec m' lossy)) kvs).map Value.map
      rw [opaq_p_agreeP lossy kvs n' m' hn' hm']

theorem opaq_p_agreeL (lossy : Bool) :
    ∀ (as : List Attr) (n m : Nat), Attr.depthL as <= n -> Attr.depthL as <= m ->
      traverse (opaqCodec n lossy).p as = traverse (opaqCodec m lossy).p as
  | [], _, _, _, _ => rfl
  | a :: as, n, m, hn, hm => by
      have han : Attr.depth a <= n := by simp only [Attr.depthL] at hn; omega
      have ham : Attr.depth a <= m := by simp only [Attr.depthL] at hm; omega
      have hsn : Attr.depthL as <= n := by simp only [Attr.depthL] at hn; omega
      have hsm : Attr.depthL as <= m := by simp only [Attr.depthL] at hm; omega
      have ha := opaq_p_agree lossy a n m han ham
      have has := opaq_p_agreeL lossy as n m hsn hsm
      simp only [traverse, ha, has]

theorem opaq_p_agreeP (lossy : Bool) :
    ∀ (kvs : List (Name × Attr)) (n m : Nat),
      Attr.depthP kvs <= n -> Attr.depthP kvs <= m ->
      traverse (decPair (opaqCodec n lossy)) kvs
        = traverse (decPair (opaqCodec m lossy)) kvs
  | [], _, _, _, _ => rfl
  | kv :: kvs, n, m, hn, hm => by
      have han : Attr.depth kv.2 <= n := by simp only [Attr.depthP] at hn; omega
      have ham : Attr.depth kv.2 <= m := by simp only [Attr.depthP] at hm; omega
      have hsn : Attr.depthP kvs <= n := by simp only [Attr.depthP] at hn; omega
      have hsm : Attr.depthP kvs <= m := by simp only [Attr.depthP] at hm; omega
      have ha := opaq_p_agree lossy kv.2 n m han ham
      have hkvs := opaq_p_agreeP lossy kvs n m hsn hsm
      simp only [traverse, decPair, ha, hkvs]

end

/-! ## Depth preservation

`opaqCodecω` below picks its write-side fuel from the value and its read-side fuel from
the attribute, so the two budgets never coincide and `retract`/`canon` have to transport
between them. These two lemmas are what licenses the transport: encoding never deepens,
and neither does decoding. -/

theorem Value.depthL_pos (vs : List Value) : 1 <= Value.depthL vs := by
  cases vs with
  | nil => simp [Value.depthL]
  | cons v vs => simp only [Value.depthL]; have := Value.depth_pos v; omega

theorem Value.depthP_pos (kvs : List (Name × Value)) : 1 <= Value.depthP kvs := by
  cases kvs with
  | nil => simp [Value.depthP]
  | cons kv kvs => simp only [Value.depthP]; have := Value.depth_pos kv.2; omega

theorem Attr.depthL_pos (as : List Attr) : 1 <= Attr.depthL as := by
  cases as with
  | nil => simp [Attr.depthL]
  | cons a as => simp only [Attr.depthL]; have := Attr.depth_pos a; omega

theorem Attr.depthP_pos (kvs : List (Name × Attr)) : 1 <= Attr.depthP kvs := by
  cases kvs with
  | nil => simp [Attr.depthP]
  | cons kv kvs => simp only [Attr.depthP]; have := Attr.depth_pos kv.2; omega

/-- A wire set is always exactly one layer of payloads. -/
theorem asWireSet_depth : ∀ {as : List Attr} {a : Attr}, asWireSet as = some a ->
    Attr.depth a = 2 := by
  intro as a h
  simp only [asWireSet] at h
  split at h
  · exact nomatch h
  · split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases hb : binPayloads as with
        | none => rw [hb] at h; exact nomatch h
        | some bs => rw [hb] at h; cases h; rfl

mutual

theorem opaq_e_depth (lossy : Bool) :
    ∀ (v : Value) (n : Nat) (a : Attr), (opaqCodec n lossy).e v = some a ->
      Attr.depth a <= Value.depth v
  | _, 0, _, he => nomatch he
  | .str _, n'+1, a, he => by
      rw [opaqCodec_e_str] at he
      simp only [stringCodec] at he; cases he; simp [Attr.depth, Value.depth]
  | .bool _, n'+1, a, he => by
      rw [opaqCodec_e_bool] at he
      simp only [booleanCodec] at he; cases he; simp [Attr.depth, Value.depth]
  | .bin _, n'+1, a, he => by
      rw [opaqCodec_e_bin] at he
      simp only [binaryCodec] at he; cases he; simp [Attr.depth, Value.depth]
  | .null, n'+1, a, he => by
      rw [opaqCodec_e_null] at he
      simp only [nullCodec] at he; cases he; simp [Attr.depth, Value.depth]
  | .num d, n'+1, a, he => by
      rw [opaqCodec_e_num] at he
      cases lossy with
      | false => simp only [Codec.empty] at he; exact nomatch he
      | true =>
        replace he : numberCodec.e (.num d) = some a := he
        rw [numberCodec_e_num] at he
        by_cases hw : Numeral.WF d.toDec = true
        · rw [if_pos hw] at he; cases he; simp [Attr.depth, Value.depth]
        · rw [if_neg hw] at he; exact nomatch he
  | .set vs, n'+1, a, he => by
      rw [opaqCodec_e_set] at he
      replace he : (traverse (opaqCodec n' lossy).e vs).bind asWireSet = some a := he
      cases htr : traverse (opaqCodec n' lossy).e vs with
      | none => rw [htr] at he; exact nomatch he
      | some as =>
        rw [htr] at he
        rw [asWireSet_depth he]
        simp only [Value.depth]
        have := Value.depthL_pos vs
        omega
  | .arr vs, n'+1, a, he => by
      rw [opaqCodec_e_arr] at he
      replace he : (traverse (opaqCodec n' lossy).e vs).map Attr.l = some a := he
      cases htr : traverse (opaqCodec n' lossy).e vs with
      | none => rw [htr] at he; exact nomatch he
      | some as =>
        rw [htr] at he
        replace he : Attr.l as = a := by simpa using he
        subst he
        simp only [Attr.depth, Value.depth]
        have := opaq_e_depthL lossy vs n' as htr
        omega
  | .map kvs, n'+1, a, he => by
      rw [opaqCodec_e_map] at he
      replace he : (traverse (encPair (opaqCodec n' lossy)) kvs).map Attr.m = some a := he
      cases htr : traverse (encPair (opaqCodec n' lossy)) kvs with
      | none => rw [htr] at he; exact nomatch he
      | some kas =>
        rw [htr] at he
        replace he : Attr.m kas = a := by simpa using he
        subst he
        simp only [Attr.depth, Value.depth]
        have := opaq_e_depthP lossy kvs n' kas htr
        omega

theorem opaq_e_depthL (lossy : Bool) :
    ∀ (vs : List Value) (n : Nat) (as : List Attr),
      traverse (opaqCodec n lossy).e vs = some as ->
      Attr.depthL as <= Value.depthL vs
  | vs, n, as, htr => by
      rw [Attr.depthL_eq, Value.depthL_eq]
      exact traverse_maxOf_le (fun v a hv => opaq_e_depth lossy v n a hv) vs as htr

theorem opaq_e_depthP (lossy : Bool) :
    ∀ (kvs : List (Name × Value)) (n : Nat) (kas : List (Name × Attr)),
      traverse (encPair (opaqCodec n lossy)) kvs = some kas ->
      Attr.depthP kas <= Value.depthP kvs
  | kvs, n, kas, htr => by
      rw [Attr.depthP_eq, Value.depthP_eq]
      refine traverse_maxOf_le (fun kv ka hkv => ?_) kvs kas htr
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some'.mp hkv
      exact opaq_e_depth lossy kv.2 n a ha

end

/-! ### Read-side depth preservation

The wire-set cases need their own list lemmas: their elements come from decoding
*payloads* through the leaf codecs, so they bottom out at depth 1 rather than recursing. -/

theorem opaq_p_s_depth (lossy : Bool) (s : String) :
    ∀ (n : Nat) (v : Value), (opaqCodec n lossy).p (.s s) = some v -> Value.depth v <= 1
  | n, v, hp => by
      cases n with | zero => exact nomatch hp | succ n' =>
      rw [opaqCodec_p_s] at hp
      simp only [stringCodec] at hp; cases hp; simp [Value.depth]

theorem opaq_p_n_depth (lossy : Bool) (x : Numeral) :
    ∀ (n : Nat) (v : Value), (opaqCodec n lossy).p (.n x) = some v -> Value.depth v <= 1
  | n, v, hp => by
      cases n with | zero => exact nomatch hp | succ n' =>
      rw [opaqCodec_p_n] at hp
      cases lossy with
      | false => simp [Codec.empty] at hp
      | true =>
        replace hp : numberCodec.p (.n x) = some v := hp
        rw [numberCodec_p_n] at hp
        cases hd : Double.ofDec x with
        | none => rw [hd] at hp; exact nomatch hp
        | some d =>
          rw [hd] at hp
          replace hp : (if Numeral.WF d.toDec then some (Value.num d) else none) = some v := hp
          by_cases hw : Numeral.WF d.toDec = true
          · rw [if_pos hw] at hp; cases hp; simp [Value.depth]
          · rw [if_neg hw] at hp; exact nomatch hp

theorem opaq_p_b_depth (lossy : Bool) (b : Bytes) :
    ∀ (n : Nat) (v : Value), (opaqCodec n lossy).p (.b b) = some v -> Value.depth v <= 1
  | n, v, hp => by
      cases n with | zero => exact nomatch hp | succ n' =>
      rw [opaqCodec_p_b] at hp
      simp only [binaryCodec] at hp; cases hp; simp [Value.depth]

/-- **The wire sets, once.** A wire set's elements are leaf attributes, and a leaf reads
    to depth 1, so the list it reads to has list-depth 1 — whichever of `SS`/`NS`/`BS`
    it is. The three families differ only in which prism the payload sits in, and the
    argument consults nothing else. -/
theorem opaq_p_leafL {α : Type} (elem : α → Attr) (lossy : Bool) (n : Nat)
    (hleaf : ∀ (x : α) (v : Value), (opaqCodec n lossy).p (elem x) = some v →
      Value.depth v <= 1) :
    ∀ (xs : List α) (vs : List Value),
      traverse (fun x => (opaqCodec n lossy).p (elem x)) xs = some vs ->
      Value.depthL vs <= 1
  | [], vs, htr => by
      replace htr : some [] = some vs := htr
      cases htr; simp [Value.depthL]
  | x :: xs, vs, htr => by
      rw [traverse_cons] at htr
      obtain ⟨v, hv, hrest⟩ := Option.bind_eq_some.mp htr
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some'.mp hrest
      have h1 := hleaf x v hv
      have h2 := opaq_p_leafL elem lossy n hleaf xs vs' hvs'
      simp only [Value.depthL]; omega

/-- …and the wire set itself is one level above its leaves. `p` refuses the empty run,
    which is where §1's `℘⁺fin` shows up in the depth argument. -/
theorem opaq_p_wire_depth {α : Type} (elem : α → Attr) (lossy : Bool) (n : Nat)
    (hleaf : ∀ (x : α) (v : Value), (opaqCodec n lossy).p (elem x) = some v →
      Value.depth v <= 1)
    {xs : List α} {v : Value}
    (hp : (if xs.isEmpty then none
            else (traverse (fun x => (opaqCodec n lossy).p (elem x)) xs).map Value.set)
          = some v) : Value.depth v <= 2 := by
  split at hp
  · exact nomatch hp
  · obtain ⟨vs, htr, rfl⟩ := Option.map_eq_some'.mp hp
    have := opaq_p_leafL elem lossy n hleaf xs vs htr
    simp only [Value.depth]; omega

theorem opaq_p_ssL (lossy : Bool) (n : Nat) :
    ∀ (ss : List String) (vs : List Value),
      traverse (fun s => (opaqCodec n lossy).p (.s s)) ss = some vs ->
      Value.depthL vs <= 1 :=
  opaq_p_leafL Attr.s lossy n fun s v h => opaq_p_s_depth lossy s n v h

theorem opaq_p_nsL (lossy : Bool) (n : Nat) :
    ∀ (xs : List Numeral) (vs : List Value),
      traverse (fun x => (opaqCodec n lossy).p (.n x)) xs = some vs ->
      Value.depthL vs <= 1 :=
  opaq_p_leafL Attr.n lossy n fun x v h => opaq_p_n_depth lossy x n v h

theorem opaq_p_bsL (lossy : Bool) (n : Nat) :
    ∀ (bs : List Bytes) (vs : List Value),
      traverse (fun b => (opaqCodec n lossy).p (.b b)) bs = some vs ->
      Value.depthL vs <= 1 :=
  opaq_p_leafL Attr.b lossy n fun b v h => opaq_p_b_depth lossy b n v h

mutual

theorem opaq_p_depth (lossy : Bool) :
    ∀ (a : Attr) (n : Nat) (v : Value), (opaqCodec n lossy).p a = some v ->
      Value.depth v <= Attr.depth a
  | _, 0, _, hp => nomatch hp
  | .s _, n'+1, v, hp => by
      rw [opaqCodec_p_s] at hp
      simp only [stringCodec] at hp; cases hp; simp [Attr.depth, Value.depth]
  | .bool _, n'+1, v, hp => by
      rw [opaqCodec_p_bool] at hp
      simp only [booleanCodec] at hp; cases hp; simp [Attr.depth, Value.depth]
  | .b _, n'+1, v, hp => by
      rw [opaqCodec_p_b] at hp
      simp only [binaryCodec] at hp; cases hp; simp [Attr.depth, Value.depth]
  | .null, n'+1, v, hp => by
      rw [opaqCodec_p_null] at hp
      simp only [nullCodec] at hp; cases hp; simp [Attr.depth, Value.depth]
  | .n x, n'+1, v, hp => by
      have := opaq_p_n_depth lossy x (n'+1) v hp
      simp only [Attr.depth]; omega
  | .ss ss, n'+1, v, hp => by
      rw [opaqCodec_p_ss] at hp
      have := opaq_p_wire_depth Attr.s lossy n'
        (fun x w h => opaq_p_s_depth lossy x n' w h) hp
      simp only [Attr.depth]; omega
  | .ns xs, n'+1, v, hp => by
      rw [opaqCodec_p_ns] at hp
      have := opaq_p_wire_depth Attr.n lossy n'
        (fun x w h => opaq_p_n_depth lossy x n' w h) hp
      simp only [Attr.depth]; omega
  | .bs bs, n'+1, v, hp => by
      rw [opaqCodec_p_bs] at hp
      have := opaq_p_wire_depth Attr.b lossy n'
        (fun x w h => opaq_p_b_depth lossy x n' w h) hp
      simp only [Attr.depth]; omega
  | .l as, n'+1, v, hp => by
      rw [opaqCodec_p_l] at hp
      replace hp : (traverse (opaqCodec n' lossy).p as).map Value.arr = some v := hp
      cases htr : traverse (opaqCodec n' lossy).p as with
      | none => rw [htr] at hp; exact nomatch hp
      | some vs =>
        rw [htr] at hp
        replace hp : Value.arr vs = v := by simpa using hp
        subst hp
        have := opaq_p_depthL lossy as n' vs htr
        simp only [Attr.depth, Value.depth]; omega
  | .m kvs, n'+1, v, hp => by
      rw [opaqCodec_p_m] at hp
      replace hp : (traverse (decPair (opaqCodec n' lossy)) kvs).map Value.map = some v := hp
      cases htr : traverse (decPair (opaqCodec n' lossy)) kvs with
      | none => rw [htr] at hp; exact nomatch hp
      | some kvs' =>
        rw [htr] at hp
        replace hp : Value.map kvs' = v := by simpa using hp
        subst hp
        have := opaq_p_depthP lossy kvs n' kvs' htr
        simp only [Attr.depth, Value.depth]; omega

theorem opaq_p_depthL (lossy : Bool) :
    ∀ (as : List Attr) (n : Nat) (vs : List Value),
      traverse (opaqCodec n lossy).p as = some vs ->
      Value.depthL vs <= Attr.depthL as
  | as, n, vs, htr => by
      rw [Value.depthL_eq, Attr.depthL_eq]
      exact traverse_maxOf_le (fun a v ha => opaq_p_depth lossy a n v ha) as vs htr

theorem opaq_p_depthP (lossy : Bool) :
    ∀ (kvs : List (Name × Attr)) (n : Nat) (kvs' : List (Name × Value)),
      traverse (decPair (opaqCodec n lossy)) kvs = some kvs' ->
      Value.depthP kvs' <= Attr.depthP kvs
  | kvs, n, kvs', htr => by
      rw [Value.depthP_eq, Attr.depthP_eq]
      refine traverse_maxOf_le (fun ka kv hka => ?_) kvs kvs' htr
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some'.mp hka
      exact opaq_p_depth lossy ka.2 n v hv

end

/-! ## `opaque`, fuel-free — §3's `(opaque)` as a rule with no fuel in it

Each input supplies its own budget: the write side from the value, the read side from the
attribute. The held set is the union over all fuels, which keeps `Carrier` trivial and
still feeds `opaq_TSub` (every fuel's `T` lands in §3's `Uν`).

The two laws that cross sides — `retract` and `canon` — are exactly where the depth
preservation lemmas are spent: `e` answers at `Value.depth v` and `p` at `Attr.depth a`,
and the agreement lemmas move the answer between the two budgets. -/

noncomputable def opaqCodecω (lossy : Bool) : Codec :=
  { T := fun v => ∃ n, (opaqCodec n lossy).T v
    μ := none
    e := fun v => (opaqCodec (Value.depth v) lossy).e v
    p := fun a => (opaqCodec (Attr.depth a) lossy).p a }

theorem opaqCodecω_μ (lossy : Bool) : (opaqCodecω lossy).μ = none := rfl

/-- Every fuel's answer is `opaqCodecω`'s answer, given enough fuel. The bridge `denote`
    will use once `opaque` stops carrying one. -/
theorem opaqCodecω_e (lossy : Bool) (v : Value) (n : Nat) (h : Value.depth v <= n) :
    (opaqCodecω lossy).e v = (opaqCodec n lossy).e v :=
  opaq_e_agree lossy v (Value.depth v) n (Nat.le_refl _) h

theorem opaqCodecω_p (lossy : Bool) (a : Attr) (n : Nat) (h : Attr.depth a <= n) :
    (opaqCodecω lossy).p a = (opaqCodec n lossy).p a :=
  opaq_p_agree lossy a (Attr.depth a) n (Nat.le_refl _) h

theorem lawful_opaqCodecω (lossy : Bool) : Lawful (opaqCodecω lossy) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v a he
    replace he : (opaqCodec (Value.depth v) lossy).e v = some a := he
    have hb : Attr.depth a <= Value.depth v := opaq_e_depth lossy v (Value.depth v) a he
    have hr := (lawful_opaqCodec (Value.depth v) lossy).retract he
    show (opaqCodec (Attr.depth a) lossy).p a = some v
    rw [← opaq_p_agree lossy a (Value.depth v) (Attr.depth a) hb (Nat.le_refl _)]
    exact hr
  · intro a v hp
    replace hp : (opaqCodec (Attr.depth a) lossy).p a = some v := hp
    have hb : Value.depth v <= Attr.depth a := opaq_p_depth lossy a (Attr.depth a) v hp
    have hc := (lawful_opaqCodec (Attr.depth a) lossy).canon hp
    show ((opaqCodec (Value.depth v) lossy).e v).isSome
    rw [opaq_e_agree lossy v (Value.depth v) (Attr.depth a) (Nat.le_refl _) hb]
    exact hc
  · intro μ hμ; exact nomatch hμ
  · intro a v a' hp he
    replace hp : (opaqCodec (Attr.depth a) lossy).p a = some v := hp
    replace he : (opaqCodec (Value.depth v) lossy).e v = some a' := he
    have hb : Value.depth v <= Attr.depth a := opaq_p_depth lossy a (Attr.depth a) v hp
    have he' : (opaqCodec (Attr.depth a) lossy).e v = some a' := by
      rw [← opaq_e_agree lossy v (Value.depth v) (Attr.depth a) (Nat.le_refl _) hb]
      exact he
    exact (lawful_opaqCodec (Attr.depth a) lossy).agree hp he'

theorem carrier_opaqCodecω (lossy : Bool) : Carrier (opaqCodecω lossy) := by
  refine ⟨?_, ?_⟩
  · intro v a he
    exact ⟨Value.depth v, (carrier_opaqCodec (Value.depth v) lossy).domE he⟩
  · intro a v hp
    exact ⟨Attr.depth a, (carrier_opaqCodec (Attr.depth a) lossy).ranP hp⟩

end Calculus
