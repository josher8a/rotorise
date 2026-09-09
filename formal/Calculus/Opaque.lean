import Calculus.Frontier
import Mathlib.Data.Finset.Lattice.Fold

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
* `maxOf` / `traverse_maxOf_le` — the measure and the step that keeps it: a traversal whose
  entry step does not increase the measure does not increase the list's maximum.
* `opaqCodec_e_*` / `opaqCodec_p_*` — the unfoldings, one per constructor of the domain
  each side ranges over. Each collapses `altCodec`'s filter to a single option by
  kind-disjointness, and is where the "at most one admits" argument is actually cashed.

  **Ten a side**, one per constructor of the domain that side ranges over: `Value` has ten
  and so does `Attr`, the three wire sets appearing on both (`strSet`/`numSet`/`binSet`
  against `ss`/`ns`/`bs`).

  **There is no asymmetry here, and this header used to explain one.** It said eight on the
  write side against ten on the read side, and grounded the difference in the wire sets
  being "one *kind* and three *members*" — which is the very reason `Value` has three of
  them too, so the explanation refuted its own premise. The counts were wrong and the
  argument was wrong about a fact that could be counted; both are corrected here, and what
  survives is the part that was never about a count. Kind-disjointness is what the (U)
  argument needs, so what each unfolding does is collapse `altCodec`'s filter to a single
  option — and on the read side three members route to one option, which is a fact about
  `Kind` (`Domain.lean`) and not about how many lemmas there are.
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
  -- §1's `M` is a key *set* with a function on it, so a map's layer is the largest
  -- entry budget over the key set — a `Finset.sup`, where the array's is a list fold.
  -- There is no list to recurse down and so no ~~depthP~~ companion.
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

theorem Value.depth_pos (v : Value) : 0 < Value.depth v := by
  cases v <;> simp [Value.depth]

theorem Attr.depth_pos (a : Attr) : 0 < Attr.depth a := by
  cases a <;> simp [Attr.depth]

/-! ### Entries are one layer shallower

What the list companions get from unfolding a `cons`, the map cases get from `Finset.sup`:
every entry is under the sup, and the sup is under any bound all the entries meet. Two
lemmas each way, and they are the whole of what the `map`/`M` cases below need. -/

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

/-- A map is no deeper than a bound its every entry meets. -/
theorem Attr.depth_m_le {keys : Finset Name} {f : {k // k ∈ keys} → Attr} {b : Nat}
    (h : ∀ k, Attr.depth (f k) <= b) : Attr.depth (.m keys f) <= b + 1 :=
  Nat.succ_le_succ (Finset.sup_le fun k _ => h k)

/-- …and the write side of the same. -/
theorem Value.depth_map_le {keys : Finset Name} {f : {k // k ∈ keys} → Value} {b : Nat}
    (h : ∀ k, Value.depth (f k) <= b) : Value.depth (.map keys f) <= b + 1 :=
  Nat.succ_le_succ (Finset.sup_le fun k _ => h k)

/-! ### The four depth measures are one shape

`Value.depthL` and `Attr.depthL` are the same fold — the largest entry measure, or 1 for
the empty list. Naming it lets both depth-preservation companions cite one traversal fact
instead of writing the same cons-unfolding out twice. -/

/-- The largest entry measure, or 1 for the empty list. -/
def maxOf {α : Type} (m : α → Nat) : List α → Nat
  | [] => 1
  | x :: xs => max (m x) (maxOf m xs)

theorem Value.depthL_eq (vs : List Value) : Value.depthL vs = maxOf Value.depth vs := by
  induction vs <;> simp_all [Value.depthL, maxOf]

theorem Attr.depthL_eq (as : List Attr) : Attr.depthL as = maxOf Attr.depth as := by
  induction as <;> simp_all [Attr.depthL, maxOf]

/-- A traversal whose entry step does not increase the measure does not increase the
    list's maximum. -/
theorem traverse_maxOf_le {α β : Type} {f : α → Option β} {mα : α → Nat} {mβ : β → Nat}
    (h : ∀ x y, f x = some y → mβ y ≤ mα x) :
    ∀ (xs : List α) (ys : List β), traverse f xs = some ys → maxOf mβ ys ≤ maxOf mα xs
  | [], ys, htr => by cases (by simpa using htr : [] = ys); simp [maxOf]
  | x :: xs, ys, htr => by
      rw [traverse_cons] at htr
      obtain ⟨y, hy, hrest⟩ := Option.bind_eq_some_iff.mp htr
      obtain ⟨ys', hys', rfl⟩ := Option.map_eq_some_iff.mp hrest
      have := h x y hy
      have := traverse_maxOf_le h xs ys' hys'
      simp only [maxOf]; omega

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
    simp [hw]

/-- §3 `(opaque)`, write side at kind `set`: the wire member is computed from the elements (`setCodec`), which is why one option covers `SS`, `NS` and `BS`. -/
theorem opaqCodec_e_strSet (lossy : Bool) (n : Nat) (S : NEFinset String) :
    (opaqCodec (n+1) lossy).e (.strSet S)
      = (setCodec (opaqCodec n lossy)).e (.strSet S) := by
  cases he : (setCodec (opaqCodec n lossy)).e (.strSet S) <;>
    cases lossy <;> simp [-setCodec, he]

theorem opaqCodec_e_numSet (lossy : Bool) (n : Nat) (S : NEFinset Double) :
    (opaqCodec (n+1) lossy).e (.numSet S)
      = (setCodec (opaqCodec n lossy)).e (.numSet S) := by
  cases he : (setCodec (opaqCodec n lossy)).e (.numSet S) <;>
    cases lossy <;> simp [-setCodec, he]

theorem opaqCodec_e_binSet (lossy : Bool) (n : Nat) (S : NEFinset Bytes) :
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
theorem opaqCodec_e_map (lossy : Bool) (n : Nat) (keys : Finset Name)
    (f : {k // k ∈ keys} → Value) :
    (opaqCodec (n+1) lossy).e (.map keys f)
      = (recordCodec (opaqCodec n lossy)).e (.map keys f) := by
  cases he : (recordCodec (opaqCodec n lossy)).e (.map keys f) <;>
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
  -- The map case takes no list companion: the entries are indexed by the key set, so
  -- pointwise agreement *is* equality of the two entry functions, and `funImage` — which
  -- is the whole of `recordCodec`'s write side — is applied to one function, not two.
  | .map keys f, n'+1, m'+1, hn, hm => by
      have hn' : ∀ k, Value.depth (f k) <= n' := fun k => by
        have := Value.depth_map_entry (f := f) k; omega
      have hm' : ∀ k, Value.depth (f k) <= m' := fun k => by
        have := Value.depth_map_entry (f := f) k; omega
      rw [opaqCodec_e_map, opaqCodec_e_map]
      show (funImage (fun k => (opaqCodec n' lossy).e (f k))).map (Attr.m keys)
         = (funImage (fun k => (opaqCodec m' lossy).e (f k))).map (Attr.m keys)
      rw [funext fun k => opaq_e_agree lossy (f k) n' m' (hn' k) (hm' k)]
termination_by v n => (n, sizeOf v)

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
termination_by vs n => (n, sizeOf vs)

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

/-- The `M` option does not admit an `N`, said as an unfolding rather than left to `simp`.
    `recordCodec`'s `M` branch is a `funImage`, and a `funImage` is a `Classical` `dif`;
    unfolding `recordCodec` inside the number case's four-way split sends `whnf` chasing
    that instance. Naming the answer — which is `rfl` — keeps the cost at nothing. -/
private theorem recordCodec_p_n {c : Codec} (x : WFNumeral) :
    (recordCodec c).p (.n x) = none := rfl

theorem opaqCodec_p_n (lossy : Bool) (n : Nat) (x : WFNumeral) :
    (opaqCodec (n+1) lossy).p (.n x)
      = (if lossy then numberCodec else Codec.empty).p (.n x) := by
  cases hd : Double.ofDec x with
  | none => cases lossy <;> simp [hd]
  | some d =>
    by_cases hw : Numeral.WF d.toDec = true <;> cases lossy <;>
      simp [-recordCodec, recordCodec_p_n, hd, hw]

/-- §3 `(opaque)`, read side at member `SS` — one of the three members routing to the single `set` option, which is the ten-versus-eight asymmetry in the header. -/
theorem opaqCodec_p_ss (lossy : Bool) (n : Nat) (vs : NEFinset String) :
    (opaqCodec (n+1) lossy).p (.ss vs) = (setCodec (opaqCodec n lossy)).p (.ss vs) := by
  cases hp : (setCodec (opaqCodec n lossy)).p (.ss vs) <;>
    cases lossy <;> simp [-setCodec, hp]

/-- §3 `(opaque)`, read side at member `NS`. -/
theorem opaqCodec_p_ns (lossy : Bool) (n : Nat) (vs : NEFinset WFNumeral) :
    (opaqCodec (n+1) lossy).p (.ns vs) = (setCodec (opaqCodec n lossy)).p (.ns vs) := by
  cases hp : (setCodec (opaqCodec n lossy)).p (.ns vs) <;>
    cases lossy <;> simp [-setCodec, hp]

/-- §3 `(opaque)`, read side at member `BS`. -/
theorem opaqCodec_p_bs (lossy : Bool) (n : Nat) (vs : NEFinset Bytes) :
    (opaqCodec (n+1) lossy).p (.bs vs) = (setCodec (opaqCodec n lossy)).p (.bs vs) := by
  cases hp : (setCodec (opaqCodec n lossy)).p (.bs vs) <;>
    cases lossy <;> simp [-setCodec, hp]

/-- §3 `(opaque)`, read side at member `L`. -/
theorem opaqCodec_p_l (lossy : Bool) (n : Nat) (as : List Attr) :
    (opaqCodec (n+1) lossy).p (.l as) = (arrayCodec (opaqCodec n lossy)).p (.l as) := by
  cases hp : (arrayCodec (opaqCodec n lossy)).p (.l as) <;>
    cases lossy <;> simp [-arrayCodec, hp]

/-- §3 `(opaque)`, read side at member `M`. -/
theorem opaqCodec_p_m (lossy : Bool) (n : Nat) (keys : Finset Name)
    (g : {k // k ∈ keys} → Attr) :
    (opaqCodec (n+1) lossy).p (.m keys g)
      = (recordCodec (opaqCodec n lossy)).p (.m keys g) := by
  cases hp : (recordCodec (opaqCodec n lossy)).p (.m keys g) <;>
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

theorem opaq_p_n_agree (lossy : Bool) (x : WFNumeral) :
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
      simp only [setCodec, decSet,
        show ∀ x : String, (opaqCodec n' lossy).p (Attr.s x)
             = (opaqCodec m' lossy).p (Attr.s x) from
          fun x => opaq_p_s_agree lossy x n' m' hn' hm']
  | .ns vs, n'+1, m'+1, hn, hm => by
      have hn' : 1 <= n' := by simp only [Attr.depth] at hn; omega
      have hm' : 1 <= m' := by simp only [Attr.depth] at hm; omega
      rw [opaqCodec_p_ns, opaqCodec_p_ns]
      simp only [setCodec, decSet,
        show ∀ x : WFNumeral, (opaqCodec n' lossy).p (Attr.n x)
             = (opaqCodec m' lossy).p (Attr.n x) from
          fun x => opaq_p_n_agree lossy x n' m' hn' hm']
  | .bs vs, n'+1, m'+1, hn, hm => by
      have hn' : 1 <= n' := by simp only [Attr.depth] at hn; omega
      have hm' : 1 <= m' := by simp only [Attr.depth] at hm; omega
      rw [opaqCodec_p_bs, opaqCodec_p_bs]
      simp only [setCodec, decSet,
        show ∀ x : Bytes, (opaqCodec n' lossy).p (Attr.b x)
             = (opaqCodec m' lossy).p (Attr.b x) from
          fun x => opaq_p_b_agree lossy x n' m' hn' hm']
  | .l as, n'+1, m'+1, hn, hm => by
      have hn' : Attr.depthL as <= n' := by simp only [Attr.depth] at hn; omega
      have hm' : Attr.depthL as <= m' := by simp only [Attr.depth] at hm; omega
      rw [opaqCodec_p_l, opaqCodec_p_l]
      show (traverse (opaqCodec n' lossy).p as).map Value.arr
         = (traverse (opaqCodec m' lossy).p as).map Value.arr
      rw [opaq_p_agreeL lossy as n' m' hn' hm']
  | .m keys g, n'+1, m'+1, hn, hm => by
      have hn' : ∀ k, Attr.depth (g k) <= n' := fun k => by
        have := Attr.depth_map_entry (f := g) k; omega
      have hm' : ∀ k, Attr.depth (g k) <= m' := fun k => by
        have := Attr.depth_map_entry (f := g) k; omega
      rw [opaqCodec_p_m, opaqCodec_p_m]
      show (funImage (fun k => (opaqCodec n' lossy).p (g k))).map (Value.map keys)
         = (funImage (fun k => (opaqCodec m' lossy).p (g k))).map (Value.map keys)
      rw [funext fun k => opaq_p_agree lossy (g k) n' m' (hn' k) (hm' k)]

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

end

/-! ## Depth preservation

`opaqCodecω` below picks its write-side fuel from the value and its read-side fuel from
the attribute, so the two budgets never coincide and `retract`/`canon` have to transport
between them. The lemmas here are what licenses the transport: encoding never deepens,
and neither does decoding. -/

/-- A wire set is always exactly one layer of payloads, whichever family it lands in. -/
theorem encSet_depth {α : Type} {c : Codec} {vinj : α → Value} {S : NEFinset α} {a : Attr}
    (h : encSet c vinj S = some a) : Attr.depth a = 2 := by
  unfold encSet at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · obtain ⟨T, -, hT⟩ := Option.map_eq_some_iff.mp h
      cases hT; rfl

/-- …and a value set likewise: its elements are scalars. -/
theorem decSet_depth {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α} {v : Value}
    (h : decSet c inj S = some v) : Value.depth v = 2 := by
  unfold decSet at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · obtain ⟨T, -, hT⟩ := Option.map_eq_some_iff.mp h
      cases hT; rfl

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
        · rw [dif_pos hw] at he; cases he; simp [Attr.depth, Value.depth]
        · rw [dif_neg hw] at he; exact nomatch he
  | .strSet S, n'+1, a, he => by
      rw [opaqCodec_e_strSet] at he
      rw [encSet_depth (c := opaqCodec n' lossy) (vinj := Value.str) he]
      simp [Value.depth]
  | .numSet S, n'+1, a, he => by
      rw [opaqCodec_e_numSet] at he
      rw [encSet_depth (c := opaqCodec n' lossy) (vinj := Value.num) he]
      simp [Value.depth]
  | .binSet S, n'+1, a, he => by
      rw [opaqCodec_e_binSet] at he
      rw [encSet_depth (c := opaqCodec n' lossy) (vinj := Value.bin) he]
      simp [Value.depth]
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
  -- `M` keeps the key set, so the two sups run over the same index and the bound is
  -- entrywise. `funImage` hands the entry hypothesis over directly (`funImage_some`).
  | .map keys f, n'+1, a, he => by
      rw [opaqCodec_e_map] at he
      replace he :
          (funImage (fun k => (opaqCodec n' lossy).e (f k))).map (Attr.m keys) = some a := he
      cases hfi : funImage (fun k => (opaqCodec n' lossy).e (f k)) with
      | none => rw [hfi] at he; exact nomatch he
      | some g =>
        rw [hfi] at he
        replace he : Attr.m keys g = a := by simpa using he
        subst he
        refine Attr.depth_m_le fun k => ?_
        exact le_trans (opaq_e_depth lossy (f k) n' (g k) (funImage_some hfi k))
          (Finset.le_sup (f := fun k => Value.depth (f k)) (Finset.mem_attach _ k))
termination_by _ n => (n, 0)

theorem opaq_e_depthL (lossy : Bool) :
    ∀ (vs : List Value) (n : Nat) (as : List Attr),
      traverse (opaqCodec n lossy).e vs = some as ->
      Attr.depthL as <= Value.depthL vs
  | vs, n, as, htr => by
      rw [Attr.depthL_eq, Value.depthL_eq]
      exact traverse_maxOf_le (fun v a hv => opaq_e_depth lossy v n a hv) vs as htr
termination_by _ n => (n, 1)

end

/-! ### Read-side depth preservation

The one case that is not a leaf `simp` is `N`, where reading goes through `Double.ofDec`
and the write-back gate. The wire sets need no list lemma of their own: `decSet` fixes
their depth at 2 outright (`opaq_p_wire_depth`), where the list representation they
replaced had to be traversed three times. -/

theorem opaq_p_n_depth (lossy : Bool) (x : WFNumeral) :
    ∀ (n : Nat) (v : Value), (opaqCodec n lossy).p (.n x) = some v -> Value.depth v <= 1
  | n, v, hp => by
      cases n with | zero => exact nomatch hp | succ n' =>
      rw [opaqCodec_p_n] at hp
      cases lossy with
      | false => simp [Codec.empty] at hp
      | true =>
        replace hp : numberCodec.p (.n x) = some v := hp
        rw [numberCodec_p_n] at hp
        cases hd : Double.ofDec x.1 with
        | none => rw [hd] at hp; exact nomatch hp
        | some d =>
          rw [hd] at hp
          replace hp : (if Numeral.WF d.toDec then some (Value.num d) else none) = some v := hp
          by_cases hw : Numeral.WF d.toDec = true
          · rw [if_pos hw] at hp; cases hp; simp [Value.depth]
          · rw [if_neg hw] at hp; exact nomatch hp

/-- …and the wire set itself is exactly one level above its leaves. `decSet` produces one
    of the three value-set constructors, and those hold scalars. -/
theorem opaq_p_wire_depth {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α} {v : Value}
    (hp : decSet c inj S = some v) : Value.depth v <= 2 := le_of_eq (decSet_depth hp)

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
      have := opaq_p_wire_depth (c := opaqCodec n' lossy) (inj := Attr.s) hp
      simp only [Attr.depth]; omega
  | .ns xs, n'+1, v, hp => by
      rw [opaqCodec_p_ns] at hp
      have := opaq_p_wire_depth (c := opaqCodec n' lossy) (inj := Attr.n) hp
      simp only [Attr.depth]; omega
  | .bs bs, n'+1, v, hp => by
      rw [opaqCodec_p_bs] at hp
      have := opaq_p_wire_depth (c := opaqCodec n' lossy) (inj := Attr.b) hp
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
  | .m keys g, n'+1, v, hp => by
      rw [opaqCodec_p_m] at hp
      replace hp :
          (funImage (fun k => (opaqCodec n' lossy).p (g k))).map (Value.map keys) = some v := hp
      cases hfi : funImage (fun k => (opaqCodec n' lossy).p (g k)) with
      | none => rw [hfi] at hp; exact nomatch hp
      | some f =>
        rw [hfi] at hp
        replace hp : Value.map keys f = v := by simpa using hp
        subst hp
        refine Value.depth_map_le fun k => ?_
        exact le_trans (opaq_p_depth lossy (g k) n' (f k) (funImage_some hfi k))
          (Finset.le_sup (f := fun k => Attr.depth (g k)) (Finset.mem_attach _ k))
termination_by _ n => (n, 0)

theorem opaq_p_depthL (lossy : Bool) :
    ∀ (as : List Attr) (n : Nat) (vs : List Value),
      traverse (opaqCodec n lossy).p as = some vs ->
      Value.depthL vs <= Attr.depthL as
  | as, n, vs, htr => by
      rw [Value.depthL_eq, Attr.depthL_eq]
      exact traverse_maxOf_le (fun a v ha => opaq_p_depth lossy a n v ha) as vs htr
termination_by _ n => (n, 1)

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
