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

Structure:

* `Value.depth` / `Attr.depth` — structural budgets.
* `traverse_congr` — the missing congruence: pointwise-equal functions traverse equally.
* `opaqCodec_e_*` / `opaqCodec_p_*` — the eight unfoldings, one per kind. Each collapses
  `altCodec`'s filter to a single option by kind-disjointness, and is where the "at most
  one admits" argument is actually cashed.
-/

namespace Calculus

/-! ## Depth -/

mutual

/-- Fuel sufficient for `opaqCodec` to see all of `v`: leaves need `1`, each container
    layer one more. -/
def Value.depth : Value → Nat
  | .str _ | .num _ | .bool _ | .bin _ | .null => 1
  | .set vs => Value.depthL vs + 1
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
  cases v <;> simp [Value.depth] <;> omega

theorem Attr.depth_pos (a : Attr) : 0 < Attr.depth a := by
  cases a <;> simp [Attr.depth] <;> omega

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

/-! ## The eight unfoldings

Each says: at this value's kind, `altCodec`'s filter collapses to exactly one option, so
the union's answer *is* that option's. This is kind-disjointness cashed — the property
`union` in general does not have, and the reason `opaque` escapes `Continuity.lean`.

Stated against the option's own codec rather than its literal encoding, so they stay
true if a primitive's shape changes. -/

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

theorem opaqCodec_e_str (lossy : Bool) (n : Nat) (s : String) :
    (opaqCodec (n+1) lossy).e (.str s) = stringCodec.e (.str s) := by
  cases lossy <;>
    simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
          binaryCodec, nullCodec, numberCodec, setCodec, arrayCodec, recordCodec,
          Codec.empty]

theorem opaqCodec_e_bool (lossy : Bool) (n : Nat) (b : Bool) :
    (opaqCodec (n+1) lossy).e (.bool b) = booleanCodec.e (.bool b) := by
  cases lossy <;>
    simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
          binaryCodec, nullCodec, numberCodec, setCodec, arrayCodec, recordCodec,
          Codec.empty]

theorem opaqCodec_e_bin (lossy : Bool) (n : Nat) (b : Bytes) :
    (opaqCodec (n+1) lossy).e (.bin b) = binaryCodec.e (.bin b) := by
  cases lossy <;>
    simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
          binaryCodec, nullCodec, numberCodec, setCodec, arrayCodec, recordCodec,
          Codec.empty]

theorem opaqCodec_e_null (lossy : Bool) (n : Nat) :
    (opaqCodec (n+1) lossy).e .null = nullCodec.e .null := by
  cases lossy <;>
    simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
          binaryCodec, nullCodec, numberCodec, setCodec, arrayCodec, recordCodec,
          Codec.empty]

theorem opaqCodec_e_num (lossy : Bool) (n : Nat) (d : Double) :
    (opaqCodec (n+1) lossy).e (.num d)
      = (if lossy then numberCodec else Codec.empty).e (.num d) := by
  cases lossy <;>
    simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
          binaryCodec, nullCodec, numberCodec, setCodec, arrayCodec, recordCodec,
          Codec.empty]

theorem opaqCodec_e_set (lossy : Bool) (n : Nat) (vs : List Value) :
    (opaqCodec (n+1) lossy).e (.set vs)
      = (setCodec (opaqCodec n lossy)).e (.set vs) := by
  cases he : (setCodec (opaqCodec n lossy)).e (.set vs) <;>
    cases lossy <;>
      simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
            binaryCodec, nullCodec, numberCodec, arrayCodec, recordCodec,
            Codec.empty, he]

theorem opaqCodec_e_arr (lossy : Bool) (n : Nat) (vs : List Value) :
    (opaqCodec (n+1) lossy).e (.arr vs)
      = (arrayCodec (opaqCodec n lossy)).e (.arr vs) := by
  cases he : (arrayCodec (opaqCodec n lossy)).e (.arr vs) <;>
    cases lossy <;>
      simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
            binaryCodec, nullCodec, numberCodec, setCodec, recordCodec,
            Codec.empty, he]

theorem opaqCodec_e_map (lossy : Bool) (n : Nat) (kvs : List (Name × Value)) :
    (opaqCodec (n+1) lossy).e (.map kvs)
      = (recordCodec (opaqCodec n lossy)).e (.map kvs) := by
  cases he : (recordCodec (opaqCodec n lossy)).e (.map kvs) <;>
    cases lossy <;>
      simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
            binaryCodec, nullCodec, numberCodec, setCodec, arrayCodec,
            Codec.empty, he]

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
  | .str _, n, m, hn, hm => by
      cases n with | zero => simp [Value.depth] at hn | succ n' =>
      cases m with | zero => simp [Value.depth] at hm | succ m' =>
      rw [opaqCodec_e_str, opaqCodec_e_str]
  | .bool _, n, m, hn, hm => by
      cases n with | zero => simp [Value.depth] at hn | succ n' =>
      cases m with | zero => simp [Value.depth] at hm | succ m' =>
      rw [opaqCodec_e_bool, opaqCodec_e_bool]
  | .bin _, n, m, hn, hm => by
      cases n with | zero => simp [Value.depth] at hn | succ n' =>
      cases m with | zero => simp [Value.depth] at hm | succ m' =>
      rw [opaqCodec_e_bin, opaqCodec_e_bin]
  | .null, n, m, hn, hm => by
      cases n with | zero => simp [Value.depth] at hn | succ n' =>
      cases m with | zero => simp [Value.depth] at hm | succ m' =>
      rw [opaqCodec_e_null, opaqCodec_e_null]
  | .num _, n, m, hn, hm => by
      cases n with | zero => simp [Value.depth] at hn | succ n' =>
      cases m with | zero => simp [Value.depth] at hm | succ m' =>
      rw [opaqCodec_e_num, opaqCodec_e_num]
  | .set vs, n, m, hn, hm => by
      cases n with | zero => simp [Value.depth] at hn | succ n' =>
      cases m with | zero => simp [Value.depth] at hm | succ m' =>
      have hn' : Value.depthL vs <= n' := by simp only [Value.depth] at hn; omega
      have hm' : Value.depthL vs <= m' := by simp only [Value.depth] at hm; omega
      rw [opaqCodec_e_set, opaqCodec_e_set]
      show (traverse (opaqCodec n' lossy).e vs).bind asWireSet
         = (traverse (opaqCodec m' lossy).e vs).bind asWireSet
      rw [opaq_e_agreeL lossy vs n' m' hn' hm']
  | .arr vs, n, m, hn, hm => by
      cases n with | zero => simp [Value.depth] at hn | succ n' =>
      cases m with | zero => simp [Value.depth] at hm | succ m' =>
      have hn' : Value.depthL vs <= n' := by simp only [Value.depth] at hn; omega
      have hm' : Value.depthL vs <= m' := by simp only [Value.depth] at hm; omega
      rw [opaqCodec_e_arr, opaqCodec_e_arr]
      show (traverse (opaqCodec n' lossy).e vs).map Attr.l
         = (traverse (opaqCodec m' lossy).e vs).map Attr.l
      rw [opaq_e_agreeL lossy vs n' m' hn' hm']
  | .map kvs, n, m, hn, hm => by
      cases n with | zero => simp [Value.depth] at hn | succ n' =>
      cases m with | zero => simp [Value.depth] at hm | succ m' =>
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

theorem opaqCodec_p_s (lossy : Bool) (n : Nat) (s : String) :
    (opaqCodec (n+1) lossy).p (.s s) = stringCodec.p (.s s) := by
  cases lossy <;>
    simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
          binaryCodec, nullCodec, numberCodec, setCodec, arrayCodec, recordCodec,
          Codec.empty]

theorem opaqCodec_p_bool (lossy : Bool) (n : Nat) (b : Bool) :
    (opaqCodec (n+1) lossy).p (.bool b) = booleanCodec.p (.bool b) := by
  cases lossy <;>
    simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
          binaryCodec, nullCodec, numberCodec, setCodec, arrayCodec, recordCodec,
          Codec.empty]

theorem opaqCodec_p_b (lossy : Bool) (n : Nat) (b : Bytes) :
    (opaqCodec (n+1) lossy).p (.b b) = binaryCodec.p (.b b) := by
  cases lossy <;>
    simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
          binaryCodec, nullCodec, numberCodec, setCodec, arrayCodec, recordCodec,
          Codec.empty]

theorem opaqCodec_p_null (lossy : Bool) (n : Nat) :
    (opaqCodec (n+1) lossy).p .null = nullCodec.p .null := by
  cases lossy <;>
    simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
          binaryCodec, nullCodec, numberCodec, setCodec, arrayCodec, recordCodec,
          Codec.empty]

theorem opaqCodec_p_n (lossy : Bool) (n : Nat) (x : Numeral) :
    (opaqCodec (n+1) lossy).p (.n x)
      = (if lossy then numberCodec else Codec.empty).p (.n x) := by
  cases hd : Double.ofDec x <;>
    cases lossy <;>
      simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
            binaryCodec, nullCodec, numberCodec, setCodec, arrayCodec, recordCodec,
            Codec.empty, hd]

theorem opaqCodec_p_ss (lossy : Bool) (n : Nat) (vs : List String) :
    (opaqCodec (n+1) lossy).p (.ss vs) = (setCodec (opaqCodec n lossy)).p (.ss vs) := by
  cases hp : (setCodec (opaqCodec n lossy)).p (.ss vs) <;>
    cases lossy <;>
      simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
            binaryCodec, nullCodec, numberCodec, arrayCodec, recordCodec,
            Codec.empty, hp]

theorem opaqCodec_p_ns (lossy : Bool) (n : Nat) (vs : List Numeral) :
    (opaqCodec (n+1) lossy).p (.ns vs) = (setCodec (opaqCodec n lossy)).p (.ns vs) := by
  cases hp : (setCodec (opaqCodec n lossy)).p (.ns vs) <;>
    cases lossy <;>
      simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
            binaryCodec, nullCodec, numberCodec, arrayCodec, recordCodec,
            Codec.empty, hp]

theorem opaqCodec_p_bs (lossy : Bool) (n : Nat) (vs : List Bytes) :
    (opaqCodec (n+1) lossy).p (.bs vs) = (setCodec (opaqCodec n lossy)).p (.bs vs) := by
  cases hp : (setCodec (opaqCodec n lossy)).p (.bs vs) <;>
    cases lossy <;>
      simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
            binaryCodec, nullCodec, numberCodec, arrayCodec, recordCodec,
            Codec.empty, hp]

theorem opaqCodec_p_l (lossy : Bool) (n : Nat) (as : List Attr) :
    (opaqCodec (n+1) lossy).p (.l as) = (arrayCodec (opaqCodec n lossy)).p (.l as) := by
  cases hp : (arrayCodec (opaqCodec n lossy)).p (.l as) <;>
    cases lossy <;>
      simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
            binaryCodec, nullCodec, numberCodec, setCodec, recordCodec,
            Codec.empty, hp]

theorem opaqCodec_p_m (lossy : Bool) (n : Nat) (kvs : List (Name × Attr)) :
    (opaqCodec (n+1) lossy).p (.m kvs) = (recordCodec (opaqCodec n lossy)).p (.m kvs) := by
  cases hp : (recordCodec (opaqCodec n lossy)).p (.m kvs) <;>
    cases lossy <;>
      simp [opaq_unfold, altCodec, OptionSem.byAttempt, stringCodec, booleanCodec,
            binaryCodec, nullCodec, numberCodec, setCodec, arrayCodec,
            Codec.empty, hp]

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
  | .s _, n, m, hn, hm => by
      cases n with | zero => simp [Attr.depth] at hn | succ n' =>
      cases m with | zero => simp [Attr.depth] at hm | succ m' =>
      rw [opaqCodec_p_s, opaqCodec_p_s]
  | .bool _, n, m, hn, hm => by
      cases n with | zero => simp [Attr.depth] at hn | succ n' =>
      cases m with | zero => simp [Attr.depth] at hm | succ m' =>
      rw [opaqCodec_p_bool, opaqCodec_p_bool]
  | .b _, n, m, hn, hm => by
      cases n with | zero => simp [Attr.depth] at hn | succ n' =>
      cases m with | zero => simp [Attr.depth] at hm | succ m' =>
      rw [opaqCodec_p_b, opaqCodec_p_b]
  | .null, n, m, hn, hm => by
      cases n with | zero => simp [Attr.depth] at hn | succ n' =>
      cases m with | zero => simp [Attr.depth] at hm | succ m' =>
      rw [opaqCodec_p_null, opaqCodec_p_null]
  | .n _, n, m, hn, hm => by
      cases n with | zero => simp [Attr.depth] at hn | succ n' =>
      cases m with | zero => simp [Attr.depth] at hm | succ m' =>
      rw [opaqCodec_p_n, opaqCodec_p_n]
  | .ss vs, n, m, hn, hm => by
      cases n with | zero => simp [Attr.depth] at hn | succ n' =>
      cases m with | zero => simp [Attr.depth] at hm | succ m' =>
      have hn' : 1 <= n' := by simp only [Attr.depth] at hn; omega
      have hm' : 1 <= m' := by simp only [Attr.depth] at hm; omega
      rw [opaqCodec_p_ss, opaqCodec_p_ss]
      show (if vs.isEmpty then none
            else (traverse (fun s => (opaqCodec n' lossy).p (.s s)) vs).map Value.set)
         = (if vs.isEmpty then none
            else (traverse (fun s => (opaqCodec m' lossy).p (.s s)) vs).map Value.set)
      rw [traverse_congr vs (fun s _ => opaq_p_s_agree lossy s n' m' hn' hm')]
  | .ns vs, n, m, hn, hm => by
      cases n with | zero => simp [Attr.depth] at hn | succ n' =>
      cases m with | zero => simp [Attr.depth] at hm | succ m' =>
      have hn' : 1 <= n' := by simp only [Attr.depth] at hn; omega
      have hm' : 1 <= m' := by simp only [Attr.depth] at hm; omega
      rw [opaqCodec_p_ns, opaqCodec_p_ns]
      show (if vs.isEmpty then none
            else (traverse (fun x => (opaqCodec n' lossy).p (.n x)) vs).map Value.set)
         = (if vs.isEmpty then none
            else (traverse (fun x => (opaqCodec m' lossy).p (.n x)) vs).map Value.set)
      rw [traverse_congr vs (fun x _ => opaq_p_n_agree lossy x n' m' hn' hm')]
  | .bs vs, n, m, hn, hm => by
      cases n with | zero => simp [Attr.depth] at hn | succ n' =>
      cases m with | zero => simp [Attr.depth] at hm | succ m' =>
      have hn' : 1 <= n' := by simp only [Attr.depth] at hn; omega
      have hm' : 1 <= m' := by simp only [Attr.depth] at hm; omega
      rw [opaqCodec_p_bs, opaqCodec_p_bs]
      show (if vs.isEmpty then none
            else (traverse (fun b => (opaqCodec n' lossy).p (.b b)) vs).map Value.set)
         = (if vs.isEmpty then none
            else (traverse (fun b => (opaqCodec m' lossy).p (.b b)) vs).map Value.set)
      rw [traverse_congr vs (fun b _ => opaq_p_b_agree lossy b n' m' hn' hm')]
  | .l as, n, m, hn, hm => by
      cases n with | zero => simp [Attr.depth] at hn | succ n' =>
      cases m with | zero => simp [Attr.depth] at hm | succ m' =>
      have hn' : Attr.depthL as <= n' := by simp only [Attr.depth] at hn; omega
      have hm' : Attr.depthL as <= m' := by simp only [Attr.depth] at hm; omega
      rw [opaqCodec_p_l, opaqCodec_p_l]
      show (traverse (opaqCodec n' lossy).p as).map Value.arr
         = (traverse (opaqCodec m' lossy).p as).map Value.arr
      rw [opaq_p_agreeL lossy as n' m' hn' hm']
  | .m kvs, n, m, hn, hm => by
      cases n with | zero => simp [Attr.depth] at hn | succ n' =>
      cases m with | zero => simp [Attr.depth] at hm | succ m' =>
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
  | .str _, n, a, he => by
      cases n with | zero => exact nomatch he | succ n' =>
      rw [opaqCodec_e_str] at he
      simp only [stringCodec] at he; cases he; simp [Attr.depth, Value.depth]
  | .bool _, n, a, he => by
      cases n with | zero => exact nomatch he | succ n' =>
      rw [opaqCodec_e_bool] at he
      simp only [booleanCodec] at he; cases he; simp [Attr.depth, Value.depth]
  | .bin _, n, a, he => by
      cases n with | zero => exact nomatch he | succ n' =>
      rw [opaqCodec_e_bin] at he
      simp only [binaryCodec] at he; cases he; simp [Attr.depth, Value.depth]
  | .null, n, a, he => by
      cases n with | zero => exact nomatch he | succ n' =>
      rw [opaqCodec_e_null] at he
      simp only [nullCodec] at he; cases he; simp [Attr.depth, Value.depth]
  | .num _, n, a, he => by
      cases n with | zero => exact nomatch he | succ n' =>
      rw [opaqCodec_e_num] at he
      cases lossy <;> simp only [numberCodec, Codec.empty] at he
      · exact nomatch he
      · cases he; simp [Attr.depth, Value.depth]
  | .set vs, n, a, he => by
      cases n with | zero => exact nomatch he | succ n' =>
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
  | .arr vs, n, a, he => by
      cases n with | zero => exact nomatch he | succ n' =>
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
  | .map kvs, n, a, he => by
      cases n with | zero => exact nomatch he | succ n' =>
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
  | [], _, as, htr => by
      replace htr : some [] = some as := htr
      cases htr; simp [Attr.depthL, Value.depthL]
  | v :: vs, n, as, htr => by
      simp only [traverse] at htr
      cases hv : (opaqCodec n lossy).e v with
      | none => rw [hv] at htr; exact nomatch htr
      | some a =>
        rw [hv] at htr
        cases hvs : traverse (opaqCodec n lossy).e vs with
        | none => rw [hvs] at htr; exact nomatch htr
        | some as' =>
          rw [hvs] at htr
          replace htr : some (a :: as') = some as := htr
          cases htr
          have h1 := opaq_e_depth lossy v n a hv
          have h2 := opaq_e_depthL lossy vs n as' hvs
          simp only [Attr.depthL, Value.depthL]
          omega

theorem opaq_e_depthP (lossy : Bool) :
    ∀ (kvs : List (Name × Value)) (n : Nat) (kas : List (Name × Attr)),
      traverse (encPair (opaqCodec n lossy)) kvs = some kas ->
      Attr.depthP kas <= Value.depthP kvs
  | [], _, kas, htr => by
      replace htr : some [] = some kas := htr
      cases htr; simp [Attr.depthP, Value.depthP]
  | kv :: kvs, n, kas, htr => by
      simp only [traverse] at htr
      cases hea : (opaqCodec n lossy).e kv.2 with
      | none =>
        have hnone : encPair (opaqCodec n lossy) kv = none := by simp [encPair, hea]
        rw [hnone] at htr; exact nomatch htr
      | some a =>
        have hka : encPair (opaqCodec n lossy) kv = some (kv.1, a) := by
          simp [encPair, hea]
        rw [hka] at htr
        cases hvs : traverse (encPair (opaqCodec n lossy)) kvs with
        | none => rw [hvs] at htr; exact nomatch htr
        | some kas' =>
          rw [hvs] at htr
          replace htr : some ((kv.1, a) :: kas') = some kas := htr
          cases htr
          have h1 := opaq_e_depth lossy kv.2 n a hea
          have h2 := opaq_e_depthP lossy kvs n kas' hvs
          simp only [Attr.depthP, Value.depthP]
          omega

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
        replace hp : (Double.ofDec x).map Value.num = some v := by
          simpa [numberCodec] using hp
        cases hd : Double.ofDec x with
        | none => rw [hd] at hp; exact nomatch hp
        | some d =>
          rw [hd] at hp
          replace hp : Value.num d = v := by simpa using hp
          subst hp; simp [Value.depth]

theorem opaq_p_b_depth (lossy : Bool) (b : Bytes) :
    ∀ (n : Nat) (v : Value), (opaqCodec n lossy).p (.b b) = some v -> Value.depth v <= 1
  | n, v, hp => by
      cases n with | zero => exact nomatch hp | succ n' =>
      rw [opaqCodec_p_b] at hp
      simp only [binaryCodec] at hp; cases hp; simp [Value.depth]

theorem opaq_p_ssL (lossy : Bool) (n : Nat) :
    ∀ (ss : List String) (vs : List Value),
      traverse (fun s => (opaqCodec n lossy).p (.s s)) ss = some vs ->
      Value.depthL vs <= 1
  | [], vs, htr => by
      replace htr : some [] = some vs := htr
      cases htr; simp [Value.depthL]
  | s :: ss, vs, htr => by
      simp only [traverse] at htr
      cases hs : (opaqCodec n lossy).p (.s s) with
      | none => rw [hs] at htr; exact nomatch htr
      | some v =>
        rw [hs] at htr
        cases hss : traverse (fun s => (opaqCodec n lossy).p (.s s)) ss with
        | none => rw [hss] at htr; exact nomatch htr
        | some vs' =>
          rw [hss] at htr
          replace htr : some (v :: vs') = some vs := htr
          cases htr
          have h1 := opaq_p_s_depth lossy s n v hs
          have h2 := opaq_p_ssL lossy n ss vs' hss
          simp only [Value.depthL]; omega

theorem opaq_p_nsL (lossy : Bool) (n : Nat) :
    ∀ (xs : List Numeral) (vs : List Value),
      traverse (fun x => (opaqCodec n lossy).p (.n x)) xs = some vs ->
      Value.depthL vs <= 1
  | [], vs, htr => by
      replace htr : some [] = some vs := htr
      cases htr; simp [Value.depthL]
  | x :: xs, vs, htr => by
      simp only [traverse] at htr
      cases hx : (opaqCodec n lossy).p (.n x) with
      | none => rw [hx] at htr; exact nomatch htr
      | some v =>
        rw [hx] at htr
        cases hxs : traverse (fun x => (opaqCodec n lossy).p (.n x)) xs with
        | none => rw [hxs] at htr; exact nomatch htr
        | some vs' =>
          rw [hxs] at htr
          replace htr : some (v :: vs') = some vs := htr
          cases htr
          have h1 := opaq_p_n_depth lossy x n v hx
          have h2 := opaq_p_nsL lossy n xs vs' hxs
          simp only [Value.depthL]; omega

theorem opaq_p_bsL (lossy : Bool) (n : Nat) :
    ∀ (bs : List Bytes) (vs : List Value),
      traverse (fun b => (opaqCodec n lossy).p (.b b)) bs = some vs ->
      Value.depthL vs <= 1
  | [], vs, htr => by
      replace htr : some [] = some vs := htr
      cases htr; simp [Value.depthL]
  | b :: bs, vs, htr => by
      simp only [traverse] at htr
      cases hb : (opaqCodec n lossy).p (.b b) with
      | none => rw [hb] at htr; exact nomatch htr
      | some v =>
        rw [hb] at htr
        cases hbs : traverse (fun b => (opaqCodec n lossy).p (.b b)) bs with
        | none => rw [hbs] at htr; exact nomatch htr
        | some vs' =>
          rw [hbs] at htr
          replace htr : some (v :: vs') = some vs := htr
          cases htr
          have h1 := opaq_p_b_depth lossy b n v hb
          have h2 := opaq_p_bsL lossy n bs vs' hbs
          simp only [Value.depthL]; omega

mutual

theorem opaq_p_depth (lossy : Bool) :
    ∀ (a : Attr) (n : Nat) (v : Value), (opaqCodec n lossy).p a = some v ->
      Value.depth v <= Attr.depth a
  | .s _, n, v, hp => by
      cases n with | zero => exact nomatch hp | succ n' =>
      rw [opaqCodec_p_s] at hp
      simp only [stringCodec] at hp; cases hp; simp [Attr.depth, Value.depth]
  | .bool _, n, v, hp => by
      cases n with | zero => exact nomatch hp | succ n' =>
      rw [opaqCodec_p_bool] at hp
      simp only [booleanCodec] at hp; cases hp; simp [Attr.depth, Value.depth]
  | .b _, n, v, hp => by
      cases n with | zero => exact nomatch hp | succ n' =>
      rw [opaqCodec_p_b] at hp
      simp only [binaryCodec] at hp; cases hp; simp [Attr.depth, Value.depth]
  | .null, n, v, hp => by
      cases n with | zero => exact nomatch hp | succ n' =>
      rw [opaqCodec_p_null] at hp
      simp only [nullCodec] at hp; cases hp; simp [Attr.depth, Value.depth]
  | .n x, n, v, hp => by
      have := opaq_p_n_depth lossy x n v hp
      simp only [Attr.depth]; omega
  | .ss ss, n, v, hp => by
      cases n with | zero => exact nomatch hp | succ n' =>
      rw [opaqCodec_p_ss] at hp
      replace hp : (if ss.isEmpty then none
        else (traverse (fun s => (opaqCodec n' lossy).p (.s s)) ss).map Value.set)
          = some v := hp
      split at hp
      · exact nomatch hp
      · cases htr : traverse (fun s => (opaqCodec n' lossy).p (.s s)) ss with
        | none => rw [htr] at hp; exact nomatch hp
        | some vs =>
          rw [htr] at hp
          replace hp : Value.set vs = v := by simpa using hp
          subst hp
          have := opaq_p_ssL lossy n' ss vs htr
          simp only [Attr.depth, Value.depth]; omega
  | .ns xs, n, v, hp => by
      cases n with | zero => exact nomatch hp | succ n' =>
      rw [opaqCodec_p_ns] at hp
      replace hp : (if xs.isEmpty then none
        else (traverse (fun x => (opaqCodec n' lossy).p (.n x)) xs).map Value.set)
          = some v := hp
      split at hp
      · exact nomatch hp
      · cases htr : traverse (fun x => (opaqCodec n' lossy).p (.n x)) xs with
        | none => rw [htr] at hp; exact nomatch hp
        | some vs =>
          rw [htr] at hp
          replace hp : Value.set vs = v := by simpa using hp
          subst hp
          have := opaq_p_nsL lossy n' xs vs htr
          simp only [Attr.depth, Value.depth]; omega
  | .bs bs, n, v, hp => by
      cases n with | zero => exact nomatch hp | succ n' =>
      rw [opaqCodec_p_bs] at hp
      replace hp : (if bs.isEmpty then none
        else (traverse (fun b => (opaqCodec n' lossy).p (.b b)) bs).map Value.set)
          = some v := hp
      split at hp
      · exact nomatch hp
      · cases htr : traverse (fun b => (opaqCodec n' lossy).p (.b b)) bs with
        | none => rw [htr] at hp; exact nomatch hp
        | some vs =>
          rw [htr] at hp
          replace hp : Value.set vs = v := by simpa using hp
          subst hp
          have := opaq_p_bsL lossy n' bs vs htr
          simp only [Attr.depth, Value.depth]; omega
  | .l as, n, v, hp => by
      cases n with | zero => exact nomatch hp | succ n' =>
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
  | .m kvs, n, v, hp => by
      cases n with | zero => exact nomatch hp | succ n' =>
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
  | [], _, vs, htr => by
      replace htr : some [] = some vs := htr
      cases htr; simp [Attr.depthL, Value.depthL]
  | a :: as, n, vs, htr => by
      simp only [traverse] at htr
      cases ha : (opaqCodec n lossy).p a with
      | none => rw [ha] at htr; exact nomatch htr
      | some v =>
        rw [ha] at htr
        cases has : traverse (opaqCodec n lossy).p as with
        | none => rw [has] at htr; exact nomatch htr
        | some vs' =>
          rw [has] at htr
          replace htr : some (v :: vs') = some vs := htr
          cases htr
          have h1 := opaq_p_depth lossy a n v ha
          have h2 := opaq_p_depthL lossy as n vs' has
          simp only [Attr.depthL, Value.depthL]; omega

theorem opaq_p_depthP (lossy : Bool) :
    ∀ (kvs : List (Name × Attr)) (n : Nat) (kvs' : List (Name × Value)),
      traverse (decPair (opaqCodec n lossy)) kvs = some kvs' ->
      Value.depthP kvs' <= Attr.depthP kvs
  | [], _, kvs', htr => by
      replace htr : some [] = some kvs' := htr
      cases htr; simp [Attr.depthP, Value.depthP]
  | kv :: kvs, n, kvs', htr => by
      simp only [traverse] at htr
      cases hpa : (opaqCodec n lossy).p kv.2 with
      | none =>
        have hnone : decPair (opaqCodec n lossy) kv = none := by simp [decPair, hpa]
        rw [hnone] at htr; exact nomatch htr
      | some v =>
        have hkv : decPair (opaqCodec n lossy) kv = some (kv.1, v) := by
          simp [decPair, hpa]
        rw [hkv] at htr
        cases hks : traverse (decPair (opaqCodec n lossy)) kvs with
        | none => rw [hks] at htr; exact nomatch htr
        | some kvs'' =>
          rw [hks] at htr
          replace htr : some ((kv.1, v) :: kvs'') = some kvs' := htr
          cases htr
          have h1 := opaq_p_depth lossy kv.2 n v hpa
          have h2 := opaq_p_depthP lossy kvs n kvs'' hks
          simp only [Attr.depthP, Value.depthP]; omega

end

/-! ## `opaque`, fuel-free

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
