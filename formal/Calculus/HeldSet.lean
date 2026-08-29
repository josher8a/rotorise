import Calculus.Soundnessω

/-!
# `Uν` and the empty set — a mechanization bug, and its witness

`docs/codec-formalization.md` §6 lists "`T` as an identity" as unproved, and says it
"bites hardest at `opaque`, where §3 says `Uν` *is* the held set". Attempting it turned up
a defect — but, unlike §4's three, this one was in the **model**, not the specification.

`HOpaque`'s `set` clause was transcribed as

```
| set (vs) (h : ∀ x ∈ vs, HOpaque lossy x) : HOpaque lossy (.set vs)
```

with no constraint on `vs`, so `HOpaque lossy (set [])` held vacuously. Nothing in the
calculus agrees:

* §1's `SS`/`NS`/`BS` are `℘⁺fin` — explicitly non-empty. There is no empty wire set to
  write, and `asWireSet []` refuses.
* `(set)`'s own held set `HSet` carries `vs ≠ []`. §3 exhibits `Uν` as the fixpoint
  `union(…, set(opaque), …)`, whose `set` option is that rule — so the fixpoint reading
  excludes `set []` too.
* §3's prose reading — "the values whose member is recoverable from the value alone" —
  excludes it as well, and for the sharpest reason: an empty set has no payloads, so
  `SS`, `NS` and `BS` are indistinguishable. Its member is precisely what cannot be
  recovered.

All three readings agree, and the inductive disagreed with all three. `Typing.lean` now
carries `hne : vs ≠ []`. The lemmas below are the witness for why it has to, and a
regression test: `opaqCodec` never held `set []` at any fuel, and never wrote it, so the
old `Uν` claimed a value the denotation could not represent.

The direction of the old error is worth recording. `typed_TSub` (denotation ⊆ judgement)
was unaffected and still holds — the surplus was on the *judgement's* side, so no law
broke and `soundness` never depended on it. What was wrong was the advertised precision of
the `: T` index, which is exactly the claim §6 was unable to check while fuel was in the
way.
-/

namespace Calculus

/-- `Uν` does not admit the empty set — the premise `Typing.lean` now carries. -/
theorem not_hopaque_set_nil (lossy : Bool) : ¬ HOpaque lossy (Value.set []) := by
  intro h
  cases h with
  | set vs hne hs => exact hne rfl

/-- Nor could it ever have: no fuel holds `set []`. `setCodec` demands a nonempty element
    list, and every other option is a different kind. -/
theorem opaqCodec_T_set_nil (lossy : Bool) :
    ∀ n, ¬ (opaqCodec n lossy).T (Value.set []) := by
  intro n hn
  cases n with
  | zero => exact hn
  | succ n' =>
    obtain ⟨o, ho, hT⟩ := hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    cases lossy <;>
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [OptionSem.byAttempt, stringCodec, booleanCodec, binaryCodec, nullCodec,
                  numberCodec, Codec.empty, setCodec, arrayCodec, recordCodec]

theorem opaqCodecω_T_set_nil (lossy : Bool) : ¬ (opaqCodecω lossy).T (Value.set []) := by
  rintro ⟨n, hn⟩
  exact opaqCodec_T_set_nil lossy n hn

/-- And nothing is written for it: `asWireSet []` refuses, so no option admits. -/
theorem opaqCodecω_e_set_nil (lossy : Bool) :
    (opaqCodecω lossy).e (Value.set []) = none := by
  show (opaqCodec (Value.depth (Value.set [])) lossy).e (Value.set []) = none
  have hd : Value.depth (Value.set []) = 1 + 1 := rfl
  rw [hd, opaqCodec_e_set]
  simp [setCodec, traverse, asWireSet]

/-- The three agree, which is what makes the corrected `Uν` the right one: the value the
    old inductive admitted is held by no fuel and written by none. -/
theorem set_nil_outside_opaque (lossy : Bool) :
    ¬ HOpaque lossy (Value.set [])
    ∧ ¬ (opaqCodecω lossy).T (Value.set [])
    ∧ (opaqCodecω lossy).e (Value.set []) = none :=
  ⟨not_hopaque_set_nil lossy, opaqCodecω_T_set_nil lossy, opaqCodecω_e_set_nil lossy⟩

/-! ## `T` as an identity, for `opaque`

With `Uν` corrected, the converse of `opaq_TSub` goes through: everything `Uν` admits, the
denotation holds. §6's row asked for exactly this and could not have it while fuel was in
the statement — the missing "fuel exceeds depth" hypothesis is now `Value.depth`.

Note the shape of the induction. The statement quantifies over *all* sufficient budgets
(`∀ n, Value.depth v ≤ n → …`) rather than fixing `n = Value.depth v`. That is what lets
the `set`/`array`/`map` cases hand their elements the parent's budget directly, with no
monotonicity lemma in between: each element's depth is below the list's, which is below
`n`. -/

mutual

theorem hopaque_T (lossy : Bool) :
    ∀ (v : Value) (n : Nat), HOpaque lossy v -> Value.depth v <= n ->
      (opaqCodec n lossy).T v
  | .str s, n, _, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      exact ⟨.byAttempt stringCodec, by simp, ⟨s, rfl⟩⟩
  | .bool b, n, _, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      exact ⟨.byAttempt booleanCodec, by simp, ⟨b, rfl⟩⟩
  | .bin b, n, _, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      exact ⟨.byAttempt binaryCodec, by simp, ⟨b, rfl⟩⟩
  | .null, n, _, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      exact ⟨.byAttempt nullCodec, by simp, rfl⟩
  | .num d, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | num _ hl =>
        subst hl
        exact ⟨.byAttempt (if true then numberCodec else Codec.empty), by simp, ⟨d, rfl⟩⟩
  | .set vs, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | set _ hne hall =>
        have hL : Value.depthL vs <= n' := by simp only [Value.depth] at hd; omega
        exact ⟨.byAttempt (setCodec (opaqCodec n' lossy)), by simp,
               ⟨hne, hopaque_TL lossy vs n' hall hL⟩⟩
  | .arr vs, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | arr _ hall =>
        have hL : Value.depthL vs <= n' := by simp only [Value.depth] at hd; omega
        exact ⟨.byAttempt (arrayCodec (opaqCodec n' lossy)), by simp,
               hopaque_TL lossy vs n' hall hL⟩
  | .map kvs, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | map _ hall =>
        have hP : Value.depthP kvs <= n' := by simp only [Value.depth] at hd; omega
        exact ⟨.byAttempt (recordCodec (opaqCodec n' lossy)), by simp,
               hopaque_TP lossy kvs n' hall hP⟩

theorem hopaque_TL (lossy : Bool) :
    ∀ (vs : List Value) (n : Nat), (∀ x ∈ vs, HOpaque lossy x) ->
      Value.depthL vs <= n -> ∀ x ∈ vs, (opaqCodec n lossy).T x
  | [], _, _, _, x, hx => absurd hx (by simp)
  | v :: vs, n, hall, hd, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hopaque_T lossy x n (hall x (by simp))
          (by simp only [Value.depthL] at hd; omega)
      · exact hopaque_TL lossy vs n (fun y hy => hall y (by simp [hy]))
          (by simp only [Value.depthL] at hd; omega) x hx'

theorem hopaque_TP (lossy : Bool) :
    ∀ (kvs : List (Name × Value)) (n : Nat), (∀ kv ∈ kvs, HOpaque lossy kv.2) ->
      Value.depthP kvs <= n -> ∀ kv ∈ kvs, (opaqCodec n lossy).T kv.2
  | [], _, _, _, kv, hkv => absurd hkv (by simp)
  | kv :: kvs, n, hall, hd, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hopaque_T lossy x.2 n (hall x (by simp))
          (by simp only [Value.depthP] at hd; omega)
      · exact hopaque_TP lossy kvs n (fun y hy => hall y (by simp [hy]))
          (by simp only [Value.depthP] at hd; omega) x hx'

end

/-- **§3's `Uν` *is* `opaque`'s held set.** The row §6 called unproved, and unprovable in
    the fuel encoding, closed for the case it said bites hardest. -/
theorem opaq_T_identity (lossy : Bool) (v : Value) :
    (opaqCodecω lossy).T v ↔ HOpaque lossy v := by
  constructor
  · rintro ⟨n, hn⟩
    exact opaq_TSub n lossy v hn
  · intro h
    exact ⟨Value.depth v, hopaque_T lossy v (Value.depth v) h (Nat.le_refl _)⟩

/-! ## §1's numeral domain, checked

`docs/codec-formalization.md` §6 listed `Numeral := String` as a gap: the grammar, the 38
significant digits and the magnitude range were unmodelled, "so `decimal` currently holds
every string", with the note that once the predicate is tightened `typed_e_mem` reports
whether the codec respects it. `Domain.lean` now carries §1's predicate and
`decimalCodec` gates on it, so here is that report.

The carrier is deliberately *not* restricted — `Attr.n "abc"` is still representable,
because §1 describes which strings DynamoDB accepts in an `N`, and the calculus's job is
that its codecs write only those. What changed is that the claim is now checkable. -/

/-- `decimal`'s held set is exactly §1's `Numerals`. -/
theorem decimal_T (v : Value) :
    (denoteω .decimal).T v ↔ ∃ s, v = .str s ∧ Numeral.WF s = true := Iff.rfl

/-- **The report.** A derivable `decimal` writes only well-formed numerals — the tightened
    `: T` index, cashed on the attribute side. -/
theorem decimal_writes_wf {v : Value} {a : Attr}
    (he : (denoteω .decimal).e v = some a) :
    ∃ x, a = .n x ∧ Numeral.WF x = true := by
  cases v with
  | str s =>
    replace he : (if Numeral.WF s = true then some (Attr.n s) else none) = some a := he
    by_cases hw : Numeral.WF s = true
    · rw [if_pos hw] at he; cases he; exact ⟨s, rfl, hw⟩
    · rw [if_neg hw] at he; exact nomatch he
  | _ =>
    replace he : (none : Option Attr) = some a := he
    exact nomatch he

/-- Dually, it reads only well-formed numerals — which is not a nicety: a `p` accepting an
    ill-formed `N` would name a value `e` then refuses, and that is **(C)** failing. -/
theorem decimal_reads_wf {a : Attr} {v : Value}
    (hp : (denoteω .decimal).p a = some v) :
    ∃ x, a = .n x ∧ Numeral.WF x = true := by
  cases a with
  | n x =>
    replace hp : (if Numeral.WF x = true then some (Value.str x) else none) = some v := hp
    by_cases hw : Numeral.WF x = true
    · exact ⟨x, rfl, hw⟩
    · rw [if_neg hw] at hp; exact nomatch hp
  | _ =>
    replace hp : (none : Option Value) = some v := hp
    exact nomatch hp

/-! ### The gap that closed

Before the tightening, `decimal` wrote an `N` for every string. It no longer does, and §1's
own worked example still goes through — the doc is explicit that `"1e+21"` is well formed
and "not a defect", the bound that bites being magnitude rather than notation. -/

theorem decimal_refuses_nonNumeral : (denoteω .decimal).e (.str "abc") = none := rfl

theorem decimal_refuses_overMagnitude : (denoteω .decimal).e (.str "1e130") = none := rfl

theorem decimal_refuses_39_digits :
    (denoteω .decimal).e (.str "123456789012345678901234567890123456789") = none := rfl

/-- §1's own example: an exponent is notation, not a magnitude violation. -/
theorem decimal_accepts_exponent :
    (denoteω .decimal).e (.str "1e+21") = some (.n "1e+21") := rfl

/-- Both magnitude boundaries are inside the domain. -/
theorem decimal_accepts_min : (denoteω .decimal).e (.str "1e-130") = some (.n "1e-130") :=
  rfl

theorem decimal_accepts_max : (denoteω .decimal).e (.str "9e125") = some (.n "9e125") := rfl

end Calculus
