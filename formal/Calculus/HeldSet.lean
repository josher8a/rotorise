import Calculus.Soundness

/-!
# `Uν` and the empty set — a mechanization bug, closed by the type

"`T` as an identity" was long unproved, and it bites hardest at `opaque`, where §3 says
`Uν` *is* the held set. Attempting it turned up
a defect — and, unlike §4's three, this one was in the **model**, not the specification.

`HOpaque`'s `set` clause was transcribed as

```
| set (vs) (h : ∀ x ∈ vs, HOpaque lossy x) : HOpaque lossy (.set vs)
```

with no constraint on `vs`, so `HOpaque lossy (set [])` held vacuously. Nothing in the
calculus agreed:

* §1's `SS`/`NS`/`BS` are `℘⁺fin` — explicitly non-empty. There is no empty wire set to
  write.
* `(set)`'s own held set `HSet` excluded it. §3 exhibits `Uν` as the fixpoint
  `union(…, set(opaque), …)`, whose `set` option is that rule — so the fixpoint reading
  excludes `set []` too.
* §3's prose reading — "the values whose member is recoverable from the value alone" —
  excludes it as well, and for the sharpest reason: an empty set has no payloads, so
  `SS`, `NS` and `BS` are indistinguishable. Its member is precisely what cannot be
  recovered.

**The repair went through three stages, and the last one is why this section is now
prose.** First the inductive gained `hne : vs ≠ []`, and three theorems here exhibited the
gap: ~~not_hopaque_set_nil~~, ~~opaqCodec_T_set_nil~~ and ~~opaqCodecω_e_set_nil~~ — the empty
set is held by no fuel, written by none, and refused by the corrected `Uν`. Then the sets
became `Finset`, and `vs ≠ []` became `S.Nonempty`. Now `Value.strSet` takes a
`NEFinset String`, and **the three theorems cannot be stated**: `Value.strSet ∅` does not
typecheck, because `∅` carries no non-emptiness proof and `℘⁺fin` has no other inhabitant
to offer.

That is the closure, and it is the same shape as the map defect's
(~~record_e_keeps_duplicate_keys~~ became unstatable when `M`'s keys became a `Finset`). A
witness that a value is excluded is worth having exactly while the value is expressible.
When the type stops admitting it, the witness stops being a theorem and becomes a
typechecking error at the point where anyone would try to write it down — which is
earlier, and cheaper to act on.

The direction matters: `typed_TSub` (denotation ⊆ judgement) holds either way, so no law
depends on this. What a surplus on the judgement's side costs is the advertised precision of
the `: T` index, and nothing else.
-/

namespace Calculus

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
      exact ⟨.byAttempt stringCodec, by simp [opaqOptions], ⟨s, rfl⟩⟩
  | .bool b, n, _, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      exact ⟨.byAttempt booleanCodec, by simp [opaqOptions], ⟨b, rfl⟩⟩
  | .bin b, n, _, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      exact ⟨.byAttempt binaryCodec, by simp [opaqOptions], ⟨b, rfl⟩⟩
  | .null, n, _, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      exact ⟨.byAttempt nullCodec, by simp [opaqOptions], rfl⟩
  | .num d, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | num _ hl hw =>
        subst hl
        exact ⟨.byAttempt (if true then numberCodec else Codec.empty), by simp [opaqOptions],
               ⟨d, rfl, hw⟩⟩
  | .strSet S, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | strSet _ hall =>
        exact ⟨.byAttempt (setCodec (opaqCodec n' lossy)), by simp [opaqOptions],
               fun x hx => hopaque_T lossy (.str x) n' (hall x hx) (by
                  simp only [Value.depth] at hd ⊢; omega)⟩
  | .numSet S, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | numSet _ hall =>
        exact ⟨.byAttempt (setCodec (opaqCodec n' lossy)), by simp [opaqOptions],
               fun x hx => hopaque_T lossy (.num x) n' (hall x hx) (by
                  simp only [Value.depth] at hd ⊢; omega)⟩
  | .binSet S, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | binSet _ hall =>
        exact ⟨.byAttempt (setCodec (opaqCodec n' lossy)), by simp [opaqOptions],
               fun x hx => hopaque_T lossy (.bin x) n' (hall x hx) (by
                  simp only [Value.depth] at hd ⊢; omega)⟩
  | .arr vs, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | arr _ hall =>
        have hL : Value.depthL vs <= n' := by simp only [Value.depth] at hd; omega
        exact ⟨.byAttempt (arrayCodec (opaqCodec n' lossy)), by simp [opaqOptions],
               hopaque_TL lossy vs n' hall hL⟩
  -- No list companion on this branch: `recordCodec`'s held set is already the pointwise
  -- statement about the entry function, so the induction hypothesis applies at each key
  -- with no traversal in between.
  | .map keys f, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | map _ _ hall =>
        exact ⟨.byAttempt (recordCodec (opaqCodec n' lossy)), by simp [opaqOptions],
               fun k => hopaque_T lossy (f k) n' (hall k)
                 (by have := Value.depth_map_entry (f := f) k; omega)⟩
termination_by v n => (n, sizeOf v)

theorem hopaque_TL (lossy : Bool) :
    ∀ (vs : List Value) (n : Nat), (∀ x ∈ vs, HOpaque lossy x) ->
      Value.depthL vs <= n -> ∀ x ∈ vs, (opaqCodec n lossy).T x
  | [], _, _, _, x, hx => absurd hx (by simp)
  | v :: vs, n, hall, hd, x, hx => by
      rcases List.mem_cons.mp hx with h | hx'
      · exact h ▸ hopaque_T lossy v n (hall v (by simp))
          (by simp only [Value.depthL] at hd; omega)
      · exact hopaque_TL lossy vs n (fun y hy => hall y (by simp [hy]))
          (by simp only [Value.depthL] at hd; omega) x hx'
termination_by vs n => (n, sizeOf vs)

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

/-! ## …and in general, at every rule

`opaq_T_identity` closes (A) at the constructor §3 says it bites hardest at. The general
statement lives **here rather than beside `typed_TSub`**, which is where its mirror is and
where it belongs by shape, for one reason that is not a preference: its `opaque` case is
`opaq_T_identity`, and this module imports `Soundness.lean`. Moving the theorem up would
mean moving `hopaque_T`'s mutual block with it, and that block is about `Value.depth` — a
recursion on the *input*, `Opaque.lean`'s, not `denote`'s on the term. The four list and
table helpers the other rules need did stay beside their converses in `Soundness.lean`;
only the two theorems that reach `opaque` are here.

So `term_depth_wf`'s users are **no longer all in one module**. The reason they are not is
written above, and no document carries a count of them.
-/

-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- **The judgement's held set is inside the denotation's** — `typed_TSub` the other way, and
    the direction that was open.

    `HeldSet.lean` names this claim (A) and had it only at `opaque` (`opaq_T_identity`); the
    general statement is here because it is `typed_TSub`'s mirror and recurses the same way.
    Every rule closes: the ground rules, `literal` and `custom` are `exact hv`, the two
    containers and the four wrappers reduce past their constructor, `opaque` is the existing
    iff, and `set` is `SetBase.elem_T`. Only four rules need anything new, and each needs the
    converse of a helper that was already here for the other direction.

    **What this does *not* say is `T = dom(e)`**, which is a different claim, is false at a
    `union`, and is the one `HeldSet.lean`'s `TIsDomE` and `not_TIsDomE_unionLiteralString`
    are about. Reading (A) as (B) is the mistake §6's row made. Held is not written. -/
theorem typed_T_eq : ∀ {t T μ}, Typed t T μ → ∀ v, T v → (denote t).T v
  | t, T, μ, h, v, hv => by
    cases h with
    | string | number | decimal | boolean | binary | null => exact hv
    -- the carrier is gated, so the rule's `HLit k ls` and the denotation's are one
    -- expression — the same fact that removed `typed_TSub`'s five-way split here
    | literal _ _ => exact hv
    | never => exact hv
    | custom _ _ => exact hv
    | opaq lossy => exact (opaq_T_identity lossy v).mpr hv
    | set b =>
      rcases hv with ⟨S, rfl, hall⟩ | ⟨S, rfl, hall⟩ | ⟨S, rfl, hall⟩ <;>
        simp only [denote, setCodec, SetBase.elem_T] <;> exact hall
    | @record t' T' μ' h' =>
      obtain ⟨keys, f, rfl, hall⟩ := hv
      exact fun k => typed_T_eq h' _ (hall k)
    | @list pre Tpre sp Tsp suf Tsuf hp hs hf =>
      obtain ⟨vs, rfl, hall⟩ := hv
      rw [denote, denoteList_eq, denoteOpt_eq, denoteList_eq]
      exact alignL_T_of_HTupleL hp hs hf
        (fun t' _ _ _ hty w hw => typed_T_eq hty w hw)
        (fun t' _ _ _ hty w hw => typed_T_eq hty w hw)
        (fun t' _ _ _ hty w hw => typed_T_eq hty w hw) hall
    | @held t' I' μ' f g h' => exact typed_T_eq h' (f v) hv
    | @refine t' T' μ' q h' => exact ⟨typed_T_eq h' v hv.1, hv.2⟩
    | @legacy t' T' μ' r h' => exact typed_T_eq h' v hv
    | @lazy t' T' μ' h' => exact typed_T_eq h' v hv
    | @object body bind R μs hfields hrest =>
      cases body with | mk fields ff rest =>
      simp only [Body.fields_mk, Body.at_mk, Body.rest_mk] at hfields hrest hv ⊢
      obtain ⟨keys, f, rfl, hreq, hall⟩ := hv
      refine ⟨⟨keys, f⟩, rfl, ?_, ?_⟩
      · refine valPresentB_of fun k fs hm hno => ?_
        obtain ⟨hk, rfl⟩ := MapOf.at_eq_some.mp hm
        refine hreq ⟨k, hk⟩ (TypedField.true_of_not_optional (hfields ⟨k, hk⟩) ?_)
        intro t' hc
        exact hno (denote t') (congrArg fieldSem hc)
      · intro k
        have hentry := hall k
        by_cases hk : k.1 ∈ fields
        · rw [dif_pos hk] at hentry
          simp only [objEntryT,
            MapOf.at_of_mem (m := (⟨fields, fun k => fieldSem (ff k)⟩ :
              MapOf FieldSem)) ⟨k.1, hk⟩]
          obtain ⟨t', hty', hshape⟩ := TypedField.term (hfields ⟨k.1, hk⟩)
          rcases hshape with heq | heq | ⟨v₀, heq⟩ <;> rw [heq] <;>
            exact typed_T_eq hty' _ hentry
        -- an undeclared name under `drop` or `refuse` is refused by *both* sides: `R` is
        -- `none` by `TypedRest` and `rcOf` is `none` by definition, so the two branches are
        -- the same `False` and the case closes on their agreement rather than despite it
        · rw [dif_neg hk] at hentry
          obtain ⟨T'', hR, hT''⟩ := hentry
          simp only [objEntryT, MapOf.at, dif_neg hk]
          cases hrest with
          | drop => exact nomatch hR
          | refuse => exact nomatch hR
          | @codec t' T''' μ'' hty' =>
            obtain rfl : T''' = T'' := Option.some.inj hR
            exact ⟨denote t', rfl, typed_T_eq hty' _ hT''⟩
    | @union opts Ts μs h' hD =>
      obtain ⟨T', hT', hTv⟩ := hv
      obtain ⟨tx, htx, hd⟩ :=
        unionT_of_mem h' (fun t' _ _ _ hty w hw => typed_T_eq hty w hw) v T' hT' hTv
      simp only [denote, optionSems_eq]
      refine ⟨optionSemOf (denote tx) (specOf tx), ?_, ?_⟩
      · simp only [List.mem_map]; exact ⟨tx, htx, rfl⟩
      · rw [optionSemOf_c]; exact hd
termination_by t _ _ _ _ => Term.depth t
decreasing_by term_depth_wf

/-- **§3's `⊢ c : T ⇝ μ` names the denotation's held set exactly**, at every rule.

    So the index is a description and carries nothing the pair does not. It stays anyway:
    the rules are the model's transcription of §3, and a judgement whose held set is spelled
    `(denote t).T` cannot be read against the document it transcribes. What the identity buys
    is that the reading is now checked rather than advertised. -/
theorem typed_T_identity {t T μ} (h : Typed t T μ) (v : Value) : (denote t).T v ↔ T v :=
  ⟨typed_TSub h v, typed_T_eq h v⟩

/-! ## Which identity? §6's row is two of them

* **(A)** `(denote t).T = T` for a derivable `⊢ t : T ⇝ μ` — §3's "`Uν` *is* `opaque`'s held
  set", which `opaq_T_identity` proves at `opaque` and `typed_T_identity` now proves at every
  rule. **Closed**, and it was the half `typed_TSub` left.
* **(B)** `T = dom(e)` — what makes `: T` an honest index rather than an upper bound.
  `Carrier.domE` is its other half.

§6's row asserted (A) and then justified it with a sentence about (B). (A) is not false at
`union`; it is definitional — and it is now proved everywhere else too, so **(B) is the whole
of what is left open**, and `not_TIsDomE_unionLiteralString` is its witness. Reading a proof of
(A) as a claim about (B) is the mistake the row made, and the reason both are named here. -/

/-- **(A) at a union is definitional.** `altCodec`'s held set *is* the union of its options'
    — no (U), no premise, nothing to prove. So the union case of (A) is exactly the options'
    (A), and §6's "false for `union`" cannot be about this claim. -/
theorem altCodec_T (os : List OptionSem) (μA : Option Member) (v : Value) :
    (altCodec os μA).T v ↔ ∃ o ∈ os, o.c.T v := Iff.rfl

/-- **(B), named.** The held set is exactly what the pair can write — `T = dom(e)`.
    `Carrier.domE` gives `dom(e) ⊆ T` for every derivable term; this is the converse, and it
    is the direction that fails. -/
def TIsDomE (c : Codec) : Prop := ∀ v, c.T v ↔ (c.e v).isSome

/-- §4's counterexample pair: both options admit `"A"`, which is what refuted §5's withdrawn
    discharger. -/
noncomputable def unionLiteralString : Codec :=
  altCodec [.byAttempt (literalCodec .string "A"), .byAttempt stringCodec] (some .S)

/-- **(B) is false for `union`:** `"A"` is held and nothing is written for it, both options
    admitting. Not unsound — `Carrier` bounds `e` by `T`, never the converse — but `: T` at a
    `union` is an upper bound unless (U) holds in full. -/
theorem not_TIsDomE_unionLiteralString : ¬ TIsDomE unionLiteralString := by
  intro h
  have hT : unionLiteralString.T (.str "A") :=
    ⟨.byAttempt (literalCodec .string "A"), by simp [], rfl⟩
  have he : unionLiteralString.e (.str "A") = none := by
    simp [unionLiteralString, altCodec, select, OptionSem.byAttempt, literalCodec, baseCodec,
      Codec.restrict, inL, stringCodec]
  have := (h (.str "A")).mp hT
  rw [he] at this
  exact nomatch this

/-! ## §1's numeral domain, checked

`Numeral := String` was a standing gap: the grammar, the 38
significant digits and the magnitude range were unmodelled, so `decimal` held
every string", with the note that once the predicate is tightened `typed_e_mem` reports
whether the codec respects it. `Domain.lean` now carries §1's predicate and
`decimalCodec` gates on it, so here is that report.

The carrier is no longer unrestricted either: `Attr.n` carries `WFNumeral`, so `⟨N, "abc"⟩`
is not an attribute and `decimal`'s report below is about a codec whose target is exactly
§1's. That was the last of §5's four refined members to be typed, and the argument for
leaving it alone — that a port should see the embedding is partial — did not survive: the
partiality is a fact about the port's types, not the model's. -/

/-- `decimal`'s held set is exactly §1's `Numerals`. -/
theorem decimal_T (v : Value) :
    (denote .decimal).T v ↔ ∃ s, v = .str s ∧ Numeral.Stored s = true := Iff.rfl

/-- **The report.** A derivable `decimal` writes only well-formed numerals — the tightened
    `: T` index, cashed on the attribute side. -/
theorem decimal_writes_stored {v : Value} {a : Attr}
    (he : (denote .decimal).e v = some a) :
    ∃ x, a = .n x ∧ Numeral.Stored x = true := by
  cases v with
  | str s =>
    rw [show (denote .decimal).e (.str s) = decimalCodec.e (.str s) from rfl,
      decimalCodec_e_str] at he
    by_cases hw : Numeral.Stored s = true
    · rw [dif_pos hw] at he; cases he; exact ⟨_, rfl, hw⟩
    · rw [dif_neg hw] at he; exact nomatch he
  | _ =>
    replace he : (none : Option Attr) = some a := he
    exact nomatch he

/-- Dually, it reads only well-formed numerals — which is not a nicety: a `p` accepting an
    ill-formed `N` would name a value `e` then refuses, and that is **(C)** failing. -/
theorem decimal_reads_stored {a : Attr} {v : Value}
    (hp : (denote .decimal).p a = some v) :
    ∃ x, a = .n x ∧ Numeral.Stored x = true := by
  cases a with
  | n x =>
    replace hp : (if Numeral.Stored x = true then some (Value.str x) else none) = some v := hp
    by_cases hw : Numeral.Stored x = true
    · exact ⟨x, rfl, hw⟩
    · rw [if_neg hw] at hp; exact nomatch hp
  | _ =>
    replace hp : (none : Option Value) = some v := hp
    exact nomatch hp

/-! ### The gap that closed, and the one behind it

Before the tightening, `decimal` wrote an `N` for every string. It no longer does — and the
second tightening is the one no reading of the specification could have produced, because
it is a fact about the **store** rather than about the calculus.

§1's worked example says `"1e+21"` is well formed and that treating it as out of range
would be a defect, "the bound that bites being magnitude rather than notation". That is
still true of `Numeral.WF`, which is what DynamoDB *accepts*. It is not true of `decimal`,
because DynamoDB hands `1e+21` back as `1000000000000000000000`, and `decimal`'s `p` is the
identity on the digits — so the round trip fails at the one point §2 cannot see, between
`e` and `p`. `Numeral.Stored` is that set, and the measurements it is read off are in
`src/codec/spec/surface/codec.dynamodb.spec.ts`. -/

theorem decimal_refuses_nonNumeral : (denote .decimal).e (.str "abc") = none := rfl

/-- Magnitude, isolated at the `WF` level, where notation is not also in play. -/
theorem wf_refuses_overMagnitude : Numeral.WF "1e130" = false := by decide

theorem wf_refuses_39_digits :
    Numeral.WF "123456789012345678901234567890123456789" = false := by decide

theorem decimal_refuses_39_digits :
    (denote .decimal).e (.str "123456789012345678901234567890123456789") = none := rfl

/-- §1's own example, at the level it was written about: the service accepts an exponent. -/
theorem wf_accepts_exponent : Numeral.WF "1e+21" = true := by decide

/-- `decimal` does not, and the reason is the store rather than the grammar. -/
theorem decimal_refuses_exponent : (denote .decimal).e (.str "1e+21") = none := rfl

/-- The same number, spelled the way it comes back. -/
theorem decimal_accepts_expanded :
    (denote .decimal).e (.str "1000000000000000000000")
      = some (.n (.of "1000000000000000000000")) := rfl

end Calculus
