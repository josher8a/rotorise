import Calculus.Soundness

/-!
# `HOpaque` and the empty set — a mechanization bug, closed by the type

"`T` as an identity" was long unproved, and it bites hardest at `opaque`, where
`HOpaque` *is* the held set. Attempting it turned up
a defect — and, unlike §4's three, this one was in the **model**, not the specification.

`HOpaque`'s `set` clause was transcribed as

```
| set (vs) (h : ∀ x ∈ vs, HOpaque lossy x) : HOpaque lossy (.set vs)
```

with no constraint on `vs`, so `HOpaque lossy (set [])` held vacuously. Nothing in the
calculus agreed:

* §1's `SS`/`NS`/`BS` are `℘⁺fin` — explicitly non-empty. There is no empty wire set to
  write.
* `(set)`'s own held set `HSet` excluded it. §3 exhibits `opaque` as the fixpoint
  `union(…, set(opaque), …)`, whose `set` option is that rule — so the fixpoint reading
  excludes `set []` too.
* §3's prose reading — "the values whose member is recoverable from the value alone" —
  excludes it as well, and for the sharpest reason: an empty set has no payloads, so
  `SS`, `NS` and `BS` are indistinguishable. Its member is precisely what cannot be
  recovered.

**The repair went through three stages, and the last one is why this section is now
prose.** First the inductive gained `hne : vs ≠ []`, and three theorems here exhibited the
gap: ~~not_hopaque_set_nil~~, ~~opaqCodec_T_set_nil~~ and ~~opaqCodecω_e_set_nil~~ — the empty
set is held by no fuel, written by none, and refused by the corrected `HOpaque`. Then the sets
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

With `HOpaque` corrected, the converse of `opaq_TSub` goes through: everything `HOpaque` admits, the
denotation holds. §6's row asked for exactly this and could not have it while fuel was in
the statement — the missing "fuel exceeds depth" hypothesis is now `Value.depth`.

Note the shape of the induction. The statement quantifies over *all* sufficient budgets
(`∀ n, Value.depth v ≤ n → …`) rather than fixing `n = Value.depth v`. That is what lets
the `set`/`array`/`map` cases hand their elements the parent's budget directly, with no
monotonicity lemma in between: each element's depth is below the list's, which is below
`n`. -/

mutual

theorem hopaque_T :
    ∀ (v : Value) (n : Nat), HOpaque v -> Value.depth v <= n ->
      (opaqCodec n).T v
  | .str s, n, _, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      exact ⟨stringCodec, by simp [opaqOptions], ⟨s, rfl⟩⟩
  | .bool b, n, _, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      exact ⟨booleanCodec, by simp [opaqOptions], ⟨b, rfl⟩⟩
  | .bin b, n, _, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      exact ⟨binaryCodec, by simp [opaqOptions], ⟨b, rfl⟩⟩
  | .null, n, _, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      exact ⟨nullCodec, by simp [opaqOptions], rfl⟩
  | .num d, n, _, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      exact ⟨numberCodec, by simp [opaqOptions], ⟨d, rfl⟩⟩
  | .strSet S, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | strSet _ hall =>
        exact ⟨(setCodec (opaqCodec n')), by simp [opaqOptions],
               fun x hx => hopaque_T (.str x) n' (hall x hx) (by
                  simp only [Value.depth] at hd ⊢; omega)⟩
  | .numSet S, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | numSet _ hall =>
        exact ⟨(setCodec (opaqCodec n')), by simp [opaqOptions],
               fun x hx => hopaque_T (.num x) n' (hall x hx) (by
                  simp only [Value.depth] at hd ⊢; omega)⟩
  | .binSet S, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | binSet _ hall =>
        exact ⟨(setCodec (opaqCodec n')), by simp [opaqOptions],
               fun x hx => hopaque_T (.bin x) n' (hall x hx) (by
                  simp only [Value.depth] at hd ⊢; omega)⟩
  | .arr vs, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | arr _ hall =>
        have hL : Value.depthL vs <= n' := by simp only [Value.depth] at hd; omega
        exact ⟨(arrayCodec (opaqCodec n')), by simp [opaqOptions],
               hopaque_TL vs n' hall hL⟩
  -- No list companion on this branch: `recordCodec`'s held set is already the pointwise
  -- statement about the entry function, so the induction hypothesis applies at each key
  -- with no traversal in between.
  | .map keys f, n, h, hd => by
      cases n with | zero => exact absurd hd (by simp [Value.depth]) | succ n' =>
      cases h with
      | map _ _ hall =>
        exact ⟨(recordCodec (opaqCodec n')), by simp [opaqOptions],
               fun k => hopaque_T (f k) n' (hall k)
                 (by have := Value.depth_map_entry (f := f) k; omega)⟩
termination_by v n => (n, sizeOf v)

theorem hopaque_TL :
    ∀ (vs : List Value) (n : Nat), (∀ x ∈ vs, HOpaque x) ->
      Value.depthL vs <= n -> ∀ x ∈ vs, (opaqCodec n).T x
  | [], _, _, _, x, hx => absurd hx (by simp)
  | v :: vs, n, hall, hd, x, hx => by
      rcases List.mem_cons.mp hx with h | hx'
      · exact h ▸ hopaque_T v n (hall v (by simp))
          (by simp only [Value.depthL] at hd; omega)
      · exact hopaque_TL vs n (fun y hy => hall y (by simp [hy]))
          (by simp only [Value.depthL] at hd; omega) x hx'
termination_by vs n => (n, sizeOf vs)

end

/-- **`HOpaque` *is* `opaque`'s held set.** The row §6 called unproved, and unprovable in
    the fuel encoding, closed for the case it said bites hardest. -/
theorem opaq_T_identity (v : Value) :
    (opaqCodecω).T v ↔ HOpaque v := by
  constructor
  · rintro ⟨n, hn⟩
    exact opaq_TSub n v hn
  · intro h
    exact ⟨Value.depth v, hopaque_T v (Value.depth v) h (Nat.le_refl _)⟩

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
    Every rule closes: the ground rules and `literal` are `exact hv`, the two
    containers and the four wrappers reduce past their constructor, `opaque` is the existing
    iff, and `set` is `SetBase.elem_T`. Only four rules need anything new, and each needs the
    converse of a helper that was already here for the other direction.

    **What this does *not* say is `T = dom(e)`**, which is a different claim, proved by
    `typed_T_adm` (`Laminar.lean`). Reading (A) as (B) is the mistake §6's row made. -/
theorem typed_T_eq : ∀ {t T μ}, Typed t T μ → ∀ v, T v → (denote t).T v
  | t, T, μ, h, v, hv => by
    cases h with
    | string | number | boolean | binary | null => exact hv
    -- the carrier is gated, so the rule's `HLit k ls` and the denotation's are one
    -- expression — the same fact that removed `typed_TSub`'s five-way split here
    | literal _ _ => exact hv
    | never => exact hv
    | opaq => exact (opaq_T_identity v).mpr hv
    | set b =>
      rcases hv with ⟨S, rfl, hall⟩ | ⟨S, rfl, hall⟩ | ⟨S, rfl, hall⟩ <;>
        simp only [denote, setCodec, SetBase.elem_T] <;> exact hall
    | @list pre Tpre sp Tsp suf Tsuf hp hs hf =>
      obtain ⟨vs, rfl, hall⟩ := hv
      rw [denote, denoteList_eq, denoteOpt_eq, denoteList_eq]
      exact alignL_T_of_HTupleL hp hs hf
        (fun t' _ _ _ hty w hw => typed_T_eq hty w hw)
        (fun t' _ _ _ hty w hw => typed_T_eq hty w hw)
        (fun t' _ _ _ hty w hw => typed_T_eq hty w hw) hall
    | @held t' I' μ' P f g h' => exact ⟨typed_T_eq h' (f v) hv.1, hv.2⟩
    | @refine t' T' μ' q h' => exact ⟨typed_T_eq h' v hv.1, hv.2⟩
    | @lazy t' T' μ' h' => exact typed_T_eq h' v hv
    | @object body bind R μs hfields hrest =>
      cases body with | mk fields ff wild =>
      simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at hfields hrest hv ⊢
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
          rcases hshape with heq | heq
          · rw [heq]; exact typed_T_eq hty' _ hentry
          · rw [heq]; exact typed_T_eq hty' _ hentry
        -- an undeclared name in a body with no open block is refused by *both* sides: `R` is
        -- `none` by `TypedWild` and `rcOf` is `none` by definition, so the two branches are
        -- the same `False` and the case closes on their agreement rather than despite it
        · rw [dif_neg hk] at hentry
          obtain ⟨T'', hR, hT''⟩ := hentry
          simp only [objEntryT, MapOf.at, dif_neg hk]
          cases hrest with
          | none => exact nomatch hR
          | @some t' T''' μ'' hty' =>
            obtain rfl : T''' = T'' := Option.some.inj hR
            exact ⟨denote t', rfl, typed_T_eq hty' _ hT''⟩
    | @union opts Ts μs h' =>
      obtain ⟨T', hT', hTv⟩ := hv
      obtain ⟨tx, htx, hd⟩ :=
        unionT_of_mem h' (fun t' _ _ _ hty w hw => typed_T_eq hty w hw) v T' hT' hTv
      simp only [denote, denoteList_eq]
      refine ⟨denote tx, ?_, ?_⟩
      · simp only [List.mem_map]; exact ⟨tx, htx, rfl⟩
      · exact hd
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

* **(A)** `(denote t).T = T` for a derivable `⊢ t : T ⇝ μ` — `HOpaque` *is* `opaque`'s held
  set, which `opaq_T_identity` proves at `opaque` and `typed_T_identity` now proves at every
  rule. **Closed**, and it was the half `typed_TSub` left.
* **(B)** `T = dom(e)` — what makes `: T` an honest index rather than an upper bound.
  `Carrier.domE` is its other half.

§6's row asserted (A) and then justified it with a sentence about (B). (A) is not false at
`union`; it is definitional — and it is now proved everywhere else too. **(B) holds at every
derivable term** by `typed_T_adm` (`Laminar.lean`): a union writes wherever one of its options
writes. Reading a proof of (A) as a claim about (B) is the mistake the row made, and the reason
both are named here. -/

/-- **(A) at a union is definitional.** `altCodec`'s held set *is* the union of its options'
    — no premise, nothing to prove. So the union case of (A) is exactly the options'
    (A), and §6's "false for `union`" cannot be about this claim. -/
theorem altCodec_T (os : List Codec) (μA : Option Member) (v : Value) :
    (altCodec os μA).T v ↔ ∃ o ∈ os, o.T v := Iff.rfl

/-- **(B), named.** The held set is exactly what the pair can write — `T = dom(e)`.
    `Carrier.domE` gives `dom(e) ⊆ T` for every derivable term; this is the converse. -/
def TIsDomE (c : Codec) : Prop := ∀ v, c.T v ↔ (c.e v).isSome

end Calculus
