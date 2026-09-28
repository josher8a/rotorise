import Calculus.Dynamo.Lang.Soundness

variable {α : Calculus.Table}

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

open Alg (Body.fields_mk Body.wild_mk Body.at_mk Term.depth)

/-! ## `T` as an identity, for `opaque`

With `HOpaque` corrected, the converse of `opaq_TSub` goes through: everything `HOpaque` admits,
`opaque` writes. `opaque`'s held set is its write domain (`muCodec`), so the identity is one
induction over `HOpaque`, and each container case reads `opaque` through itself at the fixed
point (`Ωe_arr`, `Ωe_map`, `Ωe_strSet` and the other two sets). -/

/-- Everything `HOpaque` holds, `opaque` writes. -/
theorem hopaque_e {v : Value} (h : HOpaque v) : (Ω.e v).isSome = true := by
  induction h with
  | str s => rfl
  | bool b => rfl
  | bin b => rfl
  | null => rfl
  | num d => rfl
  | strSet S _ _ =>
    rw [Ωe_strSet, encSet_congr (c := Ω) (d := stringCodec) (fun x _ => rfl)]
    exact encSet_isSome_of lawful_stringCodec.core (μ₀ := .S) rfl (fun _ _ h => Value.str.inj h)
      (fun _ _ => rfl) (fun _ _ _ ha => lawful_stringCodec.writes rfl ha)
  | numSet S _ _ =>
    rw [Ωe_numSet, encSet_congr (c := Ω) (d := numberCodec) (fun x _ => rfl)]
    exact encSet_isSome_of lawful_numberCodec.core (μ₀ := .N) rfl (fun _ _ h => Value.num.inj h)
      (fun _ _ => rfl) (fun _ _ _ ha => lawful_numberCodec.writes rfl ha)
  | binSet S _ _ =>
    rw [Ωe_binSet, encSet_congr (c := Ω) (d := binaryCodec) (fun x _ => rfl)]
    exact encSet_isSome_of lawful_binaryCodec.core (μ₀ := .B) rfl (fun _ _ h => Value.bin.inj h)
      (fun _ _ => rfl) (fun _ _ _ ha => lawful_binaryCodec.writes rfl ha)
  | arr vs _ ih =>
    rw [Ωe_arr, Option.isSome_map]
    exact traverse_isSome_of_all ih
  | map keys f _ ih =>
    rw [Ωe_map, Option.isSome_map]
    exact funImage_isSome_iff.mpr ih

/-- **`HOpaque` *is* `opaque`'s held set.** The row §6 called unproved, and unprovable in
    the fuel encoding, closed for the case it said bites hardest. -/
theorem opaq_T_identity (v : Value) : Ω.T v ↔ HOpaque v :=
  ⟨opaq_TSubω v, hopaque_e⟩

/-! ## …and in general, at every rule

`opaq_T_identity` closes (A) at the constructor §3 says it bites hardest at. The general
statement lives **here rather than beside `typed_TSub`**, which is where its mirror is and
where it belongs by shape: its `opaque` case is `opaq_T_identity`, and the two theorems that
reach `opaque` stay together. The four list and table helpers the other rules need stay beside
their converses in `Soundness.lean`.

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
    iff, and `set` recurses into its element. Only four rules need anything new, and each needs the
    converse of a helper that was already here for the other direction.

    **What this does *not* say is `T = dom(e)`**, which is a different claim, proved by
    `typed_T_adm` (`Laminar.lean`). Reading (A) as (B) is the mistake §6's row made. -/
theorem typed_T_eq : ∀ {t T μ}, Typed α t T μ → ∀ v, T v → (denote α t).T v
  | t, T, μ, h, v, hv => by
    cases h with
    | base _ => exact hv
    -- the carrier is gated, so the rule's `HLit k ls` and the denotation's are one
    -- expression — the same fact that removed `typed_TSub`'s five-way split here
    | literal _ _ => exact hv
    | never => exact hv
    | opaq => exact (opaq_T_identity v).mpr hv
    -- a closed variable holds nothing, and a `mu`'s index is its codec's held set
    | var _ => exact False.elim hv
    | mu _ _ => exact hv
    | @set t' T' μ' h' =>
      rcases hv with ⟨S, rfl, hall⟩ | ⟨S, rfl, hall⟩ | ⟨S, rfl, hall⟩ <;>
        exact fun x hx => typed_T_eq h' _ (hall x hx)
    | @list pre Tpre sp Tsp suf Tsuf hp hs hf =>
      obtain ⟨vs, rfl, hall⟩ := hv
      rw [denote_list, denoteList_eq, denoteOpt_eq, denoteList_eq]
      exact ⟨vs, rfl, alignL_T_of_HTupleL hp hs hf
        (fun t' _ _ _ hty w hw => typed_T_eq hty w hw)
        (fun t' _ _ _ hty w hw => typed_T_eq hty w hw)
        (fun t' _ _ _ hty w hw => typed_T_eq hty w hw) hall⟩
    | @held t' I' μ' P PA k kA h' => exact ⟨typed_T_eq h' ((α.word k).1 v) hv.1, hv.2⟩
    | @refine t' T' μ' q qA h' => exact ⟨typed_T_eq h' v hv.1, hv.2⟩
    | @object body bind R μs hfields hrest =>
      cases body with | mk fields ff wild =>
      simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at hfields hrest hv ⊢
      obtain ⟨keys, f, rfl, hreq, hall⟩ := hv
      refine ⟨⟨keys, f⟩, rfl, ?_, ?_⟩
      · refine valPresentB_of fun k fs hm hno => ?_
        obtain ⟨hk, rfl⟩ := MapOf.at_eq_some.mp hm
        refine hreq ⟨k, hk⟩ (TypedField.true_of_not_optional (hfields ⟨k, hk⟩) ?_)
        intro t' hc
        exact hno (denote α t') (congrArg (fieldSem α) hc)
      · intro k
        have hentry := hall k
        by_cases hk : k.1 ∈ fields
        · rw [dif_pos hk] at hentry
          simp only [objEntryT,
            MapOf.at_of_mem (m := (⟨fields, fun k => fieldSem α (ff k)⟩ :
              MapOf FieldSem)) ⟨k.1, hk⟩]
          obtain ⟨t', hty', hshape⟩ := TypedField.term (α := α) (hfields ⟨k.1, hk⟩)
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
            exact ⟨denote α t', rfl, typed_T_eq hty' _ hT''⟩
    | @union opts Ts μs h' =>
      obtain ⟨T', hT', hTv⟩ := hv
      obtain ⟨tx, htx, hd⟩ :=
        unionT_of_mem (α := α) h' (fun t' _ _ _ hty w hw => typed_T_eq hty w hw) v T' hT' hTv
      simp only [denote_rows, denoteList_eq]
      refine ⟨denote α tx, ?_, ?_⟩
      · simp only [List.mem_map]; exact ⟨tx, htx, rfl⟩
      · exact hd
termination_by t _ _ _ _ => Term.depth t
decreasing_by term_depth_wf

/-- **§3's `⊢ c : T ⇝ μ` names the denotation's held set exactly**, at every rule.

    So the index is a description and carries nothing the pair does not. It stays anyway:
    the rules are the model's transcription of §3, and a judgement whose held set is spelled
    `(denote t).T` cannot be read against the document it transcribes. What the identity buys
    is that the reading is now checked rather than advertised. -/
theorem typed_T_identity {t T μ} (h : Typed α t T μ) (v : Value) : (denote α t).T v ↔ T v :=
  ⟨Alg.typed_TSub h v, typed_T_eq h v⟩

/-! ## Which identity? §6's row is two of them

* **(A)** `(denote t).T = T` for a derivable `⊢ t : T ⇝ μ` — `HOpaque` *is* `opaque`'s held
  set, which `opaq_T_identity` proves at `opaque` and `typed_T_identity` now proves at every
  rule. **Closed**, and it was the half `typed_TSub` left.
* **(B)** `T = dom(e)` — what makes `: T` an honest index rather than an upper bound.
  `Carrier.domE` is its other half.

§6's row asserted (A) and then justified it with a sentence about (B). (A) is not false at
`union`; it is definitional — and it is now proved everywhere else too. **(B) holds at every
derivable term whose obligations hold** by `typed_T_adm` (`Laminar.lean`): a union writes wherever
one of its options writes, and a set reads its obligations. Reading a proof of (A) as a claim about (B) is the mistake the row made, and the reason
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
