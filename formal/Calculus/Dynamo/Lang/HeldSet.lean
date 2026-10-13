import Calculus.Dynamo.Lang.Soundness

variable {α : Calculus.Table}

/-!
# The judgement's held set is the denotation's

`typed_TSub` puts the denotation's held set inside the judgement's. `typed_T_eq` is the other
direction, so the two are one set (`typed_T_identity`). `opaque` holds every value, at both.
-/

namespace Calculus

open Alg (Body.fields_mk Body.wild_mk Body.at_mk Term.depth)

/-! ## At every rule

The four list and table helpers the rules need stay beside their converses in `Soundness.lean`.

So `term_depth_wf` has users in more than one module, for the reason above. No document carries
a count of them.
-/

-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- **The judgement's held set is inside the denotation's** — `typed_TSub` the other way.

    This file names this claim (A). The statement is `typed_TSub`'s mirror and recurses the
    same way.
    Every rule closes: the ground rules and `literal` are `exact hv`, the two
    containers and the four wrappers reduce past their constructor, `opaque` holds every
    value, and `set` recurses into its element. Only four rules need anything new, and each needs the
    converse of a helper of the other direction.

    **What this does *not* say is `T = dom(e)`**, which is a different claim. Reading (A) as (B) is the mistake the specification's row made. -/
theorem typed_T_eq : ∀ {t T μ}, Typed α t T μ → ∀ v, T v → (denote α t).T v
  | t, T, μ, h, v, hv => by
    cases h with
    | base _ => exact hv
    -- the carrier is gated, so the rule's `HLit k x` and the denotation's are one
    -- expression
    | literal _ _ => exact hv
    | never => exact hv
    | opaq => trivial
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
    | @held t' I' μ' P k₀ k h' => exact ⟨typed_T_eq h' _ hv.1, hv.2⟩
    | @refine t' T' μ' q qA h' => exact ⟨typed_T_eq h' v hv.1, hv.2⟩
    | @object body bind R μs hfields hrest =>
      cases body with | mk fields ff wild =>
      simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at hfields hrest hv ⊢
      obtain ⟨keys, f, rfl, hreq, hall⟩ := hv
      refine ⟨⟨keys, f⟩, rfl, Alg.slotT_all_iff.mpr ⟨fun k hk hkk => ?_, ?_⟩⟩
      · -- an absent declared name is `optional`: a required one is present
        rw [MapOf.at_of_mem (m := (⟨fields, fun k => fieldSem α (ff k)⟩ : MapOf FieldSem)) ⟨k, hk⟩]
        match hc : ff ⟨k, hk⟩ with
        | .optional t' => simp only [hc]; rfl
        | .req t' =>
          refine absurd (hreq ⟨k, hk⟩ (TypedField.true_of_not_optional (hfields ⟨k, hk⟩) ?_)) hkk
          intro t'' hc'
          rw [hc] at hc'
          exact nomatch hc'
        | .fill t' v' =>
          -- the judgement has no rule for a fill
          have hty := hfields ⟨k, hk⟩
          rw [hc] at hty
          cases hty
      · intro k
        have hentry := hall k
        by_cases hk : k.1 ∈ fields
        · rw [dif_pos hk] at hentry
          simp only [objEntryT, MapOf.at_of_mem (m := (⟨fields, fun k => fieldSem α (ff k)⟩ :
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

/-- **The judgement `⊢ c : T ⇝ μ` names the denotation's held set exactly**, at every rule.

    So the index is a description and carries nothing the pair does not. It stays anyway:
    the rules are the model's transcription of the typing rules, and a judgement whose held set is spelled
    `(denote t).T` cannot be read against the document it transcribes. What the identity buys
    is that the reading is checked rather than advertised. -/
theorem typed_T_identity {t T μ} (h : Typed α t T μ) (v : Value) : (denote α t).T v ↔ T v :=
  ⟨Alg.typed_TSub h v, typed_T_eq h v⟩

/-! ## Which identity? The specification's row is two of them

* **(A)** `(denote t).T = T` for a derivable `⊢ t : T ⇝ μ`, which `typed_T_identity` proves
  at every rule. It is the half `typed_TSub` leaves.
* **(B)** `T = dom(e)` — what makes `: T` an honest index rather than an upper bound.
  `Carrier.domE` is its other half.

The specification's row asserts (A) and then justifies it with a sentence about (B). (A) is not false at
`union`; it is definitional — and it is proved everywhere else too. Reading a proof of (A) as a claim about (B) is the mistake the row made, and the reason
both are named here. -/

/-- **(A) at a union is definitional.** `altCodec`'s held set *is* the union of its options'
    — no premise, nothing to prove. So the union case of (A) is exactly the options'
    (A), and the specification's "false for `union`" cannot be about this claim. -/
theorem altCodec_T (os : List Codec) (μA : Option Member) (v : Value) :
    (altCodec os μA).T v ↔ ∃ o ∈ os, o.T v := Iff.rfl

end Calculus
