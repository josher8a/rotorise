import Calculus.Lang.Sound

/-!
# Held-free terms are restrictions of the top, for every universe

A term with no `held` does not change the carrier. Each combinator either restricts its subterm
or composes subterms through the structure that the top itself uses, so the write graph and the
read graph of a held-free term lie inside the graphs of the top. `sub_denote` proves the two
inclusions by one mutual induction over `Term`, `Body`, `ObjectSlot`, the list and the option.

`TopLaws` states what the induction reads of the universe: each primitive is below the top, and
the set lift keeps a codec below the top. A universe supplies the laws as an instance. Neither
soundness nor the judgement reads these laws, so they sit outside `Sem`. The top is the identity,
which is canonical, so two held-free terms are compatible (`compat_of_HF`).
-/

namespace Calculus.Alg

/-! ## Held-free terms -/

section HeldFree
variable {S : Syn}

/-- A term is **held-free** when no `held` occurs in the term: the test `hasHeld` answers
    `false`. A held-free term does not change the carrier, so the term is a restriction of the
    top. The test is the definition, so a closed term is shown held-free by `rfl`. -/
abbrev HF (t : Term S) : Prop := hasHeld t = false
/-- A body is held-free when each slot and the open block are held-free. -/
abbrev HFB (b : Body S) : Prop := hasHeldB b = false
/-- A slot is held-free when the slot's term is held-free. -/
abbrev HFS (s : ObjectSlot S) : Prop := hasHeldS s = false
/-- Each term of the list is held-free. -/
abbrev HFL (ts : List (Term S)) : Prop := hasHeldL ts = false
/-- The optional term is held-free where the term is present. -/
abbrev HFO (o : Option (Term S)) : Prop := hasHeldO o = false

variable [Sem S] {α : Table S}

variable {β : Table S.op}

mutual
/-- **Confluence at a context.** A held-free term whose free variables are safe in `ctx` denotes a
    restriction of the top, over an environment whose safe entries are restrictions of the top. -/
theorem sub_denoteSafe [TopLaws S] : ∀ (t : Term S) (ctx : Nat → Bool), HF t → t.safe ctx = true →
    ∀ ρ : List S.C, (∀ i, ctx i = true → Sub (envAt ρ i) (Syn.top (S := S))) → Sub (denote α β t ρ) (Syn.top (S := S))
  | .prim g, _, _, _, _, _ => TopLaws.ground g
  | .opaq, _, _, _, _, _ => fun _ _ _ h => h
  | .never, _, _, _, _, _ => sub_empty
  | .var i, _, _, hs, _, henv => henv i hs
  | .set t, ctx, h, hs, ρ, henv => by
      simp only [denote, denoteAbs]
      cases hL : Mean.set (B := S.sig) with
      | none => exact sub_empty
      | some L => exact TopLaws.set L hL _ (sub_denoteSafe t ctx h hs ρ henv)
  -- each stage is a restriction by the body's case at the stage before, and the binder's entry is
  -- safe because each stage is below the top
  | .mu b, ctx, h, hs, ρ, henv => by
      have hs' : ∀ n, Sub (muStage (fun c => denote α β b (c :: ρ)) n) (Syn.top (S := S)) := fun n => by
        induction n with
        | zero => exact sub_empty
        | succ n ih =>
          exact sub_denoteSafe b (ctxPush true ctx) h hs (_ :: ρ) fun i hi => match i, hi with
            | 0, _ => ih
            | i + 1, hi => henv i hi
      exact fun o x y h => hs' _ o x y h
  | .held _ _ _ _ _, _, h, _, _, _ => nomatch h
  | .refine t _ _, ctx, h, hs, ρ, henv =>
      sub_trans (sub_refine2_self _ _ _) (sub_denoteSafe t ctx h hs ρ henv)
  | .legacy _ _, _, h, _, _, _ => nomatch h
  | .list pre sp suf, ctx, h, hs, ρ, henv => by
      simp only [HF, hasHeld, Bool.or_eq_false_iff] at h
      simp only [Term.safe, Bool.and_eq_true] at hs
      simp only [denote, denoteAbs]
      cases hL : Mean.list (B := S.sig) with
      | none => exact sub_empty
      | some L =>
        exact sub_listCodec (fun _ => top_list L.p.into)
          (sub_denoteListSafe pre ctx h.1.1 hs.1.1 ρ henv) (sub_denoteOptSafe sp ctx h.1.2 hs.1.2 ρ henv)
          (sub_denoteListSafe suf ctx h.2 hs.2 ρ henv)
  | .object b, ctx, h, hs, ρ, henv => sub_bodySafe b ctx h hs ρ henv
  | .union os, ctx, h, hs, ρ, henv => sub_altCodec (sub_denoteListSafe os ctx h hs ρ henv) _
/-- …at a body. -/
theorem sub_bodySafe [TopLaws S] : ∀ (b : Body S) (ctx : Nat → Bool), HFB b → b.safe ctx = true →
    ∀ ρ : List S.C, (∀ i, ctx i = true → Sub (envAt ρ i) (Syn.top (S := S))) → Sub (bodySem α β b ρ) (Syn.top (S := S))
  | .mk fields f w, ctx, h, hs, ρ, henv => by
      simp only [HFB, hasHeldB, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_exists] at h
      simp only [Body.safe, Bool.and_eq_true, decide_eq_true_eq] at hs
      simp only [bodySem, bodySemAbs]
      cases hF : Mean.map (B := S.sig) with
      | none => exact sub_empty
      | some F =>
        -- a fill is held, so a held-free body holds none
        have hnf : noFill (⟨fields, fun k => fieldSem α β (f k) ρ⟩ : MapOf _) = true :=
          decide_eq_true fun k => by
            have := h.1 k
            match hk : f k with
            | .req _ | .optional _ | .fill _ _ =>
              simp_all [hasHeldS, fieldSem, fieldSemAbs, FieldSem.isFill]
        exact sub_objectCodec (fun _ => top_map F.p.into) hnf
          (fun k => sub_slotSafe (f k) ctx (Bool.eq_false_iff.mpr (h.1 k)) (hs.1 k) ρ henv)
          (sub_wildSafe w ctx h.2 hs.2 ρ henv)
/-- …at a slot. -/
theorem sub_slotSafe [TopLaws S] : ∀ (s : ObjectSlot S) (ctx : Nat → Bool), HFS s → s.safe ctx = true →
    ∀ ρ : List S.C, (∀ i, ctx i = true → Sub (envAt ρ i) (Syn.top (S := S))) → Sub (fieldSem α β s ρ).codec (Syn.top (S := S))
  | .req t, ctx, h, hs, ρ, henv => sub_denoteSafe t ctx h hs ρ henv
  | .optional t, ctx, h, hs, ρ, henv => sub_denoteSafe t ctx h hs ρ henv
  | .fill _ _, _, h, _, _, _ => nomatch h
/-- …at an open block. -/
theorem sub_wildSafe [TopLaws S] : ∀ (w : Option (Term S)) (ctx : Nat → Bool), HFO w →
    Term.safeO ctx w = true → ∀ ρ : List S.C, (∀ i, ctx i = true → Sub (envAt ρ i) (Syn.top (S := S))) →
      ∀ c ∈ rcOf (wildSem α β w ρ), Sub c (Syn.top (S := S))
  | none, _, _, _, _, _ => fun _ hc => nomatch hc
  | some t, ctx, h, hs, ρ, henv => fun c hc => by cases hc; exact sub_denoteSafe t ctx h hs ρ henv
/-- …at a list of terms. -/
theorem sub_denoteListSafe [TopLaws S] : ∀ (ts : List (Term S)) (ctx : Nat → Bool), HFL ts →
    Term.safeL ctx ts = true → ∀ ρ : List S.C, (∀ i, ctx i = true → Sub (envAt ρ i) (Syn.top (S := S))) →
      ∀ c ∈ denoteList α β ts ρ, Sub c (Syn.top (S := S))
  | [], _, _, _, _, _ => fun _ hc => nomatch hc
  | t :: ts, ctx, h, hs, ρ, henv => fun c hc => by
      simp only [HFL, hasHeldL, Bool.or_eq_false_iff] at h
      simp only [Term.safeL, Bool.and_eq_true] at hs
      rcases List.mem_cons.mp hc with rfl | hc
      · exact sub_denoteSafe t ctx h.1 hs.1 ρ henv
      · exact sub_denoteListSafe ts ctx h.2 hs.2 ρ henv c hc
/-- …at an optional term. -/
theorem sub_denoteOptSafe [TopLaws S] : ∀ (o : Option (Term S)) (ctx : Nat → Bool), HFO o →
    Term.safeO ctx o = true → ∀ ρ : List S.C, (∀ i, ctx i = true → Sub (envAt ρ i) (Syn.top (S := S))) →
      ∀ c ∈ denoteOpt α β o ρ, Sub c (Syn.top (S := S))
  | none, _, _, _, _, _ => fun _ hc => nomatch hc
  | some t, ctx, h, hs, ρ, henv => fun c hc => by cases hc; exact sub_denoteSafe t ctx h hs ρ henv
end

/-- **Confluence.** The denotation of a held-free term is a restriction of the top, on both
    halves, over an environment of restrictions of the top: the context in which every variable is
    safe. -/
theorem sub_denoteIn [TopLaws S] (t : Term S) (h : HF t) (ρ : List S.C)
    (henv : ∀ i, Sub (envAt ρ i) (Syn.top (S := S))) : Sub (denote α β t ρ) (Syn.top (S := S)) :=
  sub_denoteSafe t (fun _ => true) h (safe_of_all t _ fun _ => rfl) ρ fun i _ => henv i

/-- **The stages of a held-free binder are below the top**, over an environment whose safe entries
    are below the top, where the binder's free variables are safe. -/
theorem stage_subSafe [TopLaws S] {b : Term S} {ctx : Nat → Bool} (hb : hasHeld b = false)
    (hs : (Term.mu b).safe ctx = true) {ρ : List S.C}
    (henv : ∀ i, ctx i = true → Sub (envAt ρ i) (Syn.top (S := S))) :
    ∀ n, Sub (muStage (fun c => denote α β b (c :: ρ)) n) (Syn.top (S := S))
  | 0 => sub_empty
  | n + 1 => sub_denoteSafe b (ctxPush true ctx) hb hs (_ :: ρ) fun i hi => match i, hi with
      | 0, _ => stage_subSafe hb hs henv n
      | i + 1, hi => henv i hi

/-- **Confluence**, closed: the denotation of a held-free term is a restriction of the top. -/
theorem sub_denote [TopLaws S] (t : Term S) (h : HF t) : Sub (denote α β t) (Syn.top (S := S)) :=
  sub_denoteIn t h [] fun _ => sub_empty

/-- **Held-free lawful terms are pairwise compatible**: the common bound is the top, and the top
    is the identity, which is canonical. -/
theorem compat_of_HF [TopLaws S] {s t : Term S} (hs : HF s) (ht : HF t)
    (hlt : Lawful Mean.mem (denote α β t)) : Compat (denote α β s) (denote α β t) :=
  compat_of_common_bound' (sub_denote s hs) (sub_denote t ht) canon_idCodec hlt

end HeldFree

end Calculus.Alg
