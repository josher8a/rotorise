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

/-! ## Inclusion lemmas, one per combinator -/

section Combinators
variable {V M : Type}

/-- Inclusion of graphs is transitive. -/
theorem sub_trans {c d u : Codec V M} (h : Sub c d) (h' : Sub d u) : Sub c u :=
  fun o x y hxy => h' o x y (h o x y hxy)

/-- A union of codecs below `u` is below `u`, because the selector returns the answer of one
    option. -/
theorem sub_altCodec {os : List (Codec V M)} {u : Codec V M} (h : ∀ o ∈ os, Sub o u)
    (μ : Option M) : Sub (altCodec os μ) u := fun o x y hxy =>
  let ⟨c, hc, _, hcy⟩ := altCodec_admits hxy
  h c hc o x y hcy

/-- A zipped traversal at the orientation `o` whose every row codec is below `u` is a traversal
    of `u` at `o`. -/
theorem forall₂_zip (o : Orient) {u : Codec V M} :
    ∀ (ds : List (Codec V M)) (xs : List (V)) (ys : List (V)),
    ds.length = xs.length → (∀ c ∈ ds, Sub c u) →
    List.Forall₂ (fun (cx : Codec V M × V) y => cx.1.f o cx.2 = some y) (ds.zip xs) ys →
    List.Forall₂ (fun x y => u.f o x = some y) xs ys
  | [], [], _, _, _, h => by cases h; exact .nil
  | d :: ds, x :: xs, y :: ys, hl, hd, .cons h1 h2 =>
      .cons ((hd d (by simp)) o _ _ h1)
        (forall₂_zip o ds xs ys (by simpa using hl) (fun c hc => hd c (by simp [hc])) h2)
  | [], _ :: _, _, hl, _, _ => nomatch hl
  | _ :: _, [], _, hl, _, _ => nomatch hl
  | _ :: _, _ :: _, [], _, _, h => nomatch h

/-- A list whose every slot is below a top that acts as the list former is below the top. -/
theorem sub_listCodec {member : V → M} {sL : Summand (List V) V M member} {u : Codec V M}
    (hu : ∀ o vs, u.f o (sL.p.into vs) = (traverse (u.f o) vs).map sL.p.into)
    {pre suf : List (Codec V M)} {sp : Option (Codec V M)}
    (hpre : ∀ c ∈ pre, Sub c u) (hsp : ∀ c ∈ sp, Sub c u) (hsuf : ∀ c ∈ suf, Sub c u) :
    Sub (listCodec sL pre sp suf) u := by
  have hrow : ∀ n ds, slotsL pre sp suf n = some ds → ∀ c ∈ ds, Sub c u := fun n ds h c hc => by
    rcases slotsL_mem pre sp suf n ds h c hc with h1 | h1 | h1
    · exact hpre c h1
    · exact hsp c h1
    · exact hsuf c h1
  intro o v a he
  obtain ⟨vs, as, hv, hE, rfl⟩ := carried_f.mp he
  simp only [alignL, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hE
  obtain ⟨ps, ⟨ds, hds, rfl⟩, ht⟩ := hE
  rw [sL.p.into_out hv, hu, traverse_eq_some.mpr (forall₂_zip o ds vs as
    (slotsL_length _ _ _ _ _ hds) (hrow _ _ hds) (traverse_eq_some.mp ht))]
  rfl

/-- An object with no fill whose every entry codec is below a top that acts as the map former
    is below the top. -/
theorem sub_objectCodec {member : V → M} {sM : Summand (MapOf V) V M member} {u : Codec V M}
    (hu : ∀ o (m : MapOf V), u.f o (sM.p.into m) =
      (funImage fun k => u.f o (m.get k)).map fun g => sM.p.into ⟨m.keys, g⟩)
    {sems : MapOf (FieldSem V M)} {rest : RestSem V M} (hnf : noFill sems = true)
    (hf : ∀ k, Sub (sems.2 k).codec u) (hw : ∀ c ∈ rcOf rest, Sub c u) :
    Sub (objectCodec sM sems rest) u := by
  intro o v a he
  obtain ⟨x, y, hv, hE, rfl⟩ := carried_f.mp he
  -- a present name: its entry goes through the top
  have hk : ∀ k : {k // k ∈ x.keys}, ∃ w, u.f o (x.get k) = some w ∧ y.at k.1 = some w := by
    intro k
    have h := objAt_at hE k.1
    rw [MapOf.at_of_mem k] at h
    simp only [liftTable, Option.map_eq_some_iff] at h
    obtain ⟨w, hcw, hyw⟩ := h
    obtain ⟨c, hc, hce⟩ := Option.bind_eq_some_iff.mp hcw
    exact ⟨w, (entryCodec_of (Q := fun c => Sub c u) hf hw hc) o _ _ hce, hyw.symm⟩
  have hs : ∀ k : {k // k ∈ x.keys}, (u.f o (x.get k)).isSome := fun k => by
    obtain ⟨w, hw', -⟩ := hk k; rw [hw']; rfl
  rw [sM.p.into_out hv, hu, funImage_eq (f := fun k => (u.f o (x.get k)).get (hs k))
    (fun k => (Option.some_get _).symm)]
  -- every other name is absent on both sides
  refine congrArg (fun m => some (sM.p.into m)) (MapOf.ext_at fun k => ?_)
  rcases Decidable.em (k ∈ x.keys) with hkx | hkx
  · obtain ⟨w, hw', hyw⟩ := hk ⟨k, hkx⟩
    rw [hyw]
    simp only [MapOf.at, dif_pos hkx, hw', Option.get_some]
  · have h := objAt_at hE k
    rw [MapOf.at_none hkx] at h
    rw [liftTable_none (noFill_at hnf k) h]
    simp only [MapOf.at, dif_neg hkx]

end Combinators

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

/-- The laws of the top that the held-free theory reads: each primitive is below the top, and
    the set lift keeps a codec below the top. The top is the identity, so it acts as the list
    and map formers with no law of the universe (`top_list`, `top_map`). -/
class TopLaws (S : Syn) [Sem S] : Prop where
  ground : ∀ g, Sub (Syn.ground g) (Syn.top (S := S))
  set : ∀ L ∈ Mean.set (B := S.sig), ∀ c : S.C, Sub c (Syn.top (S := S)) →
    Sub (L.lift c) (Syn.top (S := S))
  /-- A set over a restriction of the top acts, at each orientation, where a set over an element
      that acts less acts. The view of a set reads this law. -/
  set_mono : ∀ L ∈ Mean.set (B := S.sig), ∀ (o : Orient) (c d : S.C), Sub d (Syn.top (S := S)) →
    (∀ w, (c.f o w).isSome = true → (d.f o w).isSome = true) →
    ∀ x, ((L.lift c).f o x).isSome = true → ((L.lift d).f o x).isSome = true

/-- **The laws of the top read no orientation**, so the dual universe has the laws of the
    universe. -/
instance TopLaws.op [h : TopLaws S] : TopLaws S.op := ⟨h.ground, h.set, h.set_mono⟩

variable {β : Table S.op}

/-- The top acts as a list former: element by element. -/
theorem top_list {o : Orient} (into : List S.V → S.V) (vs : List S.V) :
    (Syn.top (S := S)).f o (into vs) = (traverse ((Syn.top (S := S)).f o) vs).map into :=
  (congrArg (Option.map into) (traverse_some vs)).symm

/-- The top acts as a map former: entry by entry. -/
theorem top_map {o : Orient} (into : MapOf S.V → S.V) (m : MapOf S.V) :
    (Syn.top (S := S)).f o (into m) =
      (funImage fun k => (Syn.top (S := S)).f o (m.get k)).map fun g => into ⟨m.keys, g⟩ :=
  (congrArg (Option.map fun g => into ⟨m.keys, g⟩) (funImage_eq (g := fun k => (Syn.top (S := S)).f o (m.get k))
    (fun _ => rfl))).symm

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
