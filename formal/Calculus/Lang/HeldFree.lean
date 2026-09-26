import Calculus.Lang.Sound

/-!
# Held-free terms are restrictions of the top, for every universe

A term with no `held` does not change the carrier. Each combinator either restricts its subterm
or composes subterms through the structure that the top itself uses, so the write graph and the
read graph of a held-free term lie inside the graphs of the top. `sub_denote` proves the two
inclusions by one mutual induction over `Term`, `Body`, `ObjectSlot`, the list and the option.

`TopLaws` states what the induction reads of the top, former by former. Neither soundness nor the
judgement reads these laws, so they sit outside `Sem`. `compat_of_HF` adds that the top is
canonical: two held-free terms below one canonical codec are compatible.
-/

namespace Calculus.Alg

/-! ## Inclusion lemmas, one per combinator -/

section Combinators
variable {V A M : Type}

/-- Inclusion of graphs is transitive. -/
theorem sub_trans {c d u : Codec V A M} (h : Sub c d) (h' : Sub d u) : Sub c u :=
  ⟨fun _ _ he => h'.1 _ _ (h.1 _ _ he), fun _ _ hp => h'.2 _ _ (h.2 _ _ hp)⟩

/-- The empty codec is below every codec. -/
theorem sub_empty {u : Codec V A M} : Sub Codec.empty u :=
  ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

/-- A union of codecs below `u` is below `u`, because the selector returns the answer of one
    option. -/
theorem sub_altCodec {os : List (Codec V A M)} {u : Codec V A M} (h : ∀ o ∈ os, Sub o u)
    (μ : Option M) : Sub (altCodec os μ) u := by
  refine ⟨fun v a he => ?_, fun a v hp => ?_⟩
  · obtain ⟨o, ho, -, he⟩ := select_admits he; exact (h o ho).1 _ _ he
  · obtain ⟨o, ho, -, hp⟩ := select_admits hp; exact (h o ho).2 _ _ hp

/-- A zipped traversal whose every row codec is below `u` is a traversal of `u`. -/
theorem forall₂_zip_e {u : Codec V A M} : ∀ (ds : List (Codec V A M)) (vs : List V) (as : List A),
    ds.length = vs.length → (∀ c ∈ ds, Sub c u) →
    List.Forall₂ (fun (cv : Codec V A M × V) a => cv.1.e cv.2 = some a) (ds.zip vs) as →
    List.Forall₂ (fun v a => u.e v = some a) vs as
  | [], [], _, _, _, h => by cases h; exact .nil
  | d :: ds, v :: vs, a :: as, hl, hd, .cons h1 h2 =>
      .cons ((hd d (by simp)).1 _ _ h1)
        (forall₂_zip_e ds vs as (by simpa using hl) (fun c hc => hd c (by simp [hc])) h2)
  | [], _ :: _, _, hl, _, _ => nomatch hl
  | _ :: _, [], _, hl, _, _ => nomatch hl
  | _ :: _, _ :: _, [], _, _, h => nomatch h

/-- …and the same on the read side. -/
theorem forall₂_zip_p {u : Codec V A M} : ∀ (ds : List (Codec V A M)) (as : List A) (vs : List V),
    ds.length = as.length → (∀ c ∈ ds, Sub c u) →
    List.Forall₂ (fun (ca : Codec V A M × A) v => ca.1.p ca.2 = some v) (ds.zip as) vs →
    List.Forall₂ (fun a v => u.p a = some v) as vs
  | [], [], _, _, _, h => by cases h; exact .nil
  | d :: ds, a :: as, v :: vs, hl, hd, .cons h1 h2 =>
      .cons ((hd d (by simp)).2 _ _ h1)
        (forall₂_zip_p ds as vs (by simpa using hl) (fun c hc => hd c (by simp [hc])) h2)
  | [], _ :: _, _, hl, _, _ => nomatch hl
  | _ :: _, [], _, hl, _, _ => nomatch hl
  | _ :: _, _ :: _, [], _, _, h => nomatch h

/-- A list whose every slot is below a top that acts as the list former is below the top. -/
theorem sub_listCodec {pV : Ctor (List V) V} {pA : Ctor (List A) A} {μL : M} {u : Codec V A M}
    (hue : ∀ vs, u.e (pV.into vs) = (traverse u.e vs).map pA.into)
    (hup : ∀ as, u.p (pA.into as) = (traverse u.p as).map pV.into)
    {pre suf : List (Codec V A M)} {sp : Option (Codec V A M)}
    (hpre : ∀ c ∈ pre, Sub c u) (hsp : ∀ c ∈ sp, Sub c u) (hsuf : ∀ c ∈ suf, Sub c u) :
    Sub (listCodec pV pA μL pre sp suf) u := by
  have hrow : ∀ n ds, slotsL pre sp suf n = some ds → ∀ c ∈ ds, Sub c u := fun n ds h c hc => by
    rcases slotsL_mem pre sp suf n ds h c hc with h1 | h1 | h1
    · exact hpre c h1
    · exact hsp c h1
    · exact hsuf c h1
  refine ⟨fun v a he => ?_, fun a v hp => ?_⟩
  · obtain ⟨vs, as, hv, hE, rfl⟩ := carried_e.mp he
    simp only [alignL, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hE
    obtain ⟨ps, ⟨ds, hds, rfl⟩, ht⟩ := hE
    rw [pV.into_out hv, hue, traverse_eq_some.mpr (forall₂_zip_e ds vs as
      (slotsL_length _ _ _ _ _ hds) (hrow _ _ hds) (traverse_eq_some.mp ht))]
    rfl
  · obtain ⟨as, vs, ha, hD, rfl⟩ := carried_p.mp hp
    simp only [alignL, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hD
    obtain ⟨ps, ⟨ds, hds, rfl⟩, ht⟩ := hD
    rw [pA.into_out ha, hup, traverse_eq_some.mpr (forall₂_zip_p ds as vs
      (slotsL_length _ _ _ _ _ hds) (hrow _ _ hds) (traverse_eq_some.mp ht))]
    rfl

/-- A key-set equation transports a keyed read. -/
theorem funImage_mapOf_congr {β γ : Type} (into : MapOf β → γ) {S T : Finset String} (hS : S = T)
    {g : {k // k ∈ S} → Option β} {g' : {k // k ∈ T} → Option β}
    (hg : ∀ (k : String) (h : k ∈ S) (h' : k ∈ T), g ⟨k, h⟩ = g' ⟨k, h'⟩) :
    (funImage g).map (fun d => into ⟨S, d⟩) = (funImage g').map (fun d => into ⟨T, d⟩) := by
  subst hS
  have himg : g = g' := funext fun k => hg k.1 k.2 k.2
  subst himg
  rfl

/-- An object whose every entry codec is below a top that acts as the map former is below the
    top. -/
theorem sub_objectCodec {mV : Ctor (MapOf V) V} {mA : Ctor (MapOf A) A} {μM : M}
    {u : Codec V A M}
    (hue : ∀ m : MapOf V, u.e (mV.into m) =
      (funImage fun k => u.e (m.get k)).map fun g => mA.into ⟨m.keys, g⟩)
    (hup : ∀ m : MapOf A, u.p (mA.into m) =
      (funImage fun k => u.p (m.get k)).map fun g => mV.into ⟨m.keys, g⟩)
    {sems : MapOf (FieldSem V A M)} {rest : RestSem V A M} (hnd : rest ≠ .drop)
    (hf : ∀ k, Sub (sems.2 k).codec u) (hw : ∀ c ∈ rcOf rest, Sub c u) :
    Sub (objectCodec mV mA μM sems rest) u := by
  refine ⟨fun v a he => ?_, fun a v hp => ?_⟩
  · obtain ⟨x, y, hv, hE, rfl⟩ := carried_e.mp he
    obtain ⟨-, g, hg, rfl⟩ := objWrite_eq.mp hE
    rw [mV.into_out hv, hue, funImage_eq (f := g) (fun k => ?_)]
    · rfl
    have hk := funImage_some hg k
    obtain ⟨c, hc, hce⟩ := Option.bind_eq_some_iff.mp hk
    exact (entryCodec_of (Q := fun c => Sub c u) hf hw hc).1 _ _ hce
  · obtain ⟨y, x, ha, hD, rfl⟩ := carried_p.mp hp
    obtain ⟨-, d, hd, rfl⟩ := objRead_eq.mp hD
    have hkeep : ∀ k, keepB rest sems k = true := by
      intro k; cases rest with
      | drop => exact absurd rfl hnd
      | refuse => rfl
      | codec _ => rfl
    have hS : y.1 = y.1.filter (keepB rest sems ·) :=
      (Finset.filter_eq_self.mpr fun k _ => by simpa using hkeep k).symm
    rw [mA.into_out ha, hup]
    rw [funImage_mapOf_congr mV.into hS
        (g' := fun k : {k // k ∈ y.1.filter (keepB rest sems ·)} =>
          (entryCodec sems (rcOf rest) k.1).bind
            (fun c => c.p (y.2 ⟨k.1, (Finset.mem_filter.mp k.2).1⟩))) (fun k h h' => ?_), hd]
    · rfl
    have hk := funImage_some hd ⟨k, h'⟩
    rw [hk]
    obtain ⟨c, hc, hcp⟩ := Option.bind_eq_some_iff.mp hk
    exact (entryCodec_of (Q := fun c => Sub c u) hf hw hc).2 _ _ hcp

end Combinators

/-! ## Held-free terms -/

section HeldFree
variable {S : Syn}

mutual
/-- A term is **held-free** when no `held` occurs in the term. A held-free term does not change
    the carrier, so the term is a restriction of the top. -/
def HF : Term S → Prop
  | .held _ _ _ _ => False
  | .refine t _ => HF t
  | .mu t => HF t
  | .list pre sp suf => HFL pre ∧ HFO sp ∧ HFL suf
  | .object b => HFB b
  | .union os => HFL os
  | .set t => HF t
  | .prim _ | .opaq | .never | .var _ => True
/-- A body is held-free when each slot and the open block are held-free. -/
def HFB : Body S → Prop
  | .mk _ f w => (∀ k, HFS (f k)) ∧ HFO w
/-- A slot is held-free when the slot's term is held-free. -/
def HFS : ObjectSlot S → Prop
  | .req t => HF t
  | .optional t => HF t
/-- Each term of the list is held-free. -/
def HFL : List (Term S) → Prop
  | [] => True
  | t :: ts => HF t ∧ HFL ts
/-- The optional term is held-free where the term is present. -/
def HFO : Option (Term S) → Prop
  | none => True
  | some t => HF t
end


/-- **The flags under one more binder**: `b` for the new variable, and `env` for the rest. -/
def flagsCons (b : Bool) (env : Nat → Bool) : Nat → Bool
  | 0 => b
  | i + 1 => env i

mutual
/-- **Whether a `held` can occur in the term, under one flag per variable.** The flag `env i`
    says whether the binder of `var i` holds a `held`. The flag of `mu b` is the test of `b` with
    its own variable at `false`: the variable adds no `held` of its own, so the flag is the least
    fixed point. Under the flags `fun _ => false` this is `HF` (`hasHeldUnder_of_HF`). -/
def hasHeldUnder (env : Nat → Bool) : Term S → Bool
  | .held _ _ _ _ => true
  | .var i => env i
  | .refine t _ => hasHeldUnder env t
  | .mu b => hasHeldUnder (flagsCons false env) b
  | .list pre sp suf => hasHeldUnderL env pre || hasHeldUnderO env sp || hasHeldUnderL env suf
  | .object b => hasHeldUnderB env b
  | .union os => hasHeldUnderL env os
  | .set t => hasHeldUnder env t
  | .prim _ | .opaq | .never => false
/-- …in a list. -/
def hasHeldUnderL (env : Nat → Bool) : List (Term S) → Bool
  | [] => false
  | t :: ts => hasHeldUnder env t || hasHeldUnderL env ts
/-- …in an optional term. -/
def hasHeldUnderO (env : Nat → Bool) : Option (Term S) → Bool
  | none => false
  | some t => hasHeldUnder env t
/-- …in a body. -/
def hasHeldUnderB (env : Nat → Bool) : Body S → Bool
  | .mk fs f w => decide (∃ k : {k // k ∈ fs}, hasHeldUnderS env (f k) = true) ||
      hasHeldUnderO env w
/-- …in a slot. -/
def hasHeldUnderS (env : Nat → Bool) : ObjectSlot S → Bool
  | .req t => hasHeldUnder env t
  | .optional t => hasHeldUnder env t
end

/-- Flags that are `false` at each variable stay so under a binder with the flag `false`. -/
theorem flagsCons_false {env : Nat → Bool} (h : ∀ i, env i = false) :
    ∀ i, flagsCons false env i = false
  | 0 => rfl
  | i + 1 => h i

mutual
/-- **A held-free term has no `held` under flags that are `false` at each variable.** -/
theorem hasHeldUnder_of_HF : ∀ t : Term S, HF t → ∀ env : Nat → Bool, (∀ i, env i = false) →
    hasHeldUnder env t = false
  | .held _ _ _ _, h, _, _ => h.elim
  | .var i, _, _, he => he i
  | .refine t _, h, env, he => hasHeldUnder_of_HF t h env he
  | .mu b, h, env, he => hasHeldUnder_of_HF b h _ (flagsCons_false he)
  | .list pre sp suf, ⟨h1, h2, h3⟩, env, he => by
      simp only [hasHeldUnder, Bool.or_eq_false_iff]
      exact ⟨⟨hasHeldUnderL_of_HFL pre h1 env he, hasHeldUnderO_of_HFO sp h2 env he⟩,
        hasHeldUnderL_of_HFL suf h3 env he⟩
  | .object (.mk fs f w), ⟨hf, hw⟩, env, he => by
      simp only [hasHeldUnder, hasHeldUnderB, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        not_exists]
      exact ⟨fun k => by rw [hasHeldUnderS_of_HFS (f k) (hf k) env he]; exact Bool.false_ne_true,
        hasHeldUnderO_of_HFO w hw env he⟩
  | .union os, h, env, he => hasHeldUnderL_of_HFL os h env he
  | .set t, h, env, he => hasHeldUnder_of_HF t h env he
  | .prim _, _, _, _ | .opaq, _, _, _ | .never, _, _, _ => rfl
/-- …in a list. -/
theorem hasHeldUnderL_of_HFL : ∀ ts : List (Term S), HFL ts → ∀ env : Nat → Bool,
    (∀ i, env i = false) → hasHeldUnderL env ts = false
  | [], _, _, _ => rfl
  | t :: ts, ⟨h1, h2⟩, env, he => by
      simp only [hasHeldUnderL, Bool.or_eq_false_iff]
      exact ⟨hasHeldUnder_of_HF t h1 env he, hasHeldUnderL_of_HFL ts h2 env he⟩
/-- …in an optional term. -/
theorem hasHeldUnderO_of_HFO : ∀ o : Option (Term S), HFO o → ∀ env : Nat → Bool,
    (∀ i, env i = false) → hasHeldUnderO env o = false
  | none, _, _, _ => rfl
  | some t, h, env, he => hasHeldUnder_of_HF t h env he
/-- …in a slot. -/
theorem hasHeldUnderS_of_HFS : ∀ s : ObjectSlot S, HFS s → ∀ env : Nat → Bool,
    (∀ i, env i = false) → hasHeldUnderS env s = false
  | .req t, h, env, he => hasHeldUnder_of_HF t h env he
  | .optional t, h, env, he => hasHeldUnder_of_HF t h env he
end

variable [Sem S]

/-- The laws of the top that the held-free theory reads: each primitive is below the top, the
    top acts as the list and map formers, and the set lift keeps a codec below the top. -/
structure TopLaws (S : Syn) [Sem S] : Prop where
  ground : ∀ g, Sub (Sem.ground g) (Sem.top (S := S))
  list : ∀ L ∈ Sem.list (S := S),
    (∀ vs, (Sem.top (S := S)).e (L.pV.into vs) = (traverse (Sem.top (S := S)).e vs).map L.pA.into) ∧
    (∀ as, (Sem.top (S := S)).p (L.pA.into as) = (traverse (Sem.top (S := S)).p as).map L.pV.into)
  map : ∀ F ∈ Sem.map (S := S),
    (∀ m : MapOf S.V, (Sem.top (S := S)).e (F.mV.into m) =
      (funImage fun k => (Sem.top (S := S)).e (m.get k)).map fun g => F.mA.into ⟨m.keys, g⟩) ∧
    (∀ m : MapOf (Sem.A S), (Sem.top (S := S)).p (F.mA.into m) =
      (funImage fun k => (Sem.top (S := S)).p (m.get k)).map fun g => F.mV.into ⟨m.keys, g⟩)
  set : ∀ L ∈ Sem.set (S := S), ∀ c : S.C, Sub c (Sem.top (S := S)) →
    Sub (L.lift c) (Sem.top (S := S))

/-- Each variable that `env` flags free of `held` denotes a restriction of the top. -/
def EnvHeld (env : Nat → Bool) (ρ : List S.C) : Prop :=
  ∀ i, env i = false → Sub (envAt ρ i) (Sem.top (S := S))

/-- A binder whose flag is `false` only where its codec is a restriction of the top. -/
theorem EnvHeld.cons {flag : Bool} {c : S.C} {env : Nat → Bool} {ρ : List S.C}
    (hc : flag = false → Sub c (Sem.top (S := S))) (h : EnvHeld env ρ) :
    EnvHeld (flagsCons flag env) (c :: ρ)
  | 0, hf => hc hf
  | i + 1, hf => h i hf

mutual
/-- **Confluence.** The denotation of a term with no `held` under the flags is a restriction of
    the top, on both halves, over an environment whose flagged variables are restrictions of the
    top. A variable is a possible `held` only where its flag says so. -/
theorem sub_denoteUnder (hT : TopLaws S) : ∀ (t : Term S) (env : Nat → Bool) (ρ : List S.C),
    hasHeldUnder env t = false → EnvHeld env ρ → Sub (denote t ρ) (Sem.top (S := S))
  | .prim g, _, _, _, _ => hT.ground g
  | .opaq, _, _, _, _ => ⟨fun _ _ h => h, fun _ _ h => h⟩
  | .never, _, _, _, _ => sub_empty
  | .var i, _, _, h, henv => henv i h
  | .set t, env, ρ, h, henv => by
      simp only [denote]
      cases hL : Sem.set (S := S) with
      | none => exact sub_empty
      | some L => exact hT.set L hL _ (sub_denoteUnder hT t env ρ h henv)
  -- each stage is a restriction by the body's case at the stage before, and the limit reads a
  -- stage at each input
  | .mu b, env, ρ, h, henv => by
      have hs : ∀ n, Sub (muStage (fun c => denote b (c :: ρ)) n) (Sem.top (S := S)) := fun n => by
        induction n with
        | zero => exact sub_empty
        | succ n ih => exact sub_denoteUnder hT b _ (_ :: ρ) h (EnvHeld.cons (fun _ => ih) henv)
      exact ⟨fun v a he => (hs _).1 v a he, fun a v hp => (hs _).2 a v hp⟩
  | .held _ _ _ _, _, _, h, _ => nomatch h
  | .refine t q, env, ρ, h, henv =>
      sub_trans (sub_restrict_self _ _) (sub_denoteUnder hT t env ρ h henv)
  | .list pre sp suf, env, ρ, h, henv => by
      simp only [hasHeldUnder, Bool.or_eq_false_iff] at h
      simp only [denote]
      cases hL : Sem.list (S := S) with
      | none => exact sub_empty
      | some L =>
        exact sub_listCodec (hT.list L hL).1 (hT.list L hL).2
          (sub_denoteList hT pre env ρ h.1.1 henv) (sub_denoteOpt hT sp env ρ h.1.2 henv)
          (sub_denoteList hT suf env ρ h.2 henv)
  | .object b, env, ρ, h, henv => sub_body hT b env ρ h henv
  | .union os, env, ρ, h, henv => sub_altCodec (sub_denoteList hT os env ρ h henv) _
/-- …at a body. -/
theorem sub_body (hT : TopLaws S) : ∀ (b : Body S) (env : Nat → Bool) (ρ : List S.C),
    hasHeldUnderB env b = false → EnvHeld env ρ → Sub (bodySem b ρ) (Sem.top (S := S))
  | .mk fields f w, env, ρ, h, henv => by
      simp only [hasHeldUnderB, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_exists] at h
      simp only [bodySem]
      cases hF : Sem.map (S := S) with
      | none => exact sub_empty
      | some F =>
        exact sub_objectCodec (hT.map F hF).1 (hT.map F hF).2 (wildSem_ne_drop _)
          (fun k => sub_slot hT (f k) env ρ (by simpa using h.1 k) henv)
          (sub_wild hT w env ρ h.2 henv)
/-- …at a slot. -/
theorem sub_slot (hT : TopLaws S) : ∀ (s : ObjectSlot S) (env : Nat → Bool) (ρ : List S.C),
    hasHeldUnderS env s = false → EnvHeld env ρ → Sub (fieldSem s ρ).codec (Sem.top (S := S))
  | .req t, env, ρ, h, henv => sub_denoteUnder hT t env ρ h henv
  | .optional t, env, ρ, h, henv => sub_denoteUnder hT t env ρ h henv
/-- …at an open block. -/
theorem sub_wild (hT : TopLaws S) : ∀ (w : Option (Term S)) (env : Nat → Bool) (ρ : List S.C),
    hasHeldUnderO env w = false → EnvHeld env ρ →
    ∀ c ∈ rcOf (wildSem w ρ), Sub c (Sem.top (S := S))
  | none, _, _, _, _ => fun _ hc => nomatch hc
  | some t, env, ρ, h, henv => fun c hc => by cases hc; exact sub_denoteUnder hT t env ρ h henv
/-- …at a list of terms. -/
theorem sub_denoteList (hT : TopLaws S) : ∀ (ts : List (Term S)) (env : Nat → Bool)
    (ρ : List S.C), hasHeldUnderL env ts = false → EnvHeld env ρ →
    ∀ c ∈ denoteList ts ρ, Sub c (Sem.top (S := S))
  | [], _, _, _, _ => fun _ hc => nomatch hc
  | t :: ts, env, ρ, h, henv => fun c hc => by
      simp only [hasHeldUnderL, Bool.or_eq_false_iff] at h
      rcases List.mem_cons.mp hc with rfl | hc
      · exact sub_denoteUnder hT t env ρ h.1 henv
      · exact sub_denoteList hT ts env ρ h.2 henv c hc
/-- …at an optional term. -/
theorem sub_denoteOpt (hT : TopLaws S) : ∀ (o : Option (Term S)) (env : Nat → Bool)
    (ρ : List S.C), hasHeldUnderO env o = false → EnvHeld env ρ →
    ∀ c ∈ denoteOpt o ρ, Sub c (Sem.top (S := S))
  | none, _, _, _, _ => fun _ hc => nomatch hc
  | some t, env, ρ, h, henv => fun c hc => by cases hc; exact sub_denoteUnder hT t env ρ h henv
end

/-- **Confluence, held-free.** The denotation of a held-free term is a restriction of the top,
    over an environment of restrictions of the top: `sub_denoteUnder` at the flags that are
    `false` at each variable. -/
theorem sub_denoteIn (hT : TopLaws S) (t : Term S) (h : HF t) (ρ : List S.C)
    (henv : ∀ i, Sub (envAt ρ i) (Sem.top (S := S))) : Sub (denote t ρ) (Sem.top (S := S)) :=
  sub_denoteUnder hT t (fun _ => false) ρ (hasHeldUnder_of_HF t h _ fun _ => rfl)
    (fun i _ => henv i)

/-- **Each stage of a binder with no `held` under the flags is a restriction of the top.** -/
theorem sub_muStage_under (hT : TopLaws S) {b : Term S} {env : Nat → Bool} {ρ : List S.C}
    (h : hasHeldUnder (flagsCons false env) b = false) (henv : EnvHeld env ρ) :
    ∀ n, Sub (muStage (fun c => denote b (c :: ρ)) n) (Sem.top (S := S))
  | 0 => sub_empty
  | n + 1 => sub_denoteUnder hT b _ _ h (EnvHeld.cons (fun _ => sub_muStage_under hT h henv n) henv)

/-- **Confluence**, closed: the denotation of a held-free term is a restriction of the top. -/
theorem sub_denote (hT : TopLaws S) (t : Term S) (h : HF t) : Sub (denote t) (Sem.top (S := S)) :=
  sub_denoteIn hT t h [] fun _ => sub_empty

/-- **Held-free lawful terms are pairwise compatible**: the common bound is the top, and the top
    is canonical. -/
theorem compat_of_HF (hT : TopLaws S) (hcan : Canon (Sem.top (S := S))) {s t : Term S} (hs : HF s) (ht : HF t)
    (hlt : Lawful Sem.member (denote t)) : Compat (denote s) (denote t) :=
  compat_of_common_bound' (sub_denote hT s hs) (sub_denote hT t ht) hcan hlt

end HeldFree

end Calculus.Alg
