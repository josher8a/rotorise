import Calculus.AlgSound

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

mutual
/-- **Confluence.** The denotation of a held-free term is a restriction of the top, on both
    halves, over an environment of restrictions of the top. -/
theorem sub_denoteIn (hT : TopLaws S) : ∀ t : Term S, HF t → ∀ ρ : List S.C,
    (∀ i, Sub (envAt ρ i) (Sem.top (S := S))) → Sub (denote t ρ) (Sem.top (S := S))
  | .prim g, _, _, _ => hT.ground g
  | .opaq, _, _, _ => ⟨fun _ _ h => h, fun _ _ h => h⟩
  | .never, _, _, _ => sub_empty
  | .var i, _, _, henv => henv i
  | .set t, h, ρ, henv => by
      simp only [denote]
      cases hL : Sem.set (S := S) with
      | none => exact sub_empty
      | some L => exact hT.set L hL _ (sub_denoteIn hT t h ρ henv)
  -- each stage is a restriction by the body's case at the stage before, and the limit reads a
  -- stage at each input
  | .mu b, h, ρ, henv => by
      have hs : ∀ n, Sub (muStage (fun c => denote b (c :: ρ)) n) (Sem.top (S := S)) := fun n => by
        induction n with
        | zero => exact sub_empty
        | succ n ih =>
          exact sub_denoteIn hT b h (_ :: ρ) fun i => match i with
            | 0 => ih
            | i + 1 => henv i
      exact ⟨fun v a he => (hs _).1 v a he, fun a v hp => (hs _).2 a v hp⟩
  | .held _ _ _ _, h, _, _ => h.elim
  | .refine t q, h, ρ, henv =>
      sub_trans (sub_restrict_self _ _) (sub_denoteIn hT t h ρ henv)
  | .list pre sp suf, ⟨h1, h2, h3⟩, ρ, henv => by
      simp only [denote]
      cases hL : Sem.list (S := S) with
      | none => exact sub_empty
      | some L =>
        exact sub_listCodec (hT.list L hL).1 (hT.list L hL).2
          (sub_denoteList hT pre h1 ρ henv) (sub_denoteOpt hT sp h2 ρ henv)
          (sub_denoteList hT suf h3 ρ henv)
  | .object b, h, ρ, henv => sub_body hT b h ρ henv
  | .union os, h, ρ, henv => sub_altCodec (sub_denoteList hT os h ρ henv) _
/-- …at a body. -/
theorem sub_body (hT : TopLaws S) : ∀ b : Body S, HFB b → ∀ ρ : List S.C,
    (∀ i, Sub (envAt ρ i) (Sem.top (S := S))) → Sub (bodySem b ρ) (Sem.top (S := S))
  | .mk fields f w, ⟨hf, hw⟩, ρ, henv => by
      simp only [bodySem]
      cases hF : Sem.map (S := S) with
      | none => exact sub_empty
      | some F =>
        exact sub_objectCodec (hT.map F hF).1 (hT.map F hF).2 (wildSem_ne_drop _)
          (fun k => sub_slot hT (f k) (hf k) ρ henv) (sub_wild hT w hw ρ henv)
/-- …at a slot. -/
theorem sub_slot (hT : TopLaws S) : ∀ s : ObjectSlot S, HFS s → ∀ ρ : List S.C,
    (∀ i, Sub (envAt ρ i) (Sem.top (S := S))) → Sub (fieldSem s ρ).codec (Sem.top (S := S))
  | .req t, h, ρ, henv => sub_denoteIn hT t h ρ henv
  | .optional t, h, ρ, henv => sub_denoteIn hT t h ρ henv
/-- …at an open block. -/
theorem sub_wild (hT : TopLaws S) : ∀ w : Option (Term S), HFO w → ∀ ρ : List S.C,
    (∀ i, Sub (envAt ρ i) (Sem.top (S := S))) → ∀ c ∈ rcOf (wildSem w ρ), Sub c (Sem.top (S := S))
  | none, _, _, _ => fun _ hc => nomatch hc
  | some t, h, ρ, henv => fun c hc => by cases hc; exact sub_denoteIn hT t h ρ henv
/-- …at a list of terms. -/
theorem sub_denoteList (hT : TopLaws S) : ∀ ts : List (Term S), HFL ts → ∀ ρ : List S.C,
    (∀ i, Sub (envAt ρ i) (Sem.top (S := S))) → ∀ c ∈ denoteList ts ρ, Sub c (Sem.top (S := S))
  | [], _, _, _ => fun _ hc => nomatch hc
  | t :: ts, ⟨h1, h2⟩, ρ, henv => fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact sub_denoteIn hT t h1 ρ henv
      · exact sub_denoteList hT ts h2 ρ henv c hc
/-- …at an optional term. -/
theorem sub_denoteOpt (hT : TopLaws S) : ∀ o : Option (Term S), HFO o → ∀ ρ : List S.C,
    (∀ i, Sub (envAt ρ i) (Sem.top (S := S))) → ∀ c ∈ denoteOpt o ρ, Sub c (Sem.top (S := S))
  | none, _, _, _ => fun _ hc => nomatch hc
  | some t, h, ρ, henv => fun c hc => by cases hc; exact sub_denoteIn hT t h ρ henv
end

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
