import Calculus.Dynamo.Lang.ScopeSound

/-!
# The index of a closed judgement is the held set of its term

`TOp.rule_T` states, at each operation of DynamoDB, that the held set the rule names from the held
sets of its positions is the held set of `TOp.run` on the codecs of the positions. The rule and the
codec build each held set with the same former, so most operations agree on the nose. Three do
not: `list` (positional through `alignL`), `object` (name-dispatched) and `set` (the three wire
sets of DynamoDB).

`Scoped.typed_T_eq` lifts the identity to a term of a scope, and `Closed.typed_T_identity` states
it at each entry of a typed closed codec: the index of the entry is the held set of its term over
the solution, and that term moves what the entry moves.
-/

namespace Calculus

open Alg (HTuple HTupleL HList HObject HUnion HNever align alignL)

/-! ## The positional held sets -/

/-- **`align` holds its pairs exactly where the positions hold `HTuple`.** -/
theorem align_iff_HTuple : ∀ (cs : List Codec) (tl : Option Codec) (vs : List Value),
    (∃ ps, align cs tl vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2) ↔
      HTuple (cs.map (·.T)) (tl.map (·.T)) vs
  | [], none, [] => ⟨fun _ => rfl, fun _ => ⟨[], rfl, fun _ h => (nomatch h)⟩⟩
  | [], none, _ :: _ => ⟨fun ⟨_, h, _⟩ => (nomatch h), fun h => (nomatch h)⟩
  | [], some _, [] => ⟨fun _ _ h => (nomatch h), fun _ => ⟨[], rfl, fun _ h => (nomatch h)⟩⟩
  | [], some c, x :: xs => by
    have ih := align_iff_HTuple [] (some c) xs
    constructor
    · rintro ⟨ps, hal, hall⟩
      obtain ⟨ps', hal', rfl⟩ := Alg.align_nil_some_cons.mp hal
      have hxs := ih.mp ⟨ps', hal', fun p hp => hall p (List.mem_cons_of_mem _ hp)⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hall (c, y) List.mem_cons_self
      · exact hxs y hy
    · intro h
      obtain ⟨ps', hal', hall'⟩ := ih.mpr fun y hy => h y (List.mem_cons_of_mem _ hy)
      refine ⟨(c, x) :: ps', Alg.align_nil_some_cons.mpr ⟨ps', hal', rfl⟩, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact h x List.mem_cons_self
      · exact hall' p hp
  | _ :: _, _, [] => ⟨fun ⟨_, h, _⟩ => (nomatch h), fun h => (nomatch h)⟩
  | c :: cs, tl, x :: xs => by
    have ih := align_iff_HTuple cs tl xs
    constructor
    · rintro ⟨ps, hal, hall⟩
      obtain ⟨ps', hal', rfl⟩ := Alg.align_cons_cons.mp hal
      exact ⟨hall (c, x) List.mem_cons_self,
        ih.mp ⟨ps', hal', fun p hp => hall p (List.mem_cons_of_mem _ hp)⟩⟩
    · rintro ⟨hx, hxs⟩
      obtain ⟨ps', hal', hall'⟩ := ih.mpr hxs
      refine ⟨(c, x) :: ps', Alg.align_cons_cons.mpr ⟨ps', hal', rfl⟩, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hx
      · exact hall' p hp

/-- **The suffix holds position by position** exactly where the zipped row holds its pairs. -/
theorem forall₂_iff_zip : ∀ (suf : List Codec) (back : List Value),
    List.Forall₂ (fun T v => T v) (suf.map (·.T)) back ↔
      back.length = suf.length ∧ ∀ p ∈ suf.zip back, p.1.T p.2
  | [], [] => ⟨fun _ => ⟨rfl, fun _ h => (nomatch h)⟩, fun _ => .nil⟩
  | [], _ :: _ => ⟨fun h => (nomatch h), fun ⟨h, _⟩ => (nomatch h)⟩
  | _ :: _, [] => ⟨fun h => (nomatch h), fun ⟨h, _⟩ => (nomatch h)⟩
  | c :: cs, b :: bs => by
    rw [List.map_cons, List.forall₂_cons, forall₂_iff_zip cs bs, List.zip_cons_cons]
    constructor
    · rintro ⟨hb, hlen, hall⟩
      refine ⟨congrArg Nat.succ hlen, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hb
      · exact hall p hp
    · rintro ⟨hlen, hall⟩
      exact ⟨hall (c, b) List.mem_cons_self, Nat.succ.inj hlen,
        fun p hp => hall p (List.mem_cons_of_mem _ hp)⟩

/-- **`alignL` holds its pairs exactly where the positions hold `HTupleL`.** -/
theorem alignL_iff_HTupleL (pre : List Codec) (sp : Option Codec) (suf : List Codec)
    (vs : List Value) :
    (∃ ps, alignL pre sp suf vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2) ↔
      HTupleL (pre.map (·.T)) (sp.map (·.T)) (suf.map (·.T)) vs := by
  constructor
  · rintro ⟨ps, hal, hall⟩
    obtain ⟨front, back, psF, rfl, hblen, halF, rfl⟩ := Alg.alignL_split _ _ _ _ _ hal
    exact ⟨front, back, rfl,
      (forall₂_iff_zip suf back).mpr ⟨hblen, fun p hp => hall p (List.mem_append_right _ hp)⟩,
      (align_iff_HTuple pre sp front).mp ⟨psF, halF, fun p hp => hall p (List.mem_append_left _ hp)⟩⟩
  · rintro ⟨front, back, rfl, hb, hf⟩
    obtain ⟨hblen, hzip⟩ := (forall₂_iff_zip suf back).mp hb
    obtain ⟨psF, halF, hpsF⟩ := (align_iff_HTuple pre sp front).mpr hf
    refine ⟨psF ++ suf.zip back, Alg.alignL_of_split hblen halF, fun p hp => ?_⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hpsF p hp
    · exact hzip p hp

/-- The held sets of a row of positions, read through `List.ofFn`. -/
theorem ofFn_T {n : Nat} (a : Fin n → Codec) : List.ofFn (fun p => (a p).T) = (List.ofFn a).map (·.T) := by
  rw [List.map_ofFn]; rfl

/-- The held set of an optional position. -/
theorem optOf_T (s : Fin 2) (a : Fin s → Codec) :
    Alg.Scoped.optOf s (fun p => (a p).T) = (Alg.Scoped.optOf s a).map (·.T) :=
  match s with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-! ## The set and the object -/

/-- **The held set of a set is `HSet` of the held set of its element.** -/
theorem HSet_setCodec (c : Codec) (v : Value) : HSet c.T v ↔ (setCodec c).T v := by
  constructor
  · rintro (⟨S, rfl, h⟩ | ⟨S, rfl, h⟩ | ⟨S, rfl, h⟩) <;> exact h
  · intro h
    cases v with
    | ss S => exact .inl ⟨S, rfl, h⟩
    | ns S => exact .inr (.inl ⟨S, rfl, h⟩)
    | bs S => exact .inr (.inr ⟨S, rfl, h⟩)
    | _ => exact False.elim h

/-- A slot with no fill lets absence be on the write exactly where it is not required. -/
theorem absent_mkField {m : Alg.Scoped.SlotMode dynSig} (hm : m.isFill = false) (c : Codec) :
    (Alg.absentOf .host (some (Alg.Scoped.mkField m c))).isSome = !m.isReq :=
  match m, hm with
  | .req, _ => rfl
  | .opt, _ => rfl

/-- A slot's field reads its codec. -/
theorem codec_mkField (m : Alg.Scoped.SlotMode dynSig) (c : Codec) :
    (Alg.Scoped.mkField m c).codec = c :=
  match m with
  | .req => rfl
  | .opt => rfl
  | .fill _ => rfl

/-- The open block: its codec's held set is the held set of the rule. -/
theorem rest_T (s : Fin 2) (a : Fin s → Codec) (x : Value) :
    (∃ rc, Alg.rcOf (Alg.Scoped.restOf (B := dynSig) s a) = some rc ∧ rc.T x) ↔
      ∃ T, Alg.Scoped.optOf s (fun p => (a p).T) = some T ∧ T x :=
  match s with
  | ⟨0, _⟩ => ⟨fun ⟨_, h, _⟩ => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | ⟨1, _⟩ => ⟨fun ⟨_, h, hx⟩ => ⟨_, rfl, by cases h; exact hx⟩,
      fun ⟨_, h, hx⟩ => ⟨_, rfl, by cases h; exact hx⟩⟩

/-- **The held set of an object with no fill is `HObject` of the held sets of its slots.** -/
theorem HObject_objectCodec {fs : Finset String} {md : {x // x ∈ fs} → Alg.Scoped.SlotMode dynSig}
    {s : Fin 2} (a : {x // x ∈ fs} ⊕ Fin s → Codec) (hfill : ∀ x, (md x).isFill = false)
    (v : Value) :
    HObject dMap.p fs (fun x => ((md x).isReq, (a (.inl x)).T))
        (Alg.Scoped.optOf s fun p => (a (.inr p)).T) v ↔
      (Alg.objectCodec dMap.toSummand ⟨fs, fun x => Alg.Scoped.mkField (md x) (a (.inl x))⟩
        (Alg.Scoped.restOf (B := dynSig) s fun p => a (.inr p))).T v := by
  constructor
  · rintro ⟨keys, f, rfl, hreq, hent⟩
    refine ⟨⟨keys, f⟩, rfl, Alg.slotT_all_iff.mpr ⟨fun k hk hkk => ?_, fun k => ?_⟩⟩
    · rw [MapOf.at_of_mem (m := ⟨fs, _⟩) ⟨k, hk⟩, absent_mkField (hfill _)]
      cases hr : (md ⟨k, hk⟩).isReq
      · rfl
      · exact absurd (hreq ⟨k, hk⟩ hr) hkk
    · have he := hent k
      rcases Decidable.em (k.1 ∈ fs) with hk | hk
      · rw [dif_pos hk] at he
        simp only [Alg.objEntryT, MapOf.at_of_mem (m := ⟨fs, _⟩) ⟨k.1, hk⟩]
        exact (congrArg (fun c => Alg.Codec.T c (f k)) (codec_mkField _ _)).mpr he
      · rw [dif_neg hk] at he
        simp only [Alg.objEntryT, MapOf.at_none (m := ⟨fs, _⟩) hk]
        exact (rest_T s _ _).mpr he
  · rintro ⟨⟨keys, f⟩, rfl, hslot⟩
    obtain ⟨habs, hent⟩ := Alg.slotT_all_iff.mp hslot
    refine ⟨keys, f, rfl, fun k hr => ?_, fun k => ?_⟩
    · refine Decidable.byContradiction fun hkk => ?_
      have h := habs k.1 k.2 hkk
      have hr' : (md k).isReq = true := hr
      rw [MapOf.at_of_mem (m := ⟨fs, _⟩) k, absent_mkField (hfill _), hr'] at h
      exact nomatch h
    · have he := hent k
      rcases Decidable.em (k.1 ∈ fs) with hk | hk
      · rw [dif_pos hk]
        simp only [Alg.objEntryT, MapOf.at_of_mem (m := ⟨fs, _⟩) ⟨k.1, hk⟩] at he
        exact (congrArg (fun c => Alg.Codec.T c (f k)) (codec_mkField _ _)).mp he
      · rw [dif_neg hk]
        simp only [Alg.objEntryT, MapOf.at_none (m := ⟨fs, _⟩) hk] at he
        exact (rest_T s _ _).mp he

/-! ## Each operation -/

variable (τ : (s : Bool) → Alg.TableAt dynSig s)

/-- **The rule names the held set of the operation's codec**, at every operation with a rule. -/
theorem TOp.rule_T : ∀ (o : Alg.Scoped.TOp dynSig) (a : o.Pos → Codec)
    (μ : o.Pos → Option Member) (r),
    Alg.Scoped.TOp.rule τ o a (fun p => (a p).T) μ = some r →
      ∀ v, r.1 v ↔ (Alg.Scoped.TOp.run τ o a).T v
  | .prim _, _, _, _, hr => by cases hr; exact fun _ => Iff.rfl
  | .opaq, _, _, _, hr => by cases hr; exact fun _ => Iff.rfl
  | .never, _, _, _, hr => by cases hr; exact fun _ => Iff.rfl
  | .set, a, _, _, hr => by cases hr; exact HSet_setCodec (a ())
  | .list _ s _, a, _, _, hr => by
    cases hr
    intro v
    refine exists_congr fun vs => and_congr_right fun _ => ?_
    rw [ofFn_T, optOf_T, ofFn_T]
    exact (alignL_iff_HTupleL _ _ _ vs).symm
  | .refine _ _, _, _, _, hr => by cases hr; exact fun _ => Iff.rfl
  | .held _ _ _, _, _, _, hr => by cases hr; exact fun _ => Iff.rfl
  | .legacy _, _, _, _, hr => nomatch hr
  | .obj fs md s, a, _, r, hr => by
    change (if (Alg.Scoped.keyPos fs).all (fun x => !(md x).isFill) then _ else none) = some r at hr
    split at hr
    · next hall =>
      cases hr
      refine HObject_objectCodec a fun x => ?_
      have h := List.all_eq_true.mp hall x (Alg.Scoped.keyPos_complete fs x)
      cases hm : (md x).isFill
      · rfl
      · have h' : (!(md x).isFill) = true := h
        rw [hm] at h'
        exact nomatch h'
    · exact nomatch hr
  | .union _, a, _, _, hr => by
    cases hr
    intro v
    constructor
    · rintro ⟨T, hT, hv⟩
      obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hT
      exact ⟨a p, List.mem_ofFn.mpr ⟨p, rfl⟩, hv⟩
    · rintro ⟨c, hc, hv⟩
      obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc
      exact ⟨(a p).T, List.mem_ofFn.mpr ⟨p, rfl⟩, hv⟩

/-! ## A term, and a closed codec -/

/-- **The index of a closed graph term is the held set of the term.** -/
theorem Scoped.typedC_T_eq {t : Alg.Scoped.Graph dynSig 0}
    {T : Alg.Mean.V dynSig → Prop} {μ : Option (Alg.Mean.Mem dynSig)}
    (h : Alg.Scoped.TypedC τ t T μ) :
    ∀ v, T v ↔ (Alg.Flat.interp (Alg.Scoped.TStep τ) Fin.elim0 t).T v := by
  induction h with
  | @node o args T μ r _ hr ih =>
    have hT : T = fun p => (Alg.Flat.interp (Alg.Scoped.TStep τ) Fin.elim0 (args p)).T :=
      funext fun p => funext fun v => propext (ih p v)
    subst hT
    exact TOp.rule_T τ o _ μ r hr

/-- **The index of a scope term is the held set of the term**, at the environments it is typed at. -/
theorem Scoped.typed_T_eq {w k : Nat}
    {ρw : Fin w → Alg.Mean.C dynSig} {ρk : Fin k → Alg.Mean.C dynSig} {t : Alg.Scoped.Term dynSig w k}
    {T : Alg.Mean.V dynSig → Prop} {μ : Option (Alg.Mean.Mem dynSig)}
    (h : Alg.Scoped.Typed τ ρw ρk t T μ) :
    ∀ v, T v ↔ (Alg.SFlat.interp (Alg.Scoped.TStep τ) t ρw ρk).T v := by
  induction h with
  | ref i => exact fun _ => Iff.rfl
  | @node o _ args T μ r _ hr ih =>
    have hT : T = fun p => (Alg.SFlat.interp (Alg.Scoped.TStep τ) (args p) ρw ρk).T :=
      funext fun p => funext fun v => propext (ih p v)
    subst hT
    exact TOp.rule_T τ o _ μ r hr
  | @down o _ args r hr => exact TOp.rule_T τ o _ _ r hr
  | @wall o _ args T μ r hc hr =>
    have hT : T = fun p => (Alg.Flat.interp (Alg.Scoped.TStep τ) Fin.elim0 (args p)).T :=
      funext fun p => funext fun v => propext (Scoped.typedC_T_eq τ (hc p) v)
    subst hT
    exact TOp.rule_T τ o _ μ r hr

/-- **The index of each entry of a typed closed codec is the held set of its term** over the
    solution, and that term moves what the entry moves. -/
theorem Closed.typed_T_identity {n : Nat} (d : Alg.Scoped.Closed dynSig n)
    (hty : Alg.Scoped.Closed.Typed τ d) (i : Fin n) :
    ∃ T μ, Alg.Scoped.Typed τ (Alg.Scoped.Closed.top τ d)
        (fun j => Alg.Scoped.Closed.top τ d (Fin.castLE (Nat.le_of_lt i.isLt) j)) (d i) T μ ∧
      (∀ v, T v ↔ (Alg.SFlat.interp (Alg.Scoped.TStep τ)
        (d i) (Alg.Scoped.Closed.top τ d)
        (fun j => Alg.Scoped.Closed.top τ d (Fin.castLE (Nat.le_of_lt i.isLt) j))).T v) ∧
      (Alg.SFlat.interp (Alg.Scoped.TStep τ)
        (d i) (Alg.Scoped.Closed.top τ d)
        (fun j => Alg.Scoped.Closed.top τ d (Fin.castLE (Nat.le_of_lt i.isLt) j))).f =
        (Alg.Scoped.Closed.top τ d i).f := by
  obtain ⟨T, μ, ht⟩ := hty i
  have hS := Alg.Scoped.TStep_lawful τ
  have hfix : ∀ j, (Alg.Scoped.Closed.top τ d j).f =
      ((Alg.nf (Alg.Scoped.TSig dynSig) d j).interp
        (Alg.Scoped.TStep τ) (Alg.Scoped.Closed.top τ d)).f := fun j =>
    funext fun o => funext fun v => Alg.solve_fix Alg.Mean.d_pos (Alg.nf_contractive hS d) j o v
  refine ⟨T, μ, ht, Scoped.typed_T_eq τ ht, ?_⟩
  have e := Alg.interp_nf (R := Alg.Scoped.TStep τ) d
    (Alg.Scoped.Closed.top τ d) i
  rw [hfix i, e]
  exact Alg.SFlat.interp_f_congr hS (d i) (fun _ => rfl) fun _ => hfix _

end Calculus
