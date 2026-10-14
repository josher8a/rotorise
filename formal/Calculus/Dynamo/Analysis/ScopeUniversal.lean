import Calculus.Dynamo.Lang.ScopeHeldFree
import Calculus.Dynamo.Analysis.ScopeSlice

/-!
# `opaque` is the universal sum, over closed codecs

`opaque` is the top of the admission lattice. The normal form is one union over each base and
each container, as a closed codec of one entry:

    opaque = union [string, boolean, binary, null, number,
                    array opaque, record opaque, set opaque]

The union holds `opaque` under a container, so the scope term is finite and names no entry.

`set opaque` does not meet the DynamoDB set obligation (`SetElem`), because `opaque` names no
member. The unfolding is a statement of the algebra, and the obligation is the store's.

The unfolding is two theorems, one for each projection. `Closed.Adm_opaqUnfold` and
`Closed.AdmA_opaqUnfold` state that the union admits exactly what `opaque` admits: every value, and
every attribute. Each proof finds the one option that acts at each constructor, and the union acts
where one option acts (`Scoped.interp_union_isSome`).
-/

namespace Calculus

/-- A union acts where one of its options acts. -/
theorem select_isSome_of_mem {V M X Y : Type} {os : List (Alg.Codec V M)}
    {run : Alg.Codec V M → X → Option Y} {x : X} {c : Alg.Codec V M} (hc : c ∈ os)
    (h : (run c x).isSome = true) : (Alg.select os run x).isSome = true := by
  cases hs : Alg.select os run x with
  | none => rw [(Alg.select_eq_none run x os).mp hs c hc] at h; exact nomatch h
  | some _ => rfl

/-- **A union term acts where the option at one position acts**, at each orientation. -/
theorem Scoped.interp_union_isSome {τ : (s : Bool) → Alg.TableAt dynSig s} {w k : Nat}
    (os : List (Scoped.Term w k)) (ρw : Fin w → Codec) (ρk : Fin k → Codec)
    (o : Alg.Orient) (x : Value) (p : Fin os.length)
    (h : ((Alg.SFlat.interp (Alg.Scoped.TStep τ) (os.get p) ρw ρk).f o x).isSome
      = true) :
    ((Alg.SFlat.interp (Alg.Scoped.TStep τ) (Scoped.Term.union os) ρw ρk).f o
      x).isSome = true := by
  show (Alg.select (List.ofFn fun p =>
    Alg.SFlat.interp (Alg.Scoped.TStep τ) (os.get p) ρw ρk) (·.f o) x).isSome = true
  exact select_isSome_of_mem (List.mem_ofFn.mpr ⟨p, rfl⟩) h

/-- **An object that declares no name and has an open block is a record**, whatever the map of
    its empty key set. -/
theorem objectCodec_empty (F : {k // k ∈ (∅ : Finset Name)} → FieldSem) (c : Codec) :
    objectCodec ⟨∅, F⟩ (.codec c) = recordCodec c := by
  have hF : F = fun k => absurd k.2 (Finset.notMem_empty k.1) :=
    funext fun k => absurd k.2 (Finset.notMem_empty k.1)
  subst hF
  rfl

/-- The options of `opaque` unfolded one time: each base, and each container over `opaque`. -/
def opaqOptions : List (Scoped.Term 1 0) :=
  [.string, .boolean, .binary, .null, .number, Scoped.Term.array .opaq,
    Scoped.Term.object ⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1), some .opaq⟩, .set .opaq]

/-- `opaque` unfolded one time, as a closed codec of one entry. -/
def opaqUnfoldClosed : Closed := Closed.one (.union opaqOptions)

/-- **The options of the unfolding are pairwise orthogonal**, as closed codecs. -/
theorem Closed.opaqUnfold_ok : certAllC (opaqOptions.map Closed.one) = true := by
  decide

/-- **The unfolding is held-free.** -/
theorem Closed.opaqUnfold_HF : opaqUnfoldClosed.HF := rfl

/-- **`opaque` is total, write side.** `opaque` writes every value. -/
theorem Closed.opaq_total (α : Table) (v : Value) :
    (((Closed.one .opaq).meaning α).e v).isSome = true :=
  congrArg Option.isSome (Closed.opaq_f α .host v)

/-- **`opaque` is total, read side.** `opaque` reads every attribute. -/
theorem Closed.opaqA_total (α : Table) (a : Attr) : (Closed.one .opaq).AdmA α a = true :=
  congrArg Option.isSome (Closed.opaq_f α .dual a)

/-- **The unfolding acts at every datum**, at each orientation. -/
theorem Closed.opaqUnfold_isSome (α : Table) (o : Alg.Orient) (v : Value) :
    ((opaqUnfoldClosed.meaning α).f o v).isSome = true := by
  rw [opaqUnfoldClosed, Closed.one_fix]
  cases v with
  | s _ =>
    refine Scoped.interp_union_isSome _ _ _ _ _ ⟨0, by decide⟩ ?_
    rcases o with ⟨⟨_ | _, _ | _⟩, ho⟩ <;> rfl
  | bool _ =>
    refine Scoped.interp_union_isSome _ _ _ _ _ ⟨1, by decide⟩ ?_
    rcases o with ⟨⟨_ | _, _ | _⟩, ho⟩ <;> rfl
  | b _ =>
    refine Scoped.interp_union_isSome _ _ _ _ _ ⟨2, by decide⟩ ?_
    rcases o with ⟨⟨_ | _, _ | _⟩, ho⟩ <;> rfl
  | null =>
    refine Scoped.interp_union_isSome _ _ _ _ _ ⟨3, by decide⟩ ?_
    rcases o with ⟨⟨_ | _, _ | _⟩, ho⟩ <;> rfl
  | n _ =>
    refine Scoped.interp_union_isSome _ _ _ _ _ ⟨4, by decide⟩ ?_
    rcases o with ⟨⟨_ | _, _ | _⟩, ho⟩ <;> rfl
  | ss S =>
    refine Scoped.interp_union_isSome _ _ _ _ _ ⟨7, by decide⟩ ?_
    exact Option.isSome_iff_exists.mpr ⟨_, setAt_Ω o .string S⟩
  | ns S =>
    refine Scoped.interp_union_isSome _ _ _ _ _ ⟨7, by decide⟩ ?_
    exact Option.isSome_iff_exists.mpr ⟨_, setAt_Ω o .number S⟩
  | bs S =>
    refine Scoped.interp_union_isSome _ _ _ _ _ ⟨7, by decide⟩ ?_
    exact Option.isSome_iff_exists.mpr ⟨_, setAt_Ω o .binary S⟩
  | l xs =>
    refine Scoped.interp_union_isSome _ _ _ _ _ ⟨5, by decide⟩ ?_
    show ((arrayCodec Alg.idCodec).f o (.l xs)).isSome = true
    rw [arrayCodec_f]
    show (Option.map Attr.l (traverse some xs)).isSome = true
    rw [Alg.traverse_some]
    rfl
  | m keys g =>
    refine Scoped.interp_union_isSome _ _ _ _ _ ⟨6, by decide⟩ ?_
    show ((objectCodec ⟨∅, _⟩ (.codec Alg.idCodec)).f o (Attr.m keys g)).isSome = true
    rw [objectCodec_empty, recordCodec_f]
    exact congrArg Option.isSome
      (congrArg (Option.map (Attr.m keys)) (Alg.funImage_eq (f := g) fun _ => rfl))

/-- **The unfolding lemma, write side.** `opaque` writes exactly the values that its unfolding
    writes: every value. -/
theorem Closed.Adm_opaqUnfold (α : Table) (v : Value) :
    ((opaqUnfoldClosed.meaning α).e v).isSome = (((Closed.one .opaq).meaning α).e v).isSome :=
  (Closed.opaqUnfold_isSome α .host v).trans (Closed.opaq_total α v).symm

/-- **The unfolding lemma, read side.** `opaque` reads exactly the attributes that its unfolding
    reads: every attribute. -/
theorem Closed.AdmA_opaqUnfold (α : Table) (a : Attr) :
    opaqUnfoldClosed.AdmA α a = (Closed.one .opaq).AdmA α a :=
  (Closed.opaqUnfold_isSome α .dual a).trans (Closed.opaqA_total α a).symm

end Calculus
