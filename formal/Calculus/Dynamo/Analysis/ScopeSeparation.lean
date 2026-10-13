import Calculus.Dynamo.Lang.ScopeSound
import Calculus.Dynamo.Lang.ScopeEquations

/-!
# Separation of closed codecs, and what the meaning does not record

The closed counterparts of the builders, of separation on the pair, and of the negative results.
`array` is the degenerate `tuple`, so the two closed codecs are one. `Closed.SepJV` and
`Closed.SepJA` state separation on the write domain and the read row of the meaning. A predicate on
the meaning does not say how a term is written: `string` and `refine(string, ⊤)` move the same data.
`Closed.Decides` states, on the meaning, that the kind does not settle admission.

The meaning holds its own domains, so no Boolean row stands beside it. A rewrite of the adapter of
a `held` or a `refine` reads the scope term (`Scoped.interp_held`, `Scoped.interp_refine`).
-/

namespace Calculus

variable {α : Table}

/-! ## `array` is the degenerate `tuple` -/

/-- `array` **is** the degenerate `tuple`: both builders write the same `list`, so the two closed
    codecs have one meaning. -/
theorem Closed.arrayRow (e : Scoped.Term 0 1 1) :
    (Closed.one (.array e)).meaning α = (Closed.one (.tuple [] (some e))).meaning α := rfl

/-- The same on the read row, and for the same reason. -/
theorem Closed.arrayRowA (e : Scoped.Term 0 1 1) (a : Attr) :
    (Closed.one (.array e)).AdmA α a = (Closed.one (.tuple [] (some e))).AdmA α a := rfl

/-! ## `refine t ⊤` and `t` move the same data -/

/-- A refinement by the trivially-true predicate: the same pair as the bare base. -/
def qTop : Value → Bool := fun _ => true

/-- **`refine t ⊤` and `t` move the same data**, over a scope term, at every environment. -/
theorem Scoped.refine_top_row {c w k : Nat} (τ : (s : Bool) → Alg.TableAt dynSig s)
    (κ : Fin c → Codec) (t : Scoped.Term c w k) (ρw : Fin w → Codec) (ρk : Fin k → Codec) :
    (Alg.SFlat.interp (Alg.CStep (Alg.Scoped.TStep τ) c κ)
        (Scoped.Term.refine t (.closure qTop) ()) ρw ρk).f =
      (Alg.SFlat.interp (Alg.CStep (Alg.Scoped.TStep τ) c κ) t ρw ρk).f := by
  funext o x
  refine Option.ext fun y => ?_
  rw [Scoped.interp_refine, Alg.Codec.restrict, Alg.refine2_f]
  cases o.c <;> cases o.s <;> simp [Alg.Side.elim, Pred.eval, qTop]

/-- **How a term is written is not a function of what it moves**: `string` and a refinement of
    `string` have one meaning at each orientation. -/
theorem Closed.Adm_string_eq_refine :
    ((Closed.one .string).meaning α).f =
      ((Closed.one (.refine .string (.closure qTop) ())).meaning α).f := by
  funext o v
  rw [Closed.one_fix, Closed.one_fix, Scoped.refine_top_row]
  rfl

/-! ## Separation on the meaning -/

variable (α) in
/-- **Separation on the write domain**: where `x` writes, `y` refuses. -/
def Closed.SepJV (x y : Closed) : Prop :=
  ∀ v, ((x.meaning α).e v).isSome = true → ((y.meaning α).e v).isSome = false

variable (α) in
/-- **…and on the read row.** -/
def Closed.SepJA (x y : Closed) : Prop := ∀ a, x.AdmA α a = true → y.AdmA α a = false

/-- A read channel that fires at `N` and nowhere else. -/
def rNum : Attr → Option Value := fun a => match a with | .n _ => some (.str "x") | _ => none

/-- **An alternate reader may read outside the member of its closed codec.** -/
theorem Closed.extendRead_reads_n :
    (((Closed.one .string).meaning α).extendRead rNum).p (.n (.of "1")) = some (.str "x") := rfl

/-- An adapter never widens the read domain. -/
theorem adapt_p_le {c : Codec} {f g : Value → Option Value} {a : Attr} :
    ((c.adapt f g).p a).isSome = true → (c.p a).isSome = true := by
  simp only [Alg.Codec.adapt, Alg.Codec.ofEP_p]
  exact Option.isSome_of_isSome_bind

/-! ## `Decides`, on the meaning -/

variable (α) in
/-- **A closed codec decides its own membership**: two values of one kind, one written and one
    refused, so the kind does not settle admission. -/
def Closed.Decides (t : Closed) : Prop :=
  ∃ v w, ((t.meaning α).e v).isSome = true ∧ v.kind = w.kind ∧ ((t.meaning α).e w).isSome = false

/-- A string `literal` decides. -/
theorem Closed.decides_literalS : (Closed.one (.literal .string "A")).Decides α :=
  ⟨.str "A", .str "B", rfl, rfl, rfl⟩

/-- `string` does not. -/
theorem Closed.not_decides_string : ¬ (Closed.one .string).Decides α := by
  rintro ⟨v, w, hv, hk, hw⟩
  cases v <;> cases w <;> first
    | exact Bool.false_ne_true ((by rfl : false = _).trans hv)
    | exact Bool.false_ne_true (hw.symm.trans (by rfl))
    | exact absurd hk (by simp [Attr.kind, Member.kind])

/-- **A row that answers `true` at every `refine` is too generous**: `refine(string, ⊤)` does not
    decide. -/
theorem Closed.not_decides_refine_top :
    ¬ (Closed.one (.refine .string (.closure qTop) ())).Decides α := by
  rintro ⟨v, w, hv, hk, hw⟩
  simp only [Alg.Codec.e] at hv hw
  rw [← Closed.Adm_string_eq_refine] at hv hw
  exact Closed.not_decides_string ⟨v, w, hv, hk, hw⟩

/-- **A row that answers `false` at every `object` is too stingy**: an object with a required field
    refuses the empty map and writes a populated one. -/
theorem Closed.decides_object :
    (Closed.one (.object (Scoped.Body.mk {"k"} (fun _ => .req .string) none))).Decides α :=
  ⟨.map {"k"} (fun _ => .str "a"), .map ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)),
    rfl, rfl, rfl⟩

/-- An adapter that sends one string to itself and everything else off `string`'s carrier.
    Total, so this is a `held` and not a `refine` — and it narrows exactly as a refinement
    would. -/
def fSplit : Value → Value := fun v => match v with | .str "A" => .str "A" | _ => .bool true

/-- The table that gives each generator the pair `fSplit`, `id`. -/
def splitTable : Table := fun _ => (fSplit, id)

/-- **The dual gap**: `held(string, string, fSplit, _)` writes `"A"` and refuses `"B"`, so it
    decides. -/
theorem Closed.decides_held :
    (Closed.one (.held false .string .string (.caller 0, false) [])).Decides splitTable :=
  ⟨.str "A", .str "B", rfl, rfl, rfl⟩

/-! ## Separation of sets, and of arrays -/

/-- A string literal writes one string and no other value. -/
theorem literal_e_isSome {c : String} {w : Value}
    (h : ((groundCodec (.literal .string c)).e w).isSome = true) : w = .str c := by
  change (((baseCodec .string).restrict (inL .string c)).e w).isSome = true at h
  rw [Alg.restrict_e_isSome, Bool.and_eq_true] at h
  exact inL_iff.mp h.1

/-- **Two sets over disjoint literals separate**: `℘⁺fin` has no empty inhabitant, so the two
    options share none. -/
theorem Closed.sepJV_set_literals :
    Closed.SepJV α (Closed.one (.set (.literal .string "A")))
      (Closed.one (.set (.literal .string "B"))) := by
  intro v hv
  simp only [Alg.Codec.e] at hv ⊢
  rw [Closed.one_fix] at hv
  rw [Closed.one_fix]
  cases v
  case ss S =>
    obtain ⟨x, hx⟩ := S.2
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hv
    have hA := literal_e_isSome (setAt_elem ha x hx)
    cases hb : ((setCodec (groundCodec (.literal .string "B"))).e (.ss S)).isSome with
    | false => exact hb
    | true =>
      obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.mp hb
      exact absurd (hA.symm.trans (literal_e_isSome (setAt_elem hb' x hx))) (by simp)
  case ns S =>
    obtain ⟨x, hx⟩ := S.2
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hv
    exact absurd (literal_e_isSome (setAt_elem ha x hx)) (by simp)
  case bs S =>
    obtain ⟨x, hx⟩ := S.2
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hv
    exact absurd (literal_e_isSome (setAt_elem ha x hx)) (by simp)
  all_goals exact nomatch hv

/-- **The array pair does not separate**: both options write `[]`. -/
theorem Closed.not_sepJV_array_literals :
    ¬ Closed.SepJV α (Closed.one (.array (.literal .string "A")))
      (Closed.one (.array (.literal .string "B"))) :=
  fun h => Bool.false_ne_true ((h (.arr []) rfl).symm.trans rfl)

/-! ## Admission reads the meaning, not the structure -/

/-- One name, declared `req string` and pinned to no literal, as a closed codec. -/
def tReqStrClosed : Closed := Closed.one (.object (Scoped.Body.mk {"A"} (fun _ => .req .string) none))

/-- …and a map carrying that name at a boolean, which the structure admits and the meaning
    refuses. -/
def vBoolAtA : Value := .map {"A"} (fun _ => .bool true)

/-- **The meaning refuses what a test of the names admits**: `{"A" ↦ true}` against
    `{A : req string}`. -/
theorem Closed.tReqStr_refuses : ((tReqStrClosed.meaning α).e vBoolAtA).isSome = false := rfl

end Calculus
