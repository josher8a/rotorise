import Calculus.ExactV

/-!
# §5 — exactness on the attribute side

`Adm` is the value half. `AdmA` is the attribute half, and it has no `Adm`-shaped
counterpart, which is the first reason the analysis tables could not simply be tightened.
-/

namespace Calculus

noncomputable section
/-! ## The attribute side

`Adm` is the value half. `AdmA` is the attribute half, and it has no
`Adm`-shaped counterpart — which is the first reason the analysis tables cannot simply be
renamed onto `Adm`. `AdmA` below is that counterpart's definition and its soundness proof.

The mirror is not symmetric, and the asymmetry that remains is §1's rather than this
file's: the numeric rows go through `Double.ofDec`, and `legacy` widens a read. `refine`
was listed here as a third — "cannot narrow a read" — and is not one: the row decodes and
then applies `q`. Each is a row here rather than a remark. -/

/-! ### The attribute side's rows, and the three that are not the value side's

The combinators below mirror the value side's one for one. `objRead` still filters the
*stored* names through `keepB`, and the row carries no filter to match it: `keepB` is the
constant `true` at every body, because `drop` was the one policy that dropped a name and an
open block is a codec or nothing. `keepB_wild` states that, and it is what the object proof
spends on the filter. -/

/-- An attribute-side row, once the subterms' rows are known. -/
abbrev AP := Attr → Bool

/-- …and on the attribute side, where `byStructure` reads the same two tests off an `.m`. -/
def admitOptA (o : Option (BodySpec) × AP) (a : Attr) : Bool :=
  match o.1 with
  | some spec =>
      match a with
      | .m keys g => keysOkA spec keys && literalsOkA spec keys g
      | _ => false
  | none => o.2 a

/-- …and the same count. -/
def selOptA (os : List (Option (BodySpec) × AP)) (a : Attr) : Bool :=
  match os.filter (fun o => admitOptA o a) with
  | [o] => o.2 a
  | _ => false

def allPA (P : AP) : List Attr → Bool
  | [] => true
  | x :: xs => P x && allPA P xs

def anyPA : List AP → Attr → Bool
  | [], _ => false
  | P :: Ps, a => P a || anyPA Ps a

def alignPA : List AP → Option AP → List Attr → Bool
  | [], none, [] => true
  | [], none, _ :: _ => false
  | [], some _, [] => true
  | [], some P, a :: as => P a && alignPA [] (some P) as
  | _ :: _, _, [] => false
  | P :: Ps, tail, a :: as => P a && alignPA Ps tail as

/-- The suffix's row on the read side: position for position, a length mismatch refused. -/
def zipPA : List AP → List Attr → Bool
  | [], [] => true
  | P :: Ps, a :: as => P a && zipPA Ps as
  | _, _ => false

/-- `alignL`'s row on the read side. Mirrors `alignPL`. -/
def alignPAL (pre : List AP) (sp : Option AP) (suf : List AP) (as : List Attr) : Bool :=
  alignPA pre sp (as.take (as.length - suf.length))
    && zipPA suf (as.drop (as.length - suf.length))

def entryPA (fs : MapOf AP) (rp : Option AP) (k : Name) : Option AP :=
  match fs.at k with | some P => some P | none => rp

/-- `objRead`'s traversal, as a row: every stored entry goes through its name's codec. -/
def objAdmA (fs : MapOf AP) (rp : Option AP) (keys : Finset Name)
    (g : {k // k ∈ keys} → Attr) : Bool :=
  decide (∀ k : {k // k ∈ keys},
    (match entryPA fs rp k.1 with | some P => P (g k) | none => false) = true)

/-- `reqPresentB`'s guard off the term's table: a slot with a stand-in reads to that
    stand-in, so only a `req` without one must be present. The mark alone does not decide
    it, which is why the row splits on `ifMissing`. -/
def reqPresentT (fields : Finset Name) (fld : {k // k ∈ fields} → ObjectSlot)
    (keys : Finset Name) : Bool :=
  decide (∀ k : {k // k ∈ fields},
    (match fld k with | .req _ none => decide (k.1 ∈ keys) | _ => true) = true)


/-- What the literal codec **reads**, exactly.

    Three rows into one, and the `number` row is the only one that is not simply membership:
    the read goes through `Double.ofDec`, and `&& WF` is there because the base's own read is
    `number`'s restricted, so it refuses a numeral whose double re-spells outside `D` even when
    that double is in `ℓ`.

    The retired per-aspect row was `⊤` here, on the ground that a *syntactic* set of
    attributes does not bound a read through `Double.ofDec`. True, and it never made the row
    unwritable: `ofDec` is a function the row may call, exactly as this one does. -/
noncomputable def AdmALit : (k : GroundKind) → k.Carrier → Attr → Bool
  | .string,  y, .s s    => decide (s = y)
  | .boolean, y, .bool b => decide (b = y)
  | .binary,  y, .b b    => decide (b = y)
  | .null,    _, .null   => true
  -- **The `&& Numeral.WF d.toDec` conjunct used to be written out here**, and it was the
  -- reason this row was exact while the table's `adm` row was not. It is now the
  -- carrier's: `y : WFDouble`, so the gate is what names the alternative.
  | .number,  y, .n x    => (match Double.ofDec x.1 with
                              | some d =>
                                  if h : Numeral.WF d.toDec = true then
                                    decide ((⟨d, h⟩ : WFDouble) = y)
                                  else false
                              | none => false)
  -- `decimal` asks its codec, which is what the retired per-aspect row did at this base too — so the joint row
  -- and the table row are the *same function* here rather than two spellings that have to be
  -- proved equal. `number` cannot do this and spells the `ofDec` lookup out, because its answer
  -- depends on the host's numeric type; `decimal`'s does not.
  | .decimal, y, a       => ((literalCodec .decimal y).p a).isSome
  | _, _, _ => false

/-- **What a set base reads.**

    Three bases answer concretely: `string` reads `SS` and nothing else, `binary` `BS`,
    `decimal` an `NS` every numeral of which is `Stored`. `number` **asks its codec** — the
    same move `admALit .number` (`Discharge.lean`) makes at the same base, and for a related
    but different reason.

    The reason is worth stating, because it is the one residue the re-indexing does *not*
    remove and it is not injectivity of `e`. `numberCodec.p` goes through `Double.ofDec`,
    which **rounds** (`Prisms.lean`), so two distinct stored numerals can read to the
    same double and `decSet`'s `Nodup` gate then refuses an `NS` every element of which
    reads. That is `e ∘ p ≠ id`, not `e` non-injective, and `numericHost` says nothing about
    whether it ever fires — it is decidable, through `Double.decEq`, and not describable
    syntactically, so the exact row is the codec's own answer. `AdmA` is already
    `noncomputable`, so this costs nothing it had not already spent. -/
noncomputable def AdmASet : SetBase → Attr → Bool
  | .string,  .ss _ => true
  | .binary,  .bs _ => true
  | .decimal, .ns S => decide (∀ x ∈ S.1, Numeral.Stored x.1 = true)
  | .number,  .ns S => (decSet numberCodec Attr.n S).isSome
  | _, _ => false

mutual

/-- **The joint admission predicate, attribute side.** The mirror of `Adm` across §1's
    asymmetry, and it is not a symmetric mirror — three rows differ in kind, not degree.

    * `number` and a numeric `literal` go through `Double.ofDec`, which is
      axiomatized. The domain is still *expressible* — `ofDec` is a function and this row
      may call it — at the cost of being `noncomputable`, which `adm` already was. These rows
      used to be sharper than §5's `⊤`; they are now equal to it, because the observation in
      the previous sentence is exactly the one §5's numeric rows were missing.
    * `refine` **does** narrow here, and the row that said it could not was wrong in the
      same way the numeric `⊤`s were. "`q` tests the value a read *produces*, and no
      syntactic set of attributes bounds that" is true of syntax and says nothing about a
      row, which may decode and then ask `q` (`refineReads`). Sound, and exact whenever the
      subterm's row is: `dom((c.restrict q).p)` is precisely `{a | ∃ v, c.p a = some v ∧ q v}`.
    * `legacy` is the read-side alternative: `p` is the subterm's channel falling back to
      `r`'s, and `r` is data the term carries — the asymmetry that makes the two sides' rows
      part at all. -/
noncomputable def AdmA : Term → Attr → Bool
  | .string   => fun a => match a with | .s _ => true | _ => false
  | .boolean  => fun a => match a with | .bool _ => true | _ => false
  | .binary   => fun a => match a with | .b _ => true | _ => false
  | .null     => fun a => match a with | .null => true | _ => false
  | .number   => fun a =>
      match a with
      | .n x => (match Double.ofDec x.1 with
                 | some d => Numeral.WF d.toDec
                 | none => false)
      | _ => false
  | .decimal  => fun a => match a with | .n x => Numeral.Stored x.1 | _ => false
  | .literal k ls => AdmALit k ls
  -- the bottom reads nothing back, and the row is that sentence
  | .never => fun _ => false
  | .custom _ cp => fun a => (cp a).isSome
  | .held t _ _ => AdmA t
  | .lazy t   => AdmA t
  | .refine t p => fun a => AdmA t a && refineReads t p.eval a
  -- hatch
  | .legacy t r => fun a => AdmA t a || (r a).isSome
  -- the read side of the same count; `byStructure` reads the structural test off an `.m`
  | .union opts => fun a => selOptA (AdmASpecs opts) a
  -- **the row that used to admit all three wire families whatever the element term was.**
  -- With the base an index the family is a function of it, so this names one — and at
  -- `number` defers to the codec, for the rounding residue `AdmASet` documents.
  | .set b    => AdmASet b
  -- **One row**, for the reason the value side gives: `array` and `tuple` were two rows
  -- computing different things on what is now one shape.
  | .list pre sp suf => fun a =>
      match a with
      | .l as => alignPAL (AdmAList pre) (AdmAOptT sp) (AdmAList suf) as
      | _ => false
  | .object b => AdmABody b
  -- the read side of the same deferral; see the `Adm` row and `ExactA_opaq`
  | .opaq lossy => fun a => ((opaqCodecω lossy).p a).isSome

/-- The read side's payload row; `AdmBody`'s mirror. -/
noncomputable def AdmABody : Body → AP
  | .mk fields fld wild => fun a =>
      match a with
      | .m keys g =>
          reqPresentT fields fld keys &&
          objAdmA ⟨fields, fun k => AdmAField (fld k)⟩ (AdmAWild wild) keys g
      | _ => false

noncomputable def AdmAField : ObjectSlot → AP
  | .req t _ => AdmA t
  | .optional t => AdmA t

noncomputable def AdmAWild : Option (KeyPat × Term) → Option AP
  | none => none
  | some (_, t) => some (AdmA t)

noncomputable def AdmAList : List Term → List AP
  | [] => []
  | t :: ts => AdmA t :: AdmAList ts

noncomputable def AdmAOptT : Option Term → Option AP
  | none => none
  | some t => some (AdmA t)


/-- `optionSems`' mirror on the attribute side. -/
noncomputable def AdmASpecs : List Term → List (Option (BodySpec) × AP)
  | [] => []
  | t :: ts => (specOf t, AdmA t) :: AdmASpecs ts

end

@[simp] theorem AdmAList_eq : ∀ ts : List Term, AdmAList ts = ts.map AdmA
  | [] => rfl
  | t :: ts => by simp only [AdmAList, List.map]; rw [AdmAList_eq ts]


@[simp] theorem AdmASpecs_eq : ∀ opts : List Term,
    AdmASpecs opts = opts.map fun t => (specOf t, AdmA t)
  | [] => rfl
  | t :: ts => by simp only [AdmASpecs, List.map]; rw [AdmASpecs_eq ts]

/-- `⋁` of `AdmA` over a union's options; sound, and inexact for the reason the value side
    gives. -/
noncomputable def AdmAAny (ts : List Term) (a : Attr) : Bool := anyPA (AdmAList ts) a

@[simp] theorem AdmAAny_nil (a : Attr) : AdmAAny [] a = false := rfl

@[simp] theorem AdmAAny_cons (t : Term) (ts : List Term) (a : Attr) :
    AdmAAny (t :: ts) a = (AdmA t a || AdmAAny ts a) := rfl

theorem AdmA_union (opts : List Term) (a : Attr) :
    AdmA (.union opts) a = selOptA (AdmASpecs opts) a := rfl

/-- An option that admits makes the disjunction true. -/
theorem AdmAAny_of_mem {t : Term} {ts : List Term} {a : Attr} (ht : t ∈ ts)
    (h : AdmA t a = true) : AdmAAny ts a = true := by
  induction ts with
  | nil => exact absurd ht (by simp)
  | cons t0 ts ih =>
    rcases List.mem_cons.mp ht with rfl | h'
    · simp [AdmAAny_cons, h]
    · simp [AdmAAny_cons, ih h']

/-- The count implies the disjunction — see `selOptV_le_AdmAny`. -/
theorem selOptA_le_AdmAAny {opts : List Term} {a : Attr}
    (h : selOptA (AdmASpecs opts) a = true) : AdmAAny opts a = true := by
  simp only [selOptA, AdmASpecs_eq] at h
  cases hf : (opts.map fun t => (specOf t, AdmA t)).filter (fun o => admitOptA o a) with
  | nil => rw [hf] at h; exact absurd h (by simp)
  | cons o rest =>
    cases rest with
    | cons _ _ => rw [hf] at h; exact absurd h (by simp)
    | nil =>
      rw [hf] at h
      have hmem : o ∈ opts.map fun t => (specOf t, AdmA t) :=
        (mem_of_filter_eq_singleton hf).1
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
      exact AdmAAny_of_mem ht h

/-- `AdmA`'s literal row, named — for the reason `Adm_literal` gives. -/
@[simp] theorem AdmA_literal (k : GroundKind) (x : k.Carrier) (a : Attr) :
    AdmA (.literal k x) a = AdmALit k x a := by unfold AdmA; rfl

/-! The four bases whose stored attribute *is* the value, stated as standalone lemmas with
their carriers written out.

`GroundKind.Carrier` is reducible, so `k.Carrier` at a *constructor* `k` is the same type as
`Bytes` — but it is not the same *expression*, and `simp` inside the goal
re-derives that on every rewrite. At `binary` (`List UInt8`) and `null` (`Unit`) that was
enough to exhaust the heartbeat budget. Taking the carrier as a plain type in the statement
does the reduction once, at elaboration.

`string` and `boolean` are here for the same reason and not because they failed: inline in
`AdmA_exact` they were re-derived inside a twenty-case fan, and the row each one needs is a
statement about *one* base. `AdmA_exact` cites all four and unfolds none. -/

theorem AdmALit_binary_exact (y : Bytes) (a : Attr) :
    AdmA (.literal .binary y) a = true ↔ ((denote (Term.literal .binary y)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          binaryCodec]

theorem AdmALit_null_exact (y : Unit) (a : Attr) :
    AdmA (.literal .null y) a = true ↔ ((denote (Term.literal .null y)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          nullCodec]

/-- `(literal)` at `string`, read side. `String` and not `k.Carrier`: the carrier reduces once
    here instead of on every rewrite. -/
theorem AdmALit_string_exact (y : String) (a : Attr) :
    AdmA (.literal .string y) a = true ↔ ((denote (Term.literal .string y)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          stringCodec]

/-- `(literal)` at `boolean`, read side. Same shape as `AdmALit_string_exact`, and the two
    cannot share a `simp` set — one of them would have to name the other's codec. -/
theorem AdmALit_boolean_exact (y : Bool) (a : Attr) :
    AdmA (.literal .boolean y) a = true ↔ ((denote (Term.literal .boolean y)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          booleanCodec]


/-- The converse direction on the attribute side: the row is `dom(p)`, not a bound on it. -/
def ExactA (t : Term) : Prop := ∀ a, AdmA t a = true ↔ ((denote t).p a).isSome

/-- The read-side agreement, option by option — `admitOptV_eq`'s twin. -/
theorem admitOptA_eq {t : Term} (h : ExactA t) (a : Attr) :
    (optionSemOf (denote t) (specOf t)).admitA a = admitOptA (specOf t, AdmA t) a := by
  unfold admitOptA
  cases hs : specOf t with
  | some spec => rfl
  | none =>
    simp only [optionSemOf, OptionSem.byAttempt]
    exact Bool.coe_iff_coe.mp (by simpa using (h a).symm)

/-- The row's own filter, pushed through the map. -/
theorem filter_map_AdmASpecs (opts : List Term) (a : Attr) :
    (opts.map fun t => (specOf t, AdmA t)).filter (fun o => admitOptA o a)
      = (opts.filter fun t => admitOptA (specOf t, AdmA t) a).map
          fun t => (specOf t, AdmA t) := by
  induction opts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.filter_cons, ih]
    cases hb : admitOptA (specOf t, AdmA t) a <;> simp []

/-- `select`'s filter is the term list's, mapped — `filter_AdmSpecs`'s twin. -/
theorem filter_AdmASpecs {opts : List Term} (h : ∀ t ∈ opts, ExactA t) (a : Attr) :
    (optionSems opts).filter (·.admitA a)
      = (opts.filter (fun t => admitOptA (specOf t, AdmA t) a)).map
          (fun t => optionSemOf (denote t) (specOf t)) := by
  induction opts with
  | nil => rfl
  | cons t ts ih =>
    have ht : ExactA t := h t (by simp)
    have hts : ∀ t' ∈ ts, ExactA t' := fun t' h' => h t' (by simp [h'])
    simp only [optionSems, List.filter_cons, admitOptA_eq ht, ih hts]
    cases hb : admitOptA (specOf t, AdmA t) a <;> simp []

/-- **`union` reads exactly what its row says** — `ExactV_union` on the other side of the
    pair, and the same two rewrites. `select` is stated once over both halves
    (`Sums.lean`), which is why this proof is the value side's verbatim. -/
theorem ExactA_union {opts : List Term} (h : ∀ t ∈ opts, ExactA t) : ExactA (.union opts) := by
  intro a
  rw [denote_union_sems]
  show selOptA (AdmASpecs opts) a = true ↔ (select (optionSems opts) (·.admitA) (·.c.p) a).isSome
  rw [AdmASpecs_eq]
  unfold select selOptA
  rw [filter_map_AdmASpecs opts a, filter_AdmASpecs h a]
  cases hf : opts.filter (fun t => admitOptA (specOf t, AdmA t) a) with
  | nil => simp
  | cons t rest =>
    cases rest with
    | nil =>
      have ht : ExactA t := h t (mem_of_filter_eq_singleton hf).1
      simpa [optionSemOf_c] using ht a
    | cons t2 r2 => simp

/-- **`set` reads exactly what its row says.**

    Four bases, eleven attribute constructors, and the argument is the same three moves in
    each cell: `decSet` succeeds on the branch the base's `p` lands in, and fails at the
    first element that base refuses (`decSet_isSome_false`). `number` is the cell that is
    `rfl`, because its row *is* the codec's answer — see `AdmASet` for why it has to be. -/
theorem ExactA_set (b : SetBase) : ExactA (.set b) := by
  intro a
  show AdmASet b a = true ↔ ((setCodec b.elem).p a).isSome = true
  cases a
  case ss S =>
    cases b
    case string =>
      have h : (decSet stringCodec Attr.s S).isSome = true :=
        decSet_isSome_str (fun _ _ => rfl) (fun _ _ _ _ _ h1 h2 => by
          simp only [stringCodec, Option.bind_some, vStr] at h1 h2
          exact (Option.some.inj h1).trans (Option.some.inj h2).symm)
      exact Iff.intro (fun _ => h) (fun _ => rfl)
    all_goals
      obtain ⟨x, hx⟩ := S.2
      simp only [AdmASet, SetBase.elem, setCodec]
      rw [decSet_isSome_false hx rfl]
  case ns S =>
    cases b
    case number => exact Iff.rfl
    case decimal =>
      show decide (∀ x ∈ S.1, Numeral.Stored x.1 = true) = true
        ↔ (decSet decimalCodec Attr.n S).isSome = true
      rw [decide_eq_true_eq]
      constructor
      · intro hst
        have hp : ∀ x ∈ S.1, (decimalCodec.p (Attr.n x)).bind vStr = some x.1 := by
          intro x hx
          show ((if Numeral.Stored x.1 then some (Value.str x.1) else none).bind vStr)
            = some x.1
          rw [if_pos (hst x hx)]; rfl
        refine decSet_isSome_str (fun x hx => by rw [hp x hx]; rfl) ?_
        intro x₁ h₁ x₂ h₂ y e₁ e₂
        rw [hp x₁ h₁] at e₁; rw [hp x₂ h₂] at e₂
        exact Subtype.ext ((Option.some.inj e₁).trans (Option.some.inj e₂).symm)
      · intro hd x hx
        by_contra hc
        have hn : decimalCodec.p (Attr.n x) = none := by
          show (if Numeral.Stored x.1 then some (Value.str x.1) else none) = none
          rw [if_neg hc]
        rw [decSet_isSome_false hx hn] at hd
        exact nomatch hd
    all_goals
      obtain ⟨x, hx⟩ := S.2
      simp only [AdmASet, SetBase.elem, setCodec]
      rw [decSet_isSome_false hx rfl]
  case bs S =>
    cases b
    case binary =>
      obtain ⟨x₀, hx₀⟩ := S.2
      have h : (decSet binaryCodec Attr.b S).isSome = true :=
        decSet_isSome_bin hx₀ rfl rfl (fun _ _ => rfl) (fun _ _ _ _ _ h1 h2 => by
          simp only [binaryCodec, Option.bind_some, vBin] at h1 h2
          exact (Option.some.inj h1).trans (Option.some.inj h2).symm)
      exact Iff.intro (fun _ => h) (fun _ => rfl)
    all_goals
      obtain ⟨x, hx⟩ := S.2
      simp only [AdmASet, SetBase.elem, setCodec]
      rw [decSet_isSome_false hx rfl]
  all_goals cases b <;> exact Iff.intro (fun h => nomatch h) (fun h => nomatch h)

theorem alignPA_iff (tail : Option Term) (htl : ∀ t ∈ tail, ExactA t) :
    ∀ (ts : List Term) (as : List Attr), (∀ t ∈ ts, ExactA t) →
      (alignPA (AdmAList ts) (AdmAOptT tail) as = true ↔
        ((align (denoteList ts) (denoteOpt tail) as).bind
          (traverse fun ca => ca.1.p ca.2)).isSome = true)
  | [], [], _ => by
      cases tail <;> simp [alignPA, AdmAList, AdmAOptT, align, denoteList, denoteOpt, traverse]
  | [], a :: as, _ => by
      cases htail : tail with
      | none => simp [alignPA, AdmAList, AdmAOptT, align, denoteList, denoteOpt]
      | some t =>
        have ht : ExactA t := htl t (by simp [htail])
        have ih := alignPA_iff tail htl [] as (by simp)
        rw [htail] at ih
        simp only [AdmAList, AdmAOptT, denoteList, denoteOpt] at ih
        simp only [alignPA, AdmAList, AdmAOptT, align, denoteList, denoteOpt,
          Bool.and_eq_true]
        cases hal : align [] (some (denote t)) as with
        | none =>
          rw [hal] at ih
          simp at ih
          simp [ih]
        | some ps =>
          rw [hal] at ih
          simp only [Option.map_some, Option.bind_some] at ih ⊢
          rw [traverse_cons_isSome, Bool.and_eq_true, ← ht a, ← ih]
  | t :: ts, [], _ => by
      cases tail <;> simp [alignPA, AdmAList, AdmAOptT, align, denoteList, denoteOpt]
  | t :: ts, a :: as, h => by
      have ht : ExactA t := h t (by simp)
      have ih := alignPA_iff tail htl ts as (fun t' ht' => h t' (by simp [ht']))
      simp only [alignPA, AdmAList, align, denoteList, Bool.and_eq_true]
      cases hal : align (denoteList ts) (denoteOpt tail) as with
      | none =>
        simp only [hal, Option.map_none, Option.bind_none, Option.isSome_none] at ih ⊢
        simp at ih
        simp [ih]
      | some ps =>
        simp only [hal, Option.map_some, Option.bind_some] at ih ⊢
        rw [traverse_cons_isSome, Bool.and_eq_true, ← ht a, ← ih]

/-- A suffix row that holds pins the length. -/
theorem zipPA_length : ∀ (Ps : List AP) (as : List Attr),
    zipPA Ps as = true → Ps.length = as.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [zipPA] at h
  | _ :: _, [], h => by simp [zipPA] at h
  | _ :: Ps, _ :: as, h => by
      simp only [zipPA, Bool.and_eq_true] at h
      simp [zipPA_length Ps as h.2]

/-- The suffix's row, transported across its positions' exactness. The length premise is
    load bearing for the reason `zipP_iff`'s is: `List.zip` truncates. -/
theorem zipPA_iff : ∀ (suf : List Term), (∀ t ∈ suf, ExactA t) → ∀ (back : List Attr),
    back.length = suf.length →
    (zipPA (AdmAList suf) back = true ↔
      (traverse (fun ca : Codec × Attr => ca.1.p ca.2)
        ((denoteList suf).zip back)).isSome = true)
  | [], _, [], _ => by simp [zipPA, AdmAList, denoteList]
  | [], _, _ :: _, h => by
      exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _, _, [], h => by
      exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | t :: ts, h, a :: as, hlen => by
      simp only [AdmAList, denoteList, zipPA, List.zip_cons_cons, Bool.and_eq_true,
        traverse_cons_isSome]
      rw [zipPA_iff ts (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) as
          (by simp only [List.length_cons] at hlen; omega),
        h t List.mem_cons_self a]

/-- **`alignPAL` is `alignL`'s row on the read side.** -/
theorem alignPAL_iff (pre : List Term) (sp : Option Term) (suf : List Term)
    (hpre : ∀ t ∈ pre, ExactA t) (hsp : ∀ t ∈ sp, ExactA t) (hsuf : ∀ t ∈ suf, ExactA t)
    (as : List Attr) :
    alignPAL (AdmAList pre) (AdmAOptT sp) (AdmAList suf) as = true ↔
      ((alignL (denoteList pre) (denoteOpt sp) (denoteList suf) as).bind
        (traverse fun ca => ca.1.p ca.2)).isSome = true := by
  have hlenA : (AdmAList suf).length = suf.length := by simp
  have hlenD : (denoteList suf).length = suf.length := by simp
  unfold alignPAL
  rw [hlenA]
  rcases Nat.lt_or_ge as.length suf.length with hlt | hge
  · rw [alignL_short _ _ _ _ (by omega)]
    have h0 : as.length - suf.length = 0 := by omega
    rw [h0, List.drop_zero]
    refine ⟨fun hc => ?_, fun hc => nomatch hc⟩
    have := zipPA_length _ _ (Bool.and_eq_true .. ▸ hc |>.2)
    rw [hlenA] at this
    omega
  · rw [alignL_eq_split _ _ _ _ (by omega), hlenD]
    rw [Bool.and_eq_true, alignPA_iff sp hsp pre (as.take (as.length - suf.length)) hpre,
      zipPA_iff suf hsuf _ (by simp; omega)]
    cases hal : align (denoteList pre) (denoteOpt sp) (as.take (as.length - suf.length)) with
    | none => simp
    | some ps => simp [traverse_append_isSome]

/-- **`list` reads exactly** once its three parts do. -/
theorem ExactA_list {pre : List Term} {sp : Option Term} {suf : List Term}
    (hpre : ∀ t ∈ pre, ExactA t) (hsp : ∀ t ∈ sp, ExactA t) (hsuf : ∀ t ∈ suf, ExactA t) :
    ExactA (.list pre sp suf) := by
  intro a
  cases a
  case l as =>
    show alignPAL (AdmAList pre) (AdmAOptT sp) (AdmAList suf) as = true ↔
      (((alignL (denoteList pre) (denoteOpt sp) (denoteList suf) as).bind
        (traverse fun ca => ca.1.p ca.2)).map Value.arr).isSome = true
    rw [alignPAL_iff pre sp suf hpre hsp hsuf as]
    cases (alignL (denoteList pre) (denoteOpt sp) (denoteList suf) as).bind
      (traverse fun ca => ca.1.p ca.2) <;> simp
  all_goals simp [AdmA, denote, listCodec]

theorem ExactA_tuple {ts : List Term} {tail : Option Term}
    (h : ∀ t ∈ ts, ExactA t) (htl : ∀ t ∈ tail, ExactA t) : ExactA (.tuple ts tail) :=
  ExactA_list h htl (by simp)

/-- **`array` reads exactly** once its element does. -/
theorem ExactA_array {c : Term} (hc : ExactA c) : ExactA (.array c) :=
  ExactA_list (by simp) (by simpa using hc) (by simp)

def ExactAField (fd : ObjectSlot) : Prop :=
  ∀ a, AdmAField fd a = true ↔ (((fieldSem fd).codec).p a).isSome

theorem reqPresentT_eq (fields : Finset Name) (fld : {k // k ∈ fields} → ObjectSlot)
    (keys : Finset Name) :
    reqPresentT fields fld keys = reqPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys := by
  simp only [reqPresentT, reqPresentB]
  congr 1
  apply propext
  -- `fieldSem (.req t m)` does not reduce while `m` is a variable, and the two rows it
  -- splits into are the two answers this guard gives.
  constructor <;> intro h k <;> have := h k <;>
    (cases hfd : fld k with
      | req t m => cases m <;> simp_all [reqPresentAt, fieldSem]
      | optional t => simp_all [reqPresentAt, fieldSem])

/-- **The read side keeps every stored name.** `drop` was the one policy that dropped one,
    and it is gone, so `objRead`'s filter is the identity on the key set and the row owes it
    nothing. -/
theorem keepB_wild (wild : Option (KeyPat × Term)) (sems : MapOf FieldSem) (k : Name) :
    keepB (wildSem wild) sems k = true := by
  cases wild with
  | none => rfl
  | some pt => rfl

theorem entryA_iff {fields : Finset Name} {fld : {k // k ∈ fields} → ObjectSlot}
    {wild : Option (KeyPat × Term)}
    (hf : ∀ k : {k // k ∈ fields}, ExactAField (fld k))
    (hr : ∀ p t, wild = some (p, t) → ExactA t) (k : Name) (a : Attr) :
    (match entryPA ⟨fields, fun k => AdmAField (fld k)⟩ (AdmAWild wild) k with
      | some P => P a | none => false) = true ↔
    ((entryCodec ⟨fields, fun k => fieldSem (fld k)⟩ (rcOf (wildSem wild)) k).bind
      (fun c => c.p a)).isSome = true := by
  simp only [entryPA, entryCodec, MapOf.at]
  by_cases hk : k ∈ fields
  · rw [dif_pos hk, dif_pos hk]
    simpa using hf ⟨k, hk⟩ a
  · rw [dif_neg hk, dif_neg hk]
    cases wild with
    | none => simp [AdmAWild, wildSem, rcOf]
    | some pt => simpa [AdmAWild, wildSem, rcOf] using hr pt.1 pt.2 rfl a

theorem ExactA_object {fields : Finset Name} {fld : {k // k ∈ fields} → ObjectSlot}
    {wild : Option (KeyPat × Term)}
    (hf : ∀ k : {k // k ∈ fields}, ExactAField (fld k))
    (hr : ∀ p t, wild = some (p, t) → ExactA t) :
    ExactA (.object (.mk fields fld wild)) := by
  intro a
  cases a
  case m keys g =>
    show (reqPresentT fields fld keys &&
        objAdmA ⟨fields, fun k => AdmAField (fld k)⟩ (AdmAWild wild) keys g) = true ↔
      ((objectCodec ⟨fields, fun k => fieldSem (fld k)⟩ (wildSem wild)).p (.m keys g)).isSome
        = true
    rw [reqPresentT_eq]
    simp only [objectCodec, objectCodecCore, carriedCodec, mA, objRead,
      objAdmA, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_map,
      Option.bind_some]
    by_cases hv : reqPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys = true
    · rw [if_pos hv]
      simp only [hv, true_and, Option.isSome_map, funImage_isSome_iff]
      constructor
      · intro h k
        exact (entryA_iff hf hr k.1 _).mp (h ⟨k.1, (Finset.mem_filter.mp k.2).1⟩)
      · intro h k
        refine (entryA_iff hf hr k.1 (g k)).mpr ?_
        have hmem : k.1 ∈ keys.filter (keepB (wildSem wild) ⟨fields, fun k => fieldSem (fld k)⟩ ·) :=
          Finset.mem_filter.mpr ⟨k.2, keepB_wild wild _ k.1⟩
        exact h ⟨k.1, hmem⟩
    · rw [if_neg hv]
      simp [hv]
  all_goals
    simp [AdmA, AdmABody, denote, bodySem, objectCodec, objectCodecCore, carriedCodec, mA]

/-- **`opaque` reads exactly what its row says**, definitionally, and for the reason
    `ExactV_opaq` gives at length: `p := (opaqCodecω lossy).p`, so the row and `dom(p)` are
    one function. ~~AdmOpaqA_iff~~ — a second induction, this one carrying an injectivity
    clause about `Double.ofDec` that `decSet` needs — is deleted rather than moved. The
    clause was true and is still true; it is now the codec's business, where it was always
    stated (`decSet`, `Products.lean`), instead of being restated here in a form that had
    to be kept in step by hand. -/
theorem ExactA_opaq (lossy : Bool) : ExactA (.opaq lossy) := fun _ => Iff.rfl


def ExactAL : List Term → Prop
  | [] => True
  | t :: ts => ExactA t ∧ ExactAL ts

def ExactAO : Option Term → Prop
  | none => True
  | some t => ExactA t

def ExactAW : Option (KeyPat × Term) → Prop
  | none => True
  | some (_, t) => ExactA t

theorem exactAL_mem : ∀ (ts : List Term), ExactAL ts → ∀ t ∈ ts, ExactA t
  | [], _, t, ht => absurd ht (by simp)
  | t0 :: ts, h, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact h.1
      · exact exactAL_mem ts h.2 t ht'

theorem exactAO_mem : ∀ (tail : Option Term), ExactAO tail → ∀ t ∈ tail, ExactA t
  | none, _, t, ht => absurd ht (by simp)
  | some t0, h, t, ht => by
      have heq : t0 = t := by simpa using ht
      subst heq; exact h

theorem exactAW_codec : ∀ (wild : Option (KeyPat × Term)), ExactAW wild →
    ∀ p t, wild = some (p, t) → ExactA t
  | none, _, _, t, h => nomatch h
  | some (_, t0), h, _, t, hc => by
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      exact hc.2 ▸ h

/-- `allPA` transported across the entry's exactness. -/
theorem AdmAAll_iff {c : Term} (h : ExactA c) : ∀ as : List Attr,
    allPA (AdmA c) as = true ↔ ∀ a ∈ as, ((denote c).p a).isSome = true := by
  intro as; induction as with
  | nil => simp [allPA]
  | cons a as ih => simp [allPA, ih, h a]

mutual
/-- **Every attribute row is exact** — all twenty-one, as on the value side, and nothing
    declines on either. `refine` was the last difference between
    the two sides and is exact now: its row decodes and then applies `q`. `legacy`,
    which used to be the other half of that asymmetry, is exact here because its row is the
    union of the two channels it reads on.

    The numeric rows are the interesting ones: they reach `dom(p)` through `Double.ofDec`,
    which is axiomatized, and are exact anyway — a row may *call* an axiomatized function
    even though no finite set of numerals describes its domain. §5 wrote `⊤` there. -/
theorem AdmA_exact : ∀ (t : Term), ExactA t
  -- the rows §5 excused on this side too
  | .list pre sp suf =>
      ExactA_list (exactAL_mem pre (AdmA_exactL pre)) (exactAO_mem sp (AdmA_exactO sp))
        (exactAL_mem suf (AdmA_exactL suf))
  | .object b => AdmA_exactB b
  | .opaq lossy => ExactA_opaq lossy
  -- both sides are empty, so the equivalence is `False ↔ False`
  | .never => fun _ => Iff.rfl
  -- exact because the constructor narrowed, not because the row sharpened
  | .set b => ExactA_set b
  -- see `ExactA_union`
  | .union opts => ExactA_union (exactAL_mem opts (AdmA_exactL opts))

  | .string => by intro a; cases a <;> simp [AdmA, denote, denote, stringCodec]
  | .boolean => by intro a; cases a <;> simp [AdmA, denote, denote, booleanCodec]
  | .binary => by intro a; cases a <;> simp [AdmA, denote, denote, binaryCodec]
  | .null => by intro a; cases a <;> simp [AdmA, denote, denote, nullCodec]
  | .number => by
      intro a
      cases a
      case n x =>
        simp only [AdmA, denote, denote, denote, numberCodec]
        cases hx : Double.ofDec x.1 <;> simp []
      all_goals simp [AdmA, denote, denote, numberCodec]
  | .decimal => by intro a; cases a <;> simp [AdmA, denote, denote, decimalCodec]
  -- Three rows into one. The `number` base is the only one needing `Double.ofDec`, and it is
  -- also the only one where unfolding `numberCodec` is safe here: the `simp only` fixes the
  -- shape before `Numeral.WF`'s parser can be reached.
  | .literal k ls => by
      intro a
      cases k
      -- the row asks the codec, so the biconditional is the row read twice
      case decimal => simp [AdmA, AdmALit, denote]
      case number =>
        cases a
        case n x =>
          -- through the named shape lemmas, not by unfolding `numberCodec`: its `p` is a
          -- `bind` over `Double.ofDec` guarded by `Numeral.WF`, and `simp` inside that gate
          -- reaches the parser and runs out of heartbeats
          rw [show (denote (Term.literal .number ls)).p (.n x)
                 = (literalCodec .number ls).p (.n x) from rfl,
             literalNCodec_p_n, numberCodec_p_n]
          cases hx : Double.ofDec x.1 with
          | none => simp [hx, AdmALit]
          | some d =>
            by_cases hw : Numeral.WF d.toDec = true <;>
              simp [hx, hw, AdmALit, inL]
        -- for every other attribute the base's own read is `none` by a match, so this is
        -- `rfl` once `AdmA`'s recursion is unfolded — no `numberCodec` in the simp set
        all_goals (simp only [AdmA_literal, AdmALit]; rfl)
      -- the four bases whose stored attribute *is* the value, one tight simp set each: a
      -- shared set has to mention every base's codec, and one of those is `number`
      case string => exact AdmALit_string_exact ls a
      case boolean => exact AdmALit_boolean_exact ls a
      case binary => exact AdmALit_binary_exact ls a
      case null => exact AdmALit_null_exact ls a
  | .custom ce cp => by intro a; simp [AdmA, denote, denote]
  | .held c f g => by
      have hc := AdmA_exact c
      intro a
      simp only [AdmA, denote, denote, denote, Codec.through]
      rw [hc a]
      cases (denote c).p a <;> simp
  -- **the row this file said could not exist.** `restrict`'s `p` is the base's `bind`ed
  -- through `q`, so `dom(p)` is `dom` of the base's intersected with `q` of what it decodes
  -- to — and that is what the row computes, term for term.
  | .refine c p => by
      have hc := AdmA_exact c
      intro a
      simp only [AdmA, refineReads, denote_refine, Codec.restrict, Bool.and_eq_true, hc a]
      cases hx : (denote c).p a <;> simp []
  | .lazy c => by
      have hc := AdmA_exact c
      intro a; simpa [AdmA, denote] using hc a
  | .legacy c r => by
      have hc := AdmA_exact c
      intro a
      simp only [AdmA, denote, denote, denote, Codec.extendRead]
      cases hx : (denote c).p a <;> simp [hc a, hx]

/-- …and its read-side twin, for the reason the write side gives. -/
theorem AdmA_exactB : ∀ (b : Body), ExactA (.object b)
  | .mk _ fld wild =>
      ExactA_object (fun k => AdmA_exactF (fld k)) (exactAW_codec wild (AdmA_exactW wild))

theorem AdmA_exactL : ∀ (ts : List Term), ExactAL ts
  | [] => trivial
  | t0 :: ts => ⟨AdmA_exact t0, AdmA_exactL ts⟩

theorem AdmA_exactO : ∀ (tail : Option Term), ExactAO tail
  | none => trivial
  | some t0 => AdmA_exact t0

/-- The stand-in splits because `fieldSem (.req t m)` does not reduce while `m` is a
    variable, the same split `Adm_exactF` makes. -/
theorem AdmA_exactF : ∀ (fd : ObjectSlot), ExactAField fd
  | .req t0 none => fun a => AdmA_exact t0 a
  | .req t0 (some _) => fun a => AdmA_exact t0 a
  | .optional t0 => fun a => AdmA_exact t0 a

theorem AdmA_exactW : ∀ (wild : Option (KeyPat × Term)), ExactAW wild
  | none => trivial
  | some (_, t0) => AdmA_exact t0
end

/-- Soundness of every attribute row — a corollary, as on the value side. The
    hundred-and-thirty-line depth recursion this was, and the ~~SoundA~~ scaffolding it needed,
    are deleted: `AdmA_exact` carries no hypothesis, so the weaker half comes free. -/
theorem AdmA_sound (t : Term) {a v} (hp : (denote t).p a = some v) : AdmA t a = true :=
  (AdmA_exact t a).mpr (by rw [hp]; rfl)

/-- **The witness that is now a theorem the other way.** `refine(string, ⊥)` reads nothing,
    and `AdmA` says so: the row decodes with `stringCodec` and applies `⊥`. This used to be
    ~~not_ExactA_refine~~, stated as "`AdmA` cannot see it". -/
theorem AdmA_refine_bot (a : Attr) : AdmA (.refine .string (.closure (fun _ => false))) a = false := by
  simp [AdmA, refineReads, Pred.eval]
  cases a <;> simp [denote, stringCodec]

end

end Calculus
