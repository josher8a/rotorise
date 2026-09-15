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

The combinators below mirror the value side's one for one, with one genuine difference:
`objRead` filters the *stored* names through `keepB` before traversing — `drop` is a read-side
policy — so `objAdmA` carries the filter and `objAdmV` does not. The filter is written as an
implication over the key set rather than as a `Finset.filter` on the subtype, because the two
predicates (`keepB` on the denoted table, `keepT` on the term's) are equal and not
*definitionally* equal, and a filtered subtype would make that difference a transport. -/

/-- An attribute-side row, once the subterms' rows are known. -/
abbrev AP := Attr → Bool

/-- …and on the attribute side, where `byStructure` reads the same two tests off an `.m`. -/
def admitOptA (o : Option (MapOf NameSpec) × AP) (a : Attr) : Bool :=
  match o.1 with
  | some spec =>
      match a with
      | .m keys g => keysOk spec keys && literalsOkA spec keys g
      | _ => false
  | none => o.2 a

/-- …and the same count. -/
def selOptA (os : List (Option (MapOf NameSpec) × AP)) (a : Attr) : Bool :=
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

def entryPA (fs : MapOf AP) (rp : Option AP) (k : Name) : Option AP :=
  match fs.at k with | some P => some P | none => rp

/-- `objRead`'s traversal, as a row: every *kept* entry goes through its name's codec. -/
def objAdmA (fs : MapOf AP) (rp : Option AP) (kn : Name → Bool) (keys : Finset Name)
    (g : {k // k ∈ keys} → Attr) : Bool :=
  decide (∀ k : {k // k ∈ keys}, kn k.1 = true →
    (match entryPA fs rp k.1 with | some P => P (g k) | none => false) = true)

/-- `reqPresentB`'s guard off the term's table: `fb` reads to its stand-in, so only `req`
    must be present. -/
def reqPresentT (fields : Finset Name) (fld : {k // k ∈ fields} → Field)
    (keys : Finset Name) : Bool :=
  decide (∀ k : {k // k ∈ fields},
    (match fld k with | .req _ => decide (k.1 ∈ keys) | _ => true) = true)

/-- `keepB`'s row: `drop` keeps declared names, the other two keep everything. -/
def keepT (rest : Rest) (fields : Finset Name) : Name → Bool :=
  match rest with
  | .drop => fun k => decide (k ∈ fields)
  | _ => fun _ => true


/-- What the literal codec **reads**, exactly.

    Three rows into one, and the `number` row is the only one that is not simply membership:
    the read goes through `Double.ofDec`, and `&& WF` is there because the base's own read is
    `number`'s restricted, so it refuses a numeral whose double re-spells outside `D` even when
    that double is in `ℓ`.

    The retired per-aspect row was `⊤` here, on the ground that a *syntactic* set of
    attributes does not bound a read through `Double.ofDec`. True, and it never made the row
    unwritable: `ofDec` is a function the row may call, exactly as this one does. -/
noncomputable def AdmALit : (k : GroundKind) → NEFinset k.Carrier → Attr → Bool
  | .string,  ls, .s s    => decide (s ∈ ls.1)
  | .boolean, ls, .bool b => decide (b ∈ ls.1)
  | .binary,  ls, .b b    => decide (b ∈ ls.1)
  | .null,    _,  .null   => true
  -- **The `&& Numeral.WF d.toDec` conjunct used to be written out here**, and it was the
  -- reason this row was exact while the table's `adm` row was not. It is now the
  -- carrier's: `ls : NEFinset WFDouble`, so the gate is what names the alternative.
  | .number,  ls, .n x    => (match Double.ofDec x.1 with
                              | some d =>
                                  if h : Numeral.WF d.toDec = true then
                                    decide ((⟨d, h⟩ : WFDouble) ∈ ls.1)
                                  else false
                              | none => false)
  -- `decimal` asks its codec, which is what the retired per-aspect row did at this base too — so the joint row
  -- and the table row are the *same function* here rather than two spellings that have to be
  -- proved equal. `number` cannot do this and spells the `ofDec` lookup out, because its answer
  -- depends on the host's numeric type; `decimal`'s does not.
  | .decimal, ls, a       => ((literalCodec .decimal ls).p a).isSome
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
  | .array c  => fun a => match a with | .l as => allPA (AdmA c) as | _ => false
  | .record c => fun a =>
      match a with | .m _ g => decide (∀ k, AdmA c (g k) = true) | _ => false
  | .held t _ _ => AdmA t
  | .lazy t   => AdmA t
  | .refine t p => fun a => AdmA t a && refineReads t p.eval a
  -- hatch
  | .legacy t r => fun a => AdmA t a || (r a).isSome
  -- the read side of the same question; see the `Adm` row. `withNull` guards *both* halves
  -- on the same `ownsNull`, so the conjunct is identical rather than a mirror of it.
  | .nullable t => fun a =>
      AdmA t a || ((match a with | .null => true | _ => false) && !(denote t).ownsNull)
  -- the read side of the same count; `byStructure` reads the structural test off an `.m`
  | .union opts => fun a => selOptA (AdmASpecs opts) a
  -- **the row that used to admit all three wire families whatever the element term was.**
  -- With the base an index the family is a function of it, so this names one — and at
  -- `number` defers to the codec, for the rounding residue `AdmASet` documents.
  | .set b    => AdmASet b
  | .tuple ts tail => fun a =>
      match a with | .l as => alignPA (AdmAList ts) (AdmAOptT tail) as | _ => false
  | .object b => AdmABody b
  -- the read side of the same deferral; see the `Adm` row and `ExactA_opaq`
  | .opaq lossy => fun a => ((opaqCodecω lossy).p a).isSome

/-- The read side's payload row; `AdmBody`'s mirror. -/
noncomputable def AdmABody : Body → AP
  | .mk fields fld rest => fun a =>
      match a with
      | .m keys g =>
          reqPresentT fields fld keys &&
          objAdmA ⟨fields, fun k => AdmAField (fld k)⟩ (AdmARest rest)
            (keepT rest fields) keys g
      | _ => false

noncomputable def AdmAField : Field → AP
  | .req t => AdmA t
  | .optional t => AdmA t
  | .fallback t _ => AdmA t

noncomputable def AdmARest : Rest → Option AP
  | .drop => none
  | .refuse => none
  | .codec t => some (AdmA t)

noncomputable def AdmAList : List Term → List AP
  | [] => []
  | t :: ts => AdmA t :: AdmAList ts

noncomputable def AdmAOptT : Option Term → Option AP
  | none => none
  | some t => some (AdmA t)


/-- `optionSems`' mirror on the attribute side. -/
noncomputable def AdmASpecs : List Term → List (Option (MapOf NameSpec) × AP)
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
@[simp] theorem AdmA_literal (k : GroundKind) (ls : NEFinset k.Carrier) (a : Attr) :
    AdmA (.literal k ls) a = AdmALit k ls a := by unfold AdmA; rfl

/-! The four bases whose stored attribute *is* the value, stated as standalone lemmas with
their carriers written out.

`GroundKind.Carrier` is reducible, so `NEFinset k.Carrier` at a *constructor* `k` is the same
type as `NEFinset Bytes` — but it is not the same *expression*, and `simp` inside the goal
re-derives that on every rewrite. At `binary` (`List UInt8`) and `null` (`Unit`) that was
enough to exhaust the heartbeat budget. Taking the carrier as a plain type in the statement
does the reduction once, at elaboration.

`string` and `boolean` are here for the same reason and not because they failed: inline in
`AdmA_exact` they were re-derived inside a twenty-case fan, and the row each one needs is a
statement about *one* base. `AdmA_exact` cites all four and unfolds none. -/

theorem AdmALit_binary_exact (ls : NEFinset Bytes) (a : Attr) :
    AdmA (.literal .binary ls) a = true ↔ ((denote (Term.literal .binary ls)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          binaryCodec]

theorem AdmALit_null_exact (ls : NEFinset Unit) (a : Attr) :
    AdmA (.literal .null ls) a = true ↔ ((denote (Term.literal .null ls)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          nullCodec]

/-- `(literal)` at `string`, read side. `NEFinset String` and not `NEFinset k.Carrier`: the
    carrier reduces once here instead of on every rewrite. -/
theorem AdmALit_string_exact (ls : NEFinset String) (a : Attr) :
    AdmA (.literal .string ls) a = true ↔ ((denote (Term.literal .string ls)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec,
          stringCodec]

/-- `(literal)` at `boolean`, read side. Same shape as `AdmALit_string_exact`, and the two
    cannot share a `simp` set — one of them would have to name the other's codec. -/
theorem AdmALit_boolean_exact (ls : NEFinset Bool) (a : Attr) :
    AdmA (.literal .boolean ls) a = true ↔ ((denote (Term.literal .boolean ls)).p a).isSome = true := by
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

/-- **`nullable` reads exactly what its row says.** The same two cases as `ExactV_nullable`,
    against the same guard: `withNull` gates *both* halves of the pair on one `ownsNull`, so
    the read side needs no separate argument and gets none. -/
theorem ExactA_nullable {t : Term} (h : ExactA t) : ExactA (.nullable t) := by
  intro a
  rw [denote_nullable]
  simp only [AdmA, Codec.withNull]
  cases hw : (denote t).ownsNull with
  | true => simp [h a]
  | false =>
    simp only [Bool.not_false, Bool.and_true, if_false, Bool.false_eq_true, addPoint]
    cases a <;> simp [h _]

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

theorem ExactA_tuple {ts : List Term} {tail : Option Term}
    (h : ∀ t ∈ ts, ExactA t) (htl : ∀ t ∈ tail, ExactA t) : ExactA (.tuple ts tail) := by
  intro a
  cases a
  case l as =>
    show alignPA (AdmAList ts) (AdmAOptT tail) as = true ↔
      (((align (denoteList ts) (denoteOpt tail) as).bind
        (traverse fun ca => ca.1.p ca.2)).map Value.arr).isSome = true
    rw [alignPA_iff tail htl ts as h]
    cases (align (denoteList ts) (denoteOpt tail) as).bind (traverse fun ca => ca.1.p ca.2) <;>
      simp
  all_goals simp [AdmA, denote, tupleCodec]

def ExactAField (fd : Field) : Prop :=
  ∀ a, AdmAField fd a = true ↔ (((fieldSem fd).codec).p a).isSome

theorem reqPresentT_eq (fields : Finset Name) (fld : {k // k ∈ fields} → Field)
    (keys : Finset Name) :
    reqPresentT fields fld keys = reqPresentB ⟨fields, fun k => fieldSem (fld k)⟩ keys := by
  simp only [reqPresentT, reqPresentB]
  congr 1
  apply propext
  constructor <;> intro h k <;> have := h k <;> cases hfd : fld k <;>
    simp_all [reqPresentAt, fieldSem]

theorem keepB_eq (fields : Finset Name) (fld : {k // k ∈ fields} → Field) (rest : Rest)
    (k : Name) :
    keepB (restSem rest) ⟨fields, fun k => fieldSem (fld k)⟩ k = keepT rest fields k := by
  cases rest with
  | drop =>
    simp only [keepB, keepT, restSem, MapOf.at]
    by_cases hk : k ∈ fields <;> simp [hk]
  | refuse => rfl
  | codec t => rfl

theorem entryA_iff {fields : Finset Name} {fld : {k // k ∈ fields} → Field} {rest : Rest}
    (hf : ∀ k : {k // k ∈ fields}, ExactAField (fld k))
    (hr : ∀ t, rest = .codec t → ExactA t) (k : Name) (a : Attr) :
    (match entryPA ⟨fields, fun k => AdmAField (fld k)⟩ (AdmARest rest) k with
      | some P => P a | none => false) = true ↔
    ((entryCodec ⟨fields, fun k => fieldSem (fld k)⟩ (rcOf (restSem rest)) k).bind
      (fun c => c.p a)).isSome = true := by
  simp only [entryPA, entryCodec, MapOf.at]
  by_cases hk : k ∈ fields
  · rw [dif_pos hk, dif_pos hk]
    simpa using hf ⟨k, hk⟩ a
  · rw [dif_neg hk, dif_neg hk]
    cases rest with
    | drop => simp [AdmARest, restSem, rcOf]
    | refuse => simp [AdmARest, restSem, rcOf]
    | codec t => simpa [AdmARest, restSem, rcOf] using hr t rfl a

theorem ExactA_object {fields : Finset Name} {fld : {k // k ∈ fields} → Field} {rest : Rest}
    (hf : ∀ k : {k // k ∈ fields}, ExactAField (fld k))
    (hr : ∀ t, rest = .codec t → ExactA t) :
    ExactA (.object (.mk fields fld rest)) := by
  intro a
  cases a
  case m keys g =>
    show (reqPresentT fields fld keys &&
        objAdmA ⟨fields, fun k => AdmAField (fld k)⟩ (AdmARest rest)
          (keepT rest fields) keys g) = true ↔
      ((objectCodec ⟨fields, fun k => fieldSem (fld k)⟩ (restSem rest)).p (.m keys g)).isSome
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
        refine (entryA_iff hf hr k.1 _).mp ?_
        refine h ⟨k.1, (Finset.mem_filter.mp k.2).1⟩ ?_
        rw [← keepB_eq fields fld rest]
        exact (Finset.mem_filter.mp k.2).2
      · intro h k hk
        refine (entryA_iff hf hr k.1 (g k)).mpr ?_
        have hmem : k.1 ∈ keys.filter (keepB (restSem rest) ⟨fields, fun k => fieldSem (fld k)⟩ ·) :=
          Finset.mem_filter.mpr ⟨k.2, by rw [keepB_eq fields fld rest]; exact hk⟩
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

def ExactAR : Rest → Prop
  | .drop | .refuse => True
  | .codec t => ExactA t

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

theorem exactAR_codec : ∀ (rest : Rest), ExactAR rest → ∀ t, rest = .codec t → ExactA t
  | .drop, _, t, h => nomatch h
  | .refuse, _, t, h => nomatch h
  | .codec t0, h, t, hc => by
      have heq : t = t0 := by injection hc.symm
      subst heq; exact h

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
  | .tuple ts tail =>
      ExactA_tuple (exactAL_mem ts (AdmA_exactL ts)) (exactAO_mem tail (AdmA_exactO tail))
  | .object b => AdmA_exactB b
  | .opaq lossy => ExactA_opaq lossy
  -- both sides are empty, so the equivalence is `False ↔ False`
  | .never => fun _ => Iff.rfl
  -- exact because the constructor narrowed, not because the row sharpened
  | .set b => ExactA_set b
  -- the row that asks `ownsNull`; see `ExactA_nullable`
  | .nullable c => ExactA_nullable (AdmA_exact c)
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
  | .array c => by
      have hc := AdmA_exact c
      intro a
      cases a
      case l as =>
        simp only [AdmA, denote, denote, denote, arrayCodec]
        rw [AdmAAll_iff hc, ← traverse_isSome_iff]
        cases traverse (denote c).p as <;> simp
      all_goals simp [AdmA, denote, denote, arrayCodec]
  | .record c => by
      have hc := AdmA_exact c
      intro a
      cases a
      case m keys g =>
        simp only [AdmA, denote, denote, denote, recordCodec, Option.isSome_map, decide_eq_true_eq,
          funImage_isSome_iff]
        exact forall_congr' fun k => hc (g k)
      all_goals simp only [AdmA, denote, denote, denote, recordCodec, 
        Option.isSome_none, Bool.false_eq_true]
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
  | .mk _ fld rest =>
      ExactA_object (fun k => AdmA_exactF (fld k)) (exactAR_codec rest (AdmA_exactR rest))

theorem AdmA_exactL : ∀ (ts : List Term), ExactAL ts
  | [] => trivial
  | t0 :: ts => ⟨AdmA_exact t0, AdmA_exactL ts⟩

theorem AdmA_exactO : ∀ (tail : Option Term), ExactAO tail
  | none => trivial
  | some t0 => AdmA_exact t0

theorem AdmA_exactF : ∀ (fd : Field), ExactAField fd
  | .req t0 => fun a => AdmA_exact t0 a
  | .optional t0 => fun a => AdmA_exact t0 a
  | .fallback t0 _ => fun a => AdmA_exact t0 a

theorem AdmA_exactR : ∀ (rest : Rest), ExactAR rest
  | .drop => trivial
  | .refuse => trivial
  | .codec t0 => AdmA_exact t0
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
