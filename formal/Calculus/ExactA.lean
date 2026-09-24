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
file's: the numeric rows went through the host's decimal reader, and `refine` narrows a read.
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

/-- …and on the attribute side, admitted by attempt like `admitOptV`. `o.1` (`specOf`)
    goes unread here. -/
def admitOptA (o : Option (BodySpec) × AP) (a : Attr) : Bool := o.2 a

/-- …and the same disjunction. -/
def selOptA (os : List (Option (BodySpec) × AP)) (a : Attr) : Bool :=
  os.any (fun o => admitOptA o a)

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

/-- The current-schema reader has the same required-name guard as the writer. -/
def reqPresentT (fields : Finset Name) (fld : {k // k ∈ fields} → ObjectSlot)
    (keys : Finset Name) : Bool :=
  decide (∀ k : {k // k ∈ fields},
    (match fld k with | .req _ => decide (k.1 ∈ keys) | _ => true) = true)


/-- What the literal codec **reads**, exactly.

    Each row is membership. `N` is carried exactly, so the `number` row compares the payload
    with the literal, as the `string` row does. -/
noncomputable def AdmALit : (k : GroundKind) → k.Carrier → Attr → Bool
  | .string,  y, .s s    => decide (s = y)
  | .boolean, y, .bool b => decide (b = y)
  | .binary,  y, .b b    => decide (b = y)
  | .null,    _, .null   => true
  -- `N` is carried exactly on both sides, so the attribute payload IS the alternative and
  -- this row reads like `string`'s beside it.
  | .number,  y, .n x    => decide (x = y)
  | _, _, _ => false

/-- **What a set base reads.**

    Two bases answer concretely: `string` reads `SS` and nothing else, and `binary` `BS`.
    `number` asks its codec: `decSet` reads each payload of an `NS` through `numberCodec.p`.
    `N` is carried exactly, so `numberCodec.p` is a constructor wrapper on the numeral
    (`numberCodec_p_n`), and no two distinct payloads read to one value. `AdmA` is already
    `noncomputable`, so the row costs nothing it had not already spent. -/
noncomputable def AdmASet : SetBase → Attr → Bool
  | .string,  .ss _ => true
  | .binary,  .bs _ => true
  | .number,  .ns S => (decSet numberCodec Attr.n S).isSome
  | _, _ => false

mutual

/-- **The joint admission predicate, attribute side.** The mirror of `Adm` across §1's
    asymmetry, and it is not a symmetric mirror: one row differs in kind, not degree.

    * `refine` **does** narrow here, and the row that said it could not was wrong. "`q` tests the value a read *produces*, and no
      syntactic set of attributes bounds that" is true of syntax and says nothing about a
      row, which may decode and then ask `q` (`refineReads`). Sound, and exact whenever the
      subterm's row is: `dom((c.restrict q).p)` is precisely `{a | ∃ v, c.p a = some v ∧ q v}`.
    An alternate reader is `Codec.extendRead`, outside `Term`, so this table has no
    alternate-reader row. -/
noncomputable def AdmA : Term → Attr → Bool
  | .string   => fun a => match a with | .s _ => true | _ => false
  | .boolean  => fun a => match a with | .bool _ => true | _ => false
  | .binary   => fun a => match a with | .b _ => true | _ => false
  | .null     => fun a => match a with | .null => true | _ => false
  | .number   => fun a => match a with | .n _ => true | _ => false
  | .literal k ls => AdmALit k ls
  -- the bottom reads nothing back, and the row is that sentence
  | .never => fun _ => false
  -- the read side of the caller-side restriction: decode, transform, then ask `P`'s row
  | .held t P _ g => fun a => AdmA t a && refineReads t (fun w => Adm P (g w)) a
  | .lazy t   => AdmA t
  | .refine t p => fun a => AdmA t a && refineReads t p.eval a
  -- hatch
  -- the read side of the same disjunction; every option, object included, is admitted by attempt
  | .union opts => fun a => selOptA (AdmASpecs opts) a
  -- **the row that used to admit all three wire families whatever the element term was.**
  -- With the base an index the family is a function of it, so this names one — and at
  -- `number` defers to the codec, as `AdmASet` states.
  | .set b    => AdmASet b
  -- **One row**, for the reason the value side gives: `array` and `tuple` were two rows
  -- computing different things on what is now one shape.
  | .list pre sp suf => fun a =>
      match a with
      | .l as => alignPAL (AdmAList pre) (AdmAOptT sp) (AdmAList suf) as
      | _ => false
  | .object b => AdmABody b
  -- the read side of the same deferral; see the `Adm` row and `ExactA_opaq`
  | .opaq => fun a => ((opaqCodecω).p a).isSome

/-- The read side's payload row; `AdmBody`'s mirror. -/
noncomputable def AdmABody : Body → AP
  | .mk fields fld wild => fun a =>
      match a with
      | .m keys g =>
          reqPresentT fields fld keys &&
          objAdmA ⟨fields, fun k => AdmAField (fld k)⟩ (AdmAWild wild) keys g
      | _ => false

noncomputable def AdmAField : ObjectSlot → AP
  | .req t => AdmA t
  | .optional t => AdmA t

noncomputable def AdmAWild : Option Term → Option AP
  | none => none
  | some t => some (AdmA t)

noncomputable def AdmAList : List Term → List AP
  | [] => []
  | t :: ts => AdmA t :: AdmAList ts

noncomputable def AdmAOptT : Option Term → Option AP
  | none => none
  | some t => some (AdmA t)


/-- `denoteList`' mirror on the attribute side. -/
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

/-- The row is the disjunction — see `selOptV_eq_AdmAny`. -/
theorem selOptA_eq_AdmAAny (opts : List Term) (a : Attr) :
    selOptA (AdmASpecs opts) a = AdmAAny opts a := by
  rw [AdmASpecs_eq]
  induction opts with
  | nil => rfl
  | cons t ts ih => simp only [selOptA, List.map_cons, List.any_cons] at ih ⊢; rw [ih]; rfl

/-- …read as the implication the containments need. -/
theorem selOptA_le_AdmAAny {opts : List Term} {a : Attr}
    (h : selOptA (AdmASpecs opts) a = true) : AdmAAny opts a = true :=
  selOptA_eq_AdmAAny opts a ▸ h

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
    ((denote t).p a).isSome = admitOptA (specOf t, AdmA t) a := by
  unfold admitOptA
  exact Bool.coe_iff_coe.mp (by simpa using (h a).symm)

/-- `select`'s filter is the term list's, mapped — `filter_AdmSpecs`'s twin. -/
theorem filter_AdmASpecs {opts : List Term} (h : ∀ t ∈ opts, ExactA t) (a : Attr) :
    (denoteList opts).filter (fun c => (c.p a).isSome)
      = (opts.filter (fun t => admitOptA (specOf t, AdmA t) a)).map denote := by
  induction opts with
  | nil => rfl
  | cons t ts ih =>
    have ht : ExactA t := h t (by simp)
    have hts : ∀ t' ∈ ts, ExactA t' := fun t' h' => h t' (by simp [h'])
    simp only [denoteList, List.filter_cons, admitOptA_eq ht, ih hts]
    cases hb : admitOptA (specOf t, AdmA t) a <;> simp []

/-- **A union reads exactly where one of its options reads.** -/
theorem select_isSome_attemptA (os : List Codec) (a : Attr) :
    (select os (·.p) a).isSome = true ↔ ∃ o ∈ os, (o.p a).isSome = true := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨o, ho, -, hp⟩ := select_admits hv
    exact ⟨o, ho, by rw [hp]; rfl⟩
  · rintro ⟨o, ho, hp⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨o', hf⟩ := find?_attempt_A ho hv
    unfold select; rw [hf]; exact acts_of_find?_A hf

/-- **`union` reads exactly what its row says** — `ExactV_union` on the other side of the
    pair. -/
theorem ExactA_union {opts : List Term} (h : ∀ t ∈ opts, ExactA t) : ExactA (.union opts) := by
  intro a
  rw [denote_union_sems]
  show selOptA (AdmASpecs opts) a = true ↔ (select (denoteList opts) (·.p) a).isSome
  rw [selOptA_eq_AdmAAny, select_isSome_attemptA, denoteList_eq]
  simp only [List.mem_map, exists_exists_and_eq_and]
  constructor
  · intro ha
    induction opts with
    | nil => exact absurd ha (by simp)
    | cons t ts ih =>
      rw [AdmAAny_cons, Bool.or_eq_true] at ha
      rcases ha with ha | ha
      · exact ⟨t, List.mem_cons_self, (h t List.mem_cons_self a).mp ha⟩
      · obtain ⟨t', ht', hp⟩ := ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) ha
        exact ⟨t', List.mem_cons_of_mem _ ht', hp⟩
  · rintro ⟨t, ht, hp⟩
    exact AdmAAny_of_mem ht ((h t ht a).mpr hp)

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
  constructor <;> intro h k <;> have := h k <;>
    (cases hfd : fld k with
      | req t => simp_all [reqPresentAt, fieldSem]
      | optional t => simp_all [reqPresentAt, fieldSem])

/-- **The read side keeps every stored name.** `drop` was the one policy that dropped one,
    and it is gone, so `objRead`'s filter is the identity on the key set and the row owes it
    nothing. -/
theorem keepB_wild (wild : Option Term) (sems : MapOf FieldSem) (k : Name) :
    keepB (wildSem wild) sems k = true := by
  cases wild with
  | none => rfl
  | some pt => rfl

theorem entryA_iff {fields : Finset Name} {fld : {k // k ∈ fields} → ObjectSlot}
    {wild : Option Term}
    (hf : ∀ k : {k // k ∈ fields}, ExactAField (fld k))
    (hr : ∀ t, wild = some t → ExactA t) (k : Name) (a : Attr) :
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
    | some pt => simpa [AdmAWild, wildSem, rcOf] using hr pt rfl a

theorem ExactA_object {fields : Finset Name} {fld : {k // k ∈ fields} → ObjectSlot}
    {wild : Option Term}
    (hf : ∀ k : {k // k ∈ fields}, ExactAField (fld k))
    (hr : ∀ t, wild = some t → ExactA t) :
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
    `ExactV_opaq` gives at length: `p := (opaqCodecω).p`, so the row and `dom(p)` are
    one function. ~~AdmOpaqA_iff~~ — a second induction, this one carrying an injectivity
    clause about the host's decimal reader that `decSet` needs — is deleted rather than moved. The
    clause was true and is still true; it is now the codec's business, where it was always
    stated (`decSet`, `Products.lean`), instead of being restated here in a form that had
    to be kept in step by hand. -/
theorem ExactA_opaq : ExactA .opaq := fun _ => Iff.rfl


def ExactAL : List Term → Prop
  | [] => True
  | t :: ts => ExactA t ∧ ExactAL ts

def ExactAO : Option Term → Prop
  | none => True
  | some t => ExactA t

def ExactAW : Option Term → Prop
  | none => True
  | some t => ExactA t

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

theorem exactAW_codec : ∀ (wild : Option Term), ExactAW wild →
    ∀ t, wild = some t → ExactA t
  | none, _, t, h => nomatch h
  | some t0, h, t, hc => by
      simp only [Option.some.injEq] at hc
      exact hc ▸ h

/-- `allPA` transported across the entry's exactness. -/
theorem AdmAAll_iff {c : Term} (h : ExactA c) : ∀ as : List Attr,
    allPA (AdmA c) as = true ↔ ∀ a ∈ as, ((denote c).p a).isSome = true := by
  intro as; induction as with
  | nil => simp [allPA]
  | cons a as ih => simp [allPA, ih, h a]

mutual
/-- **Every attribute row is exact** — all twenty-one, as on the value side, and nothing
    declines on either. `refine` was the last difference between
    the two sides and is exact now: its row decodes and then applies `q`.
    which used to be the other half of that asymmetry, is exact here because its row is the
    union of the two channels it reads on.

    The numeric rows are the interesting ones: they reach `dom(p)` through the host's decimal reader,
    which is axiomatized, and are exact anyway — a row may *call* an axiomatized function
    even though no finite set of numerals describes its domain. §5 wrote `⊤` there. -/
theorem AdmA_exact : ∀ (t : Term), ExactA t
  -- the rows §5 excused on this side too
  | .list pre sp suf =>
      ExactA_list (exactAL_mem pre (AdmA_exactL pre)) (exactAO_mem sp (AdmA_exactO sp))
        (exactAL_mem suf (AdmA_exactL suf))
  | .object b => AdmA_exactB b
  | .opaq => ExactA_opaq
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
  | .number => by intro a; cases a <;> simp [AdmA, denote, denote, numberCodec]
  -- Three rows into one, and `number`'s no longer needs the host lookup that used to make it
  -- the awkward one: both numeric bases now read the attribute payload directly.
  | .literal k ls => by
      intro a
      cases k
      case number =>
        cases a
        case n x =>
          -- `numberCodec.p` is a constructor wrapper now, so the host's decimal reader bind and the
          -- `Numeral.WF` gate this used to walk through are both gone and the row is the
          -- payload comparison on both sides
          rw [show (denote (Term.literal .number ls)).p (.n x)
                 = (literalCodec .number ls).p (.n x) from rfl,
             literalNCodec_p_n, numberCodec_p_n]
          simp [AdmALit, inL]
        -- for every other attribute the base's own read is `none` by a match, so this is
        -- `rfl` once `AdmA`'s recursion is unfolded
        all_goals (simp only [AdmA_literal, AdmALit]; rfl)
      -- the four bases whose stored attribute *is* the value, one tight simp set each: a
      -- shared set has to mention every base's codec, and one of those is `number`
      case string => exact AdmALit_string_exact ls a
      case boolean => exact AdmALit_boolean_exact ls a
      case binary => exact AdmALit_binary_exact ls a
      case null => exact AdmALit_null_exact ls a
  | .held c P f g => by
      have hc := AdmA_exact c
      have hP := Adm_exact P
      intro a
      simp only [AdmA, refineReads, denote_held, Codec.restrict, Codec.through,
        Bool.and_eq_true, hc a]
      cases (denote c).p a with
      | none => simp
      | some w => simpa using Bool.eq_iff_iff.mpr (hP (g w))
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

/-- Each current-schema slot reads exactly through its carried term. -/
theorem AdmA_exactF : ∀ (fd : ObjectSlot), ExactAField fd
  | .req t0 => fun a => AdmA_exact t0 a
  | .optional t0 => fun a => AdmA_exact t0 a

theorem AdmA_exactW : ∀ (wild : Option Term), ExactAW wild
  | none => trivial
  | some t0 => AdmA_exact t0
end

/-! ### The same equation on the read side

The value side needs only `AdmWild`, which is `none` exactly where the body declares no open
block. The read side reads the block the same way. `mem_fields_of_admA` handles an undeclared
name under a closed body, and each name's own presence pair handles a declared absent name. -/

/-- `AdmABody` at a map, unfolded. -/
theorem AdmABody_map {b : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Attr} :
    AdmABody b (.m keys g)
      = (reqPresentT b.fields b.at keys &&
         objAdmA ⟨b.fields, fun k => AdmAField (b.at k)⟩ (AdmAWild b.wild) keys g) := by
  cases b; rfl

/-- A field's row carries its literal alternatives on the read side, where it has any —
    `altsOkV_of_AdmField`'s twin, through `ExactA` because `altsOkA` asks the codec. -/
theorem altsOkA_of_AdmAField {f : ObjectSlot} {a : Attr} (h : AdmAField f a = true) :
    altsOkA (altsOfField f) a = true := by
  cases f with
  | req t => cases t <;> first | rfl | exact (AdmA_exact _ a).mp h
  | optional t => cases t <;> first | rfl | exact (AdmA_exact _ a).mp h

/-- Every present name is declared, where the body declares no open block and so refuses an
    undeclared one. The read side used to need this against `drop` as well, which skips such a
    name rather than refusing it, and a name that is skipped is read. `drop` is gone, so the one
    closed state answers both halves the same way. -/
theorem mem_fields_of_admA {b : Body} (hr : b.wild = none)
    {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (h : AdmABody b (.m keys g) = true) : ∀ k ∈ keys, k ∈ b.fields := by
  rw [AdmABody_map, Bool.and_eq_true] at h
  have h2 := h.2
  unfold objAdmA at h2
  intro k hk
  refine Decidable.byContradiction (fun hnb => ?_)
  have hh := of_decide_eq_true h2 ⟨k, hk⟩
  rw [entryPA, MapOf.at, dif_neg hnb, hr] at hh
  exact absurd hh (by simp [AdmAWild])

/-- One entry of the read-side object row — `objAdmV_row`'s twin. It took a keep filter as a
    hypothesis while `drop` made the two sides' filters differ; they do not differ now. -/
theorem objAdmA_row {c : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hB : objAdmA ⟨c.fields, fun k => AdmAField (c.at k)⟩ (AdmAWild c.wild) keys g = true)
    {k : Name} (hk : k ∈ keys) (hc : k ∈ c.fields) :
    AdmAField (c.at ⟨k, hc⟩) (g ⟨k, hk⟩) = true := by
  unfold objAdmA at hB
  have hh := of_decide_eq_true hB ⟨k, hk⟩
  rwa [entryPA, MapOf.at, dif_pos hc] at hh

/-- A present name the body does not declare goes through the open block, on the read side.
    `objAdmV_wild`'s twin. -/
theorem objAdmA_wild {c : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hB : objAdmA ⟨c.fields, fun k => AdmAField (c.at k)⟩ (AdmAWild c.wild) keys g = true)
    {k : Name} (hk : k ∈ keys) (hnc : k ∉ c.fields) {w : Term}
    (hw : c.wild = some w) : AdmA w (g ⟨k, hk⟩) = true := by
  unfold objAdmA at hB
  have hh := of_decide_eq_true hB ⟨k, hk⟩
  rwa [entryPA, MapOf.at, dif_neg hnc, hw, AdmAWild] at hh

/-- A term's row carries its literal alternatives on the read side, where it has any.
    `altsOkA_of_AdmAField`'s twin at the term level, which is what an open block needs. -/
theorem altsOkA_of_AdmA {t : Term} {a : Attr} (h : AdmA t a = true) :
    altsOkA (altsOfTerm t) a = true := by
  cases t <;> first | rfl | exact (AdmA_exact _ a).mp h

/-- **An object option has its structural test for a read row, open block and all.**
    `structural_of_AdmBody`'s twin, and it carries no closedness premise for the same reason. -/
theorem structural_of_AdmABody {b : Body}
    {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (h : AdmABody b (.m keys g) = true) :
    (keysOk b.spec keys && literalsOkA b.spec keys g) = true := by
  have h' := h
  rw [AdmABody_map, Bool.and_eq_true] at h'
  cases hb : b with
  | mk fields fld wild =>
    subst hb
    refine Bool.and_eq_true _ _ |>.mpr ⟨?_, ?_⟩
    · refine keysOk_of_names ?_ (fun k hreq => ?_) (fun k hforbid hk => ?_)
      · cases hw : wild with
        | none => exact Or.inr (mem_fields_of_admA (b := .mk fields fld wild) hw h)
        | some _ => exact Or.inl rfl
      · cases hf : fld k with
        | req t =>
          have hh := of_decide_eq_true h'.1 k
          exact of_decide_eq_true (by simpa [Body.at, hf] using hh)
        | optional t =>
          rw [hf] at hreq
          cases t <;> simp [ObjectSlot.presence, Term.isNever] at hreq
      · have hrow := objAdmA_row h'.2 hk k.2
        change AdmAField (fld k) (g ⟨k.1, hk⟩) = true at hrow
        cases hf : fld k with
        | req t =>
          rw [hf] at hforbid
          have ht : t = .never := by
            cases t <;> simp [ObjectSlot.presence, ObjectSlot.isReq, Term.isNever] at hforbid ⊢
          subst t
          rw [hf] at hrow
          simp [AdmAField, AdmA] at hrow
        | optional t =>
          rw [hf] at hforbid
          have ht : t = .never := by
            cases t <;> simp [ObjectSlot.presence, Term.isNever] at hforbid ⊢
          subst t
          rw [hf] at hrow
          simp [AdmAField, AdmA] at hrow
    · refine decide_eq_true (fun k => ?_)
      show litOkA _ k.1 (g k) = true
      cases hkf : decide (k.1 ∈ fields) with
      | true =>
        have hd := of_decide_eq_true hkf
        rw [litOkA, show (Body.spec (.mk fields fld wild)).names.at k.1
              = some ⟨_, altsOfField (fld ⟨k.1, hd⟩)⟩ from dif_pos hd]
        exact altsOkA_of_AdmAField (objAdmA_row h'.2 k.2 hd)
      | false =>
        have hnd := of_decide_eq_false hkf
        cases hw : wild with
        | none => exact absurd (mem_fields_of_admA (b := .mk fields fld wild) hw h k.1 k.2) hnd
        | some w =>
          have hat : (Body.spec (.mk fields fld (some w))).names.at k.1 = none := dif_neg hnd
          have hws : (Body.spec (.mk fields fld (some w))).wild = some (altsOfTerm w) := by
            simp [Body.spec]
          simp only [litOkA, hat, hws]
          exact altsOkA_of_AdmA (objAdmA_wild h'.2 k.2 hnd hw)

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
