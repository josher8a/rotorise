import Calculus.Lang.ExactA
import Calculus.Dynamo.Analysis.ExactV

/-!
# §5 — exactness on the attribute side

`Adm` is the value half. `AdmA` is the attribute half, and it has no `Adm`-shaped
counterpart, which is the first reason the analysis tables could not simply be tightened.
-/

namespace Calculus

/-- **`refine`'s read-side gate**: decode with the base, then apply `q` to what comes out.

    The row this replaces was `admA (.refine t q) = admA t` — the predicate dropped — and
    the reason on record was that `q` tests the value a read *produces*, so no *syntactic*
    set of attributes bounds it. The premise is true and the conclusion does not follow, in
    exactly the way `number`'s and `opaq`'s `⊤`s did not follow: a row is not confined to
    syntax. It may call the denotation, and the denotation is what produces the value `q`
    tests. `(denote t).p a` is that value, or `none`; the gate is `q` of it.

    `AdmA`'s `refine` row is this function, which is why the row survived the retirement of
    the per-aspect tables it was first written for. -/
noncomputable def refineReads (t : Term) (q : Value → Bool) (a : Attr) : Bool :=
  match (denote t).p a with
  | some v => q v
  | none => false

/-- The gate, unfolded at a successful read. -/
theorem refineReads_some {t : Term} {q : Value → Bool} {a : Attr} {v : Value}
    (h : (denote t).p a = some v) : refineReads t q a = q v := by
  simp [refineReads, h]

/-- …and at a failed one. -/
theorem refineReads_none {t : Term} {q : Value → Bool} {a : Attr}
    (h : (denote t).p a = none) : refineReads t q a = false := by
  simp [refineReads, h]

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

The attribute side reads the combinators of the value side at the carrier `Attr`. `objRead`
still filters the *stored* names through `keepB`, and the row carries no filter to match it:
`keepB` is the constant `true` at every body, because `drop` was the one policy that dropped a
name and an open block is a codec or nothing. `keepB_wild` states that, and it is what the object proof
spends on the filter. -/

/-- An attribute-side row, once the subterms' rows are known. -/
abbrev AP := Attr → Bool

/- `reqPresentT` is the generic guard of `Calculus.Lang.ExactA`, and no caller reaches it by
   field notation. -/
export Alg (reqPresentT)

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

/-- Whether an attribute is of one ground base's member. -/
def inBaseA : GroundKind → Attr → Bool
  | .string, .s _ | .number, .n _ | .boolean, .bool _ | .binary, .b _ | .null, .null => true
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
  | .base k   => inBaseA k
  | .literal k ls => AdmALit k ls
  -- the bottom reads nothing back, and the row is that sentence
  | .never => fun _ => false
  -- the read side of the caller-side restriction: decode, transform, then ask `P`'s row
  | .held t P _ g => fun a => AdmA t a && refineReads t (fun w => Adm P (g w)) a
  | .refine t p => fun a => AdmA t a && refineReads t p.eval a
  -- hatch
  -- the read side of the same disjunction; every option, object included, is admitted by attempt
  | .union opts => fun a => anyP (AdmAList opts) a
  -- **`set` asks its own codec**, for the reason the value side gives: a read over the
  -- elements alone is exact only where the element reads injectively and at one member
  | .set t    => fun a => ((setCodec (denote t)).p a).isSome
  -- **One row**, for the reason the value side gives: `array` and `tuple` were two rows
  -- computing different things on what is now one shape.
  | .list pre sp suf => fun a =>
      match a with
      | .l as => alignPL (AdmAList pre) (AdmAOptT sp) (AdmAList suf) as
      | _ => false
  | .object b => AdmABody b
  -- the read side of the same deferral; see the `Adm` row
  | .opaq => fun a => ((muCodec opaqStep).p a).isSome
  -- a closed variable is the bottom, and `mu` asks its own codec, as `opaq` does
  | .var _ => fun _ => false
  | .mu b => fun a => ((denote (.mu b)).p a).isSome

/-- The read side's payload row; `AdmBody`'s mirror. -/
noncomputable def AdmABody : Body → AP
  | .mk fields fld wild => fun a =>
      match a with
      | .m keys g =>
          reqPresentT fields fld keys &&
          objAdmV ⟨fields, fun k => AdmAField (fld k)⟩ (AdmAWild wild) keys g
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



end

@[simp] theorem AdmAList_eq : ∀ ts : List Term, AdmAList ts = ts.map AdmA
  | [] => rfl
  | t :: ts => by simp only [AdmAList, List.map]; rw [AdmAList_eq ts]



/-- `⋁` of `AdmA` over a union's options; sound, and inexact for the reason the value side
    gives. -/
noncomputable def AdmAAny (ts : List Term) (a : Attr) : Bool := anyP (AdmAList ts) a

@[simp] theorem AdmAAny_nil (a : Attr) : AdmAAny [] a = false := rfl

@[simp] theorem AdmAAny_cons (t : Term) (ts : List Term) (a : Attr) :
    AdmAAny (t :: ts) a = (AdmA t a || AdmAAny ts a) := rfl

theorem AdmA_union (opts : List Term) (a : Attr) :
    AdmA (.union opts) a = AdmAAny opts a := rfl

/-- An option that admits makes the disjunction true. -/
theorem AdmAAny_of_mem {t : Term} {ts : List Term} {a : Attr} (ht : t ∈ ts)
    (h : AdmA t a = true) : AdmAAny ts a = true := by
  induction ts with
  | nil => exact absurd ht (by simp)
  | cons t0 ts ih =>
    rcases List.mem_cons.mp ht with rfl | h'
    · simp [AdmAAny_cons, h]
    · simp [AdmAAny_cons, ih h']

/-- A list reads an attribute exactly when one of its terms does. -/
theorem AdmAAny_iff : ∀ {os : List Term} {a : Attr},
    AdmAAny os a = true ↔ ∃ t ∈ os, AdmA t a = true
  | [], a => by simp
  | t :: ts, a => by
      rw [AdmAAny_cons, Bool.or_eq_true, AdmAAny_iff]
      constructor
      · rintro (h | ⟨u, hu, h⟩)
        · exact ⟨t, by simp, h⟩
        · exact ⟨u, by simp [hu], h⟩
      · rintro ⟨u, hu, h⟩
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact Or.inl h
        · exact Or.inr ⟨u, hu', h⟩

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
the literal row they were re-derived inside a twenty-case fan, and the row each one needs is a
statement about *one* base. The literal row of `dynPrimAdmA` cites all four and unfolds none. -/

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

/-- The read-side agreement, option by option — `isSome_e_eq_Adm`'s twin. -/
theorem isSome_p_eq_AdmA {t : Term} (h : ExactA t) (a : Attr) :
    ((denote t).p a).isSome = AdmA t a := by
  exact Bool.coe_iff_coe.mp (by simpa using (h a).symm)

/-- `select`'s filter is the term list's, mapped — `filter_AdmList`'s twin. -/
theorem filter_AdmAList {opts : List Term} (h : ∀ t ∈ opts, ExactA t) (a : Attr) :
    (denoteList opts).filter (fun c => (c.p a).isSome)
      = (opts.filter (fun t => AdmA t a)).map denote := by
  induction opts with
  | nil => rfl
  | cons t ts ih =>
    have ht : ExactA t := h t (by simp)
    have hts : ∀ t' ∈ ts, ExactA t' := fun t' h' => h t' (by simp [h'])
    simp only [denoteList, List.filter_cons, isSome_p_eq_AdmA ht, ih hts]
    cases hb : AdmA t a <;> simp []

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

/-- `allP` transported across the entry's exactness. -/
theorem AdmAAll_iff {c : Term} (h : ExactA c) : ∀ as : List Attr,
    allP (AdmA c) as = true ↔ ∀ a ∈ as, ((denote c).p a).isSome = true := by
  intro as; induction as with
  | nil => simp [allP]
  | cons a as ih => simp [allP, ih, h a]

/-! ## DynamoDB is an instance

The structure of `AdmA` and its exactness are the term language's (`Alg.AdmA`,
`Alg.AdmA_exact`). DynamoDB supplies the primitive rows, `inBaseA` and `AdmALit`, and their
exactness. `AdmA` keeps the DynamoDB rows by name, for the reason `Adm` does, and `AdmA_eq_alg`
pins each row to the generic one. -/

/-- The DynamoDB primitive rows on the read side: `inBaseA` at a base and `AdmALit` at a
    literal. -/
noncomputable instance dynPrimAdmA : Alg.PrimAdmA dynSyn where
  admA
    | .base k => inBaseA k
    | .literal k x => AdmALit k x
  admA_exact
    | .base k, a => by
        show AdmA (.base k) a = true ↔ ((denote (.base k)).p a).isSome = true
        cases k <;> cases a <;> simp [AdmA, inBaseA, denote, stringCodec, numberCodec,
          booleanCodec, binaryCodec, nullCodec]
    | .literal k ls, a => by
        show AdmA (.literal k ls) a = true ↔ ((denote (.literal k ls)).p a).isSome = true
        cases k
        case number =>
          cases a
          case n x =>
            -- `numberCodec.p` is a constructor wrapper, so the row is the payload comparison
            -- on both sides
            rw [show (denote (Term.literal .number ls)).p (.n x)
                   = (literalCodec .number ls).p (.n x) from rfl,
               literalNCodec_p_n, numberCodec_p_n]
            simp [AdmALit, inL]
          -- for every other attribute the base's own read is `none` by a match
          all_goals (simp only [AdmA_literal, AdmALit]; rfl)
        -- the four bases whose stored attribute *is* the value, one tight simp set each
        case string => exact AdmALit_string_exact ls a
        case boolean => exact AdmALit_boolean_exact ls a
        case binary => exact AdmALit_binary_exact ls a
        case null => exact AdmALit_null_exact ls a

/-- The read-side gate at DynamoDB is the generic gate. -/
theorem refineReads_eq_alg (t : Term) (q : Value → Bool) :
    refineReads t q = Alg.refineReads t q := by
  funext a
  unfold refineReads Alg.refineReads
  rw [denote_eq_alg]
  -- the two matches are different auxiliary definitions, and a match reduces only at a
  -- constructor
  cases (Alg.denote t).p a <;> rfl

mutual

/-- The DynamoDB rows are the generic rows at `dynSyn`. -/
theorem AdmA_eq_alg : ∀ t : Term, AdmA t = Alg.AdmA t
  | .base _ | .literal _ _ | .never | .opaq | .var _ => rfl
  | .refine t p => by
      show (fun a => AdmA t a && refineReads t p.eval a)
        = fun a => Alg.AdmA t a && Alg.refineReads t p.eval a
      rw [AdmA_eq_alg t, refineReads_eq_alg]
      rfl
  | .held t P _ g => by
      show (fun a => AdmA t a && refineReads t (fun w => Adm P (g w)) a)
        = fun a => Alg.AdmA t a && Alg.refineReads t (fun w => Alg.Adm P (g w)) a
      rw [AdmA_eq_alg t, refineReads_eq_alg, Adm_eq_alg P]
      rfl
  | .union opts => by
      show (fun a => anyP (AdmAList opts) a) = fun a => anyP (Alg.AdmAList opts) a
      rw [AdmAList_eq_alg opts]
      rfl
  | .set t => by
      show (fun a => ((setCodec (denote t)).p a).isSome)
        = fun a => ((setCodec (Alg.denote t)).p a).isSome
      rw [denote_eq_alg]
  | .mu b => by
      show (fun a => ((denote (.mu b)).p a).isSome) = fun a => ((Alg.denote (.mu b)).p a).isSome
      rw [denote_eq_alg]
      rfl
  | .list pre sp suf => by
      funext a
      cases a
      case l as =>
        show alignPL (AdmAList pre) (AdmAOptT sp) (AdmAList suf) as
          = alignPL (Alg.AdmAList pre) (Alg.AdmAOptT sp) (Alg.AdmAList suf) as
        rw [AdmAList_eq_alg pre, AdmAOptT_eq_alg sp, AdmAList_eq_alg suf]
      all_goals rfl
  | .object b => AdmABody_eq_alg b

/-- …at a payload. -/
theorem AdmABody_eq_alg : ∀ b : Body, AdmABody b = Alg.AdmABody b
  | .mk fields fld wild => by
      have hf : (fun k => AdmAField (fld k)) = fun k => Alg.AdmAField (fld k) :=
        funext fun k => AdmAField_eq_alg (fld k)
      funext a
      cases a
      case m keys g =>
        show (reqPresentT fields fld keys &&
            objAdmV ⟨fields, fun k => AdmAField (fld k)⟩ (AdmAWild wild) keys g)
          = (reqPresentT fields fld keys &&
            objAdmV ⟨fields, fun k => Alg.AdmAField (fld k)⟩ (Alg.AdmAWild wild) keys g)
        rw [hf, AdmAWild_eq_alg wild]
      all_goals rfl

/-- …at a slot. -/
theorem AdmAField_eq_alg : ∀ s : ObjectSlot, AdmAField s = Alg.AdmAField s
  | .req t | .optional t => AdmA_eq_alg t

/-- …at the open block. -/
theorem AdmAWild_eq_alg : ∀ w : Option Term, AdmAWild w = Alg.AdmAWild w
  | none => rfl
  | some t => congrArg some (AdmA_eq_alg t)

/-- …at a list of terms. -/
theorem AdmAList_eq_alg : ∀ ts : List Term, AdmAList ts = Alg.AdmAList ts
  | [] => rfl
  | t :: ts => by
      show AdmA t :: AdmAList ts = Alg.AdmA t :: Alg.AdmAList ts
      rw [AdmA_eq_alg t, AdmAList_eq_alg ts]

/-- …at an optional term. -/
theorem AdmAOptT_eq_alg : ∀ o : Option Term, AdmAOptT o = Alg.AdmAOptT o
  | none => rfl
  | some t => congrArg some (AdmA_eq_alg t)

end

/-- **Every attribute row is exact**, as on the value side. The term language proves it once
    for every universe (`Alg.AdmA_exact`), and this is that theorem at DynamoDB. The numeric
    rows read the attribute payload directly, so a row reaches `dom(p)` with no appeal to the
    host's decimal reader. -/
theorem AdmA_exact (t : Term) : ExactA t := fun a => by
  rw [AdmA_eq_alg, denote_eq_alg]
  exact Alg.AdmA_exact t a

/-! ### The same equation on the read side

The value side needs only `AdmWild`, which is `none` exactly where the body declares no open
block. The read side reads the block the same way: an undeclared name under a closed body is
refused, and each name's own presence pair handles a declared absent name. -/

/-- `AdmABody` at a map, unfolded. -/
theorem AdmABody_map {b : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Attr} :
    AdmABody b (.m keys g)
      = (reqPresentT b.fields b.at keys &&
         objAdmV ⟨b.fields, fun k => AdmAField (b.at k)⟩ (AdmAWild b.wild) keys g) := by
  cases b; rfl

/-- One entry of the read-side object row — `objAdmV_row`'s twin. It took a keep filter as a
    hypothesis while `drop` made the two sides' filters differ; they do not differ now. -/
theorem objAdmA_row {c : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hB : objAdmV ⟨c.fields, fun k => AdmAField (c.at k)⟩ (AdmAWild c.wild) keys g = true)
    {k : Name} (hk : k ∈ keys) (hc : k ∈ c.fields) :
    AdmAField (c.at ⟨k, hc⟩) (g ⟨k, hk⟩) = true := by
  unfold objAdmV at hB
  have hh := of_decide_eq_true hB ⟨k, hk⟩
  rwa [entryP, MapOf.at, dif_pos hc] at hh

/-- A present name the body does not declare goes through the open block, on the read side.
    `objAdmV_wild`'s twin. -/
theorem objAdmA_wild {c : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hB : objAdmV ⟨c.fields, fun k => AdmAField (c.at k)⟩ (AdmAWild c.wild) keys g = true)
    {k : Name} (hk : k ∈ keys) (hnc : k ∉ c.fields) {w : Term}
    (hw : c.wild = some w) : AdmA w (g ⟨k, hk⟩) = true := by
  unfold objAdmV at hB
  have hh := of_decide_eq_true hB ⟨k, hk⟩
  rwa [entryP, MapOf.at, dif_neg hnc, hw, AdmAWild] at hh

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
