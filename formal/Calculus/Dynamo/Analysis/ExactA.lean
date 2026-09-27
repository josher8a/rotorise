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
noncomputable abbrev refineReads (t : Term) (q : Value → Bool) : Attr → Bool :=
  Alg.refineReads t [] q

@[AdmA_rows] theorem refineReads_eq (t : Term) (q : Value → Bool) (a : Attr) :
    refineReads t q a = match (denote t).p a with
      | some v => q v
      | none => false := by
  -- the two matches are different auxiliary definitions, and a match reduces only at a
  -- constructor
  show Alg.refineReads t [] q a = _
  unfold Alg.refineReads
  cases (Alg.denote t).p a <;> rfl

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
    AdmALit .binary y a = true ↔ ((denote (Term.literal .binary y)).p a).isSome = true := by
  cases a <;>
    simp [AdmALit, denote_rows, literalCodec, baseCodec,
          binaryCodec]

theorem AdmALit_null_exact (y : Unit) (a : Attr) :
    AdmALit .null y a = true ↔ ((denote (Term.literal .null y)).p a).isSome = true := by
  cases a <;>
    simp [AdmALit, denote_rows, literalCodec, baseCodec,
          nullCodec]

/-- `(literal)` at `string`, read side. `String` and not `k.Carrier`: the carrier reduces once
    here instead of on every rewrite. -/
theorem AdmALit_string_exact (y : String) (a : Attr) :
    AdmALit .string y a = true ↔ ((denote (Term.literal .string y)).p a).isSome = true := by
  cases a <;>
    simp [AdmALit, denote_rows, literalCodec, baseCodec,
          stringCodec]

/-- `(literal)` at `boolean`, read side. Same shape as `AdmALit_string_exact`, and the two
    cannot share a `simp` set — one of them would have to name the other's codec. -/
theorem AdmALit_boolean_exact (y : Bool) (a : Attr) :
    AdmALit .boolean y a = true ↔ ((denote (Term.literal .boolean y)).p a).isSome = true := by
  cases a <;>
    simp [AdmALit, denote_rows, literalCodec, baseCodec,
          booleanCodec]

/-! ## DynamoDB is an instance

The structure of `AdmA` and its exactness are the term language's (`Alg.AdmA`,
`Alg.AdmA_exact`). DynamoDB supplies the primitive rows, `inBaseA` and `AdmALit`, and their
exactness. -/

/-- The DynamoDB primitive rows on the read side: `inBaseA` at a base and `AdmALit` at a
    literal. -/
noncomputable instance dynPrimAdmA : Alg.PrimAdmA dynSyn where
  admA
    | .base k => inBaseA k
    | .literal k x => AdmALit k x
  admA_exact
    | .base k, a => by
        show inBaseA k a = true ↔ ((denote (.base k)).p a).isSome = true
        cases k <;> cases a <;> simp [inBaseA, denote_rows, stringCodec, numberCodec,
          booleanCodec, binaryCodec, nullCodec]
    | .literal k ls, a => by
        show AdmALit k ls a = true ↔ ((denote (.literal k ls)).p a).isSome = true
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
          all_goals (simp only [AdmALit]; rfl)
        -- the four bases whose stored attribute *is* the value, one tight simp set each
        case string => exact AdmALit_string_exact ls a
        case boolean => exact AdmALit_boolean_exact ls a
        case binary => exact AdmALit_binary_exact ls a
        case null => exact AdmALit_null_exact ls a

/-- **The joint admission predicate, attribute side**: the generic row at DynamoDB. The mirror
    of `Adm` across §1's asymmetry, and it is not a symmetric mirror: `refine` **does** narrow
    here, because a row may decode and then ask `q` (`refineReads`). An alternate reader is
    `Codec.extendRead`, outside `Term`, so this table has no alternate-reader row. -/
abbrev AdmA (t : Term) : AP := Alg.AdmA t []

/-- The read side's payload row; `AdmBody`'s mirror. -/
abbrev AdmABody (b : Body) : AP := Alg.AdmABody b []

/-- A slot's read row is its term's. -/
abbrev AdmAField (s : ObjectSlot) : AP := Alg.AdmAField s []

/-- The open block's read row, where the body has one. -/
abbrev AdmAWild (w : Option Term) : Option AP := Alg.AdmAWild w []

/-- The options' read rows, in order. -/
abbrev AdmAList (ts : List Term) : List AP := Alg.AdmAList ts []

/-- The spread's read row, where there is one. -/
abbrev AdmAOptT (o : Option Term) : Option AP := Alg.AdmAOptT o []

/-! ### The rows at the DynamoDB constructors

Each row is the generic row at `dynSyn`, stated at the DynamoDB carriers: `Attr.l` and `Attr.m`
in place of the formers' prisms, and the primitive row in place of `PrimAdmA.admA`. -/

section Rows
variable (t : Term) (ts : List Term)

@[AdmA_rows] theorem AdmA_base (k : GroundKind) : AdmA (.base k) = inBaseA k := rfl
/-- The bottom reads no attribute back, and the row is that sentence. -/
@[AdmA_rows] theorem AdmA_never (a : Attr) : AdmA .never a = false := rfl
/-- The read side of the caller-side restriction: decode, transform, then ask `P`'s row. -/
@[AdmA_rows] theorem AdmA_held (P : Term) (f g : Value → Value) :
    AdmA (.held t P f g) = fun a => AdmA t a && refineReads t (fun w => Adm P (g w)) a := rfl
@[AdmA_rows] theorem AdmA_refine (p : Pred) :
    AdmA (.refine t p) = fun a => AdmA t a && refineReads t p.eval a := rfl
/-- The read side of the same disjunction; every option, object included, is admitted by
    attempt. -/
@[AdmA_rows] theorem AdmA_union_row : AdmA (.union ts) = fun a => anyP (AdmAList ts) a := rfl
/-- **`set` asks its own codec**, for the reason the value side gives: a read over the elements
    alone is exact only where the element reads injectively and at one member. -/
@[AdmA_rows] theorem AdmA_set : AdmA (.set t) = fun a => ((setCodec (denote t)).p a).isSome :=
  rfl
/-- **One row**, for the reason the value side gives. -/
@[AdmA_rows] theorem AdmA_list (pre suf : List Term) (sp : Option Term) :
    AdmA (.list pre sp suf) = fun a =>
      match a with
      | .l as => alignPL (AdmAList pre) (AdmAOptT sp) (AdmAList suf) as
      | _ => false := by
  funext a; cases a <;> rfl
@[AdmA_rows] theorem AdmA_object (b : Body) : AdmA (.object b) = AdmABody b := rfl
/-- The read side of the same deferral; see the `Adm` row. -/
@[AdmA_rows] theorem AdmA_opaq : AdmA .opaq = fun a => ((muCodec opaqStep).p a).isSome := rfl
/-- A closed variable is the bottom, and `mu` asks its own codec, as `opaq` does. -/
@[AdmA_rows] theorem AdmA_var (i : Nat) : AdmA (.var i) = fun _ => false := rfl
@[AdmA_rows] theorem AdmA_mu : AdmA (.mu t) = fun a => ((denote (.mu t)).p a).isSome := rfl
@[AdmA_rows] theorem AdmABody_mk (fields : Finset Name) (fld : {k // k ∈ fields} → ObjectSlot)
    (wild : Option Term) : AdmABody (.mk fields fld wild) = fun a =>
      match a with
      | .m keys g =>
          valPresentT fields fld keys &&
          objAdmV ⟨fields, fun k => AdmAField (fld k)⟩ (AdmAWild wild) keys g
      | _ => false := by
  funext a; cases a <;> rfl
@[AdmA_rows] theorem AdmAField_req : AdmAField (.req t) = AdmA t := rfl
@[AdmA_rows] theorem AdmAField_optional : AdmAField (.optional t) = AdmA t := rfl
@[AdmA_rows] theorem AdmAWild_none : AdmAWild none = none := rfl
@[AdmA_rows] theorem AdmAWild_some : AdmAWild (some t) = some (AdmA t) := rfl
@[AdmA_rows] theorem AdmAList_nil : AdmAList [] = [] := rfl
@[AdmA_rows] theorem AdmAList_cons : AdmAList (t :: ts) = AdmA t :: AdmAList ts := rfl
@[AdmA_rows] theorem AdmAOptT_none : AdmAOptT none = none := rfl
@[AdmA_rows] theorem AdmAOptT_some : AdmAOptT (some t) = some (AdmA t) := rfl

end Rows


/-- `⋁` of `AdmA` over a union's options; sound, and inexact for the reason the value side
    gives. -/
noncomputable def AdmAAny (ts : List Term) (a : Attr) : Bool := anyP (AdmAList ts) a

@[simp] theorem AdmAAny_nil (a : Attr) : AdmAAny [] a = false := rfl

@[simp] theorem AdmAAny_cons (t : Term) (ts : List Term) (a : Attr) :
    AdmAAny (t :: ts) a = (AdmA t a || AdmAAny ts a) := rfl

theorem AdmA_union (opts : List Term) (a : Attr) :
    AdmA (.union opts) a = AdmAAny opts a := rfl

/-- `AdmA`'s literal row, named — for the reason `Adm_literal` gives. -/
@[simp, AdmA_rows] theorem AdmA_literal (k : GroundKind) (x : k.Carrier) (a : Attr) :
    AdmA (.literal k x) a = AdmALit k x a := rfl

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
    simp only [denote_rows, List.filter_cons, isSome_p_eq_AdmA ht, ih hts]
    cases hb : AdmA t a <;> simp []

/-- **Every attribute row is exact**, as on the value side. The term language proves it once
    for every universe (`Alg.AdmA_exact`), and this is that theorem at DynamoDB. The numeric
    rows read the attribute payload directly, so a row reaches `dom(p)` with no appeal to the
    host's decimal reader. -/
theorem AdmA_exact (t : Term) : ExactA t := Alg.AdmA_exact t []

/-! ### The same equation on the read side

The value side needs only `AdmWild`, which is `none` exactly where the body declares no open
block. The read side reads the block the same way: an undeclared name under a closed body is
refused, and each name's own presence pair handles a declared absent name. -/

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
  rwa [entryP, MapOf.at, dif_neg hnc, hw, AdmAWild_some] at hh

/-- Soundness of every attribute row — a corollary, as on the value side. The
    hundred-and-thirty-line depth recursion this was, and the ~~SoundA~~ scaffolding it needed,
    are deleted: `AdmA_exact` carries no hypothesis, so the weaker half comes free. -/
theorem AdmA_sound (t : Term) {a v} (hp : (denote t).p a = some v) : AdmA t a = true :=
  (AdmA_exact t a).mpr (by rw [hp]; rfl)

/-- **The witness that is now a theorem the other way.** `refine(string, ⊥)` reads nothing,
    and `AdmA` says so: the row decodes with `stringCodec` and applies `⊥`. This used to be
    ~~not_ExactA_refine~~, stated as "`AdmA` cannot see it". -/
theorem AdmA_refine_bot (a : Attr) : AdmA (.refine .string (.closure (fun _ => false))) a = false := by
  simp [AdmA_rows, Pred.eval]
  cases a <;> simp [denote_rows, stringCodec]

end

end Calculus
