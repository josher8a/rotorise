import Calculus.Lang.ExactA
import Calculus.Dynamo.Analysis.ExactV

variable {α : Calculus.Table}

/-!
# Exactness on the attribute side

`Adm` is the value half. `AdmA` is the attribute half, and it has no `Adm`-shaped
counterpart.
-/

namespace Calculus

variable (α) in
/-- **`refine`'s read-side gate**: decode with the base, then apply `q` to what comes out.

    `q` tests the value a read *produces*, so no *syntactic* set of attributes bounds it. A
    row is not confined to syntax: it may call the denotation, and the denotation is what
    produces the value `q` tests. `(denote t).p a` is that value, or `none`; the gate is `q`
    of it.

    `AdmA`'s `refine` row is this function. -/
abbrev refineReads (t : Term) (q : Value → Bool) : Attr → Bool :=
  Alg.refineReads α dynTableA t [] q

@[AdmA_rows] theorem refineReads_eq (t : Term) (q : Value → Bool) (a : Attr) :
    refineReads α t q a = match (denote α t).p a with
      | some v => q v
      | none => false := by
  -- the two matches are different auxiliary definitions, and a match reduces only at a
  -- constructor
  show Alg.gate (Alg.denote α dynTableA t []).p q a = _
  unfold Alg.gate
  cases (Alg.denote α dynTableA t).p a <;> rfl

section
/-! ## The attribute side

`Adm` is the value half. `AdmA` is the attribute half, and it has no
`Adm`-shaped counterpart. `AdmA` below is that counterpart's definition and its soundness proof.

The numeric rows read the attribute payload directly, and the `refine` row decodes and then
applies `q` (`refineReads`). Each is a row here rather than a remark. -/

/-! ### The attribute side's rows

The attribute side reads the combinators of the value side at the carrier `Attr`. `objAt` at the
dual reads every stored name, because a rest policy refuses an undeclared name or reads it with the
codec of the open block. The attribute row is the value row of the dual. -/

/-- An attribute-side row, once the subterms' rows are known. -/
abbrev AP := Attr → Bool

/-! ## DynamoDB is an instance

The structure of `AdmA` and its exactness are the term language's (`Alg.AdmA`,
`Alg.AdmA_exact`). With one carrier, each DynamoDB primitive is one map at both orientations
(`ground_selfdual`). So the read-side rows of the primitives are the write-side rows, `inBase`
and `inL`, and their exactness is the write-side exactness. -/

/-- The DynamoDB primitive rows on the read side: the write-side rows, because each primitive is
    self-dual. -/
instance dynPrimAdmA : Alg.PrimAdmA dynSyn :=
  Alg.PrimAdm.dual fun g => (ground_selfdual g).symm

variable (α) in
/-- **The joint admission predicate, attribute side**: the generic row at DynamoDB. The mirror
    of `Adm` across the asymmetry of value and attribute, and it is not a symmetric mirror: `refine` **does** narrow
    here, because a row may decode and then ask `q` (`refineReads`). An alternate reader
    (`Term.legacy`) asks its own codec, so this table has no structural alternate-reader row. -/
abbrev AdmA (t : Term) : AP := Alg.AdmA α dynTableA t []

variable (α) in
/-- The read side's payload row; `AdmBody`'s mirror. -/
abbrev AdmABody (b : Body) : AP := Alg.AdmABody α dynTableA b []

variable (α) in
/-- A slot's read row is its term's. -/
abbrev AdmAField (s : ObjectSlot) : AP := Alg.AdmAField α dynTableA s []

variable (α) in
/-- The open block's read row, where the body has one. -/
abbrev AdmAWild (w : Option Term) : Option AP := Alg.AdmAWild α dynTableA w []

variable (α) in
/-- The options' read rows, in order. -/
abbrev AdmAList (ts : List Term) : List AP := Alg.AdmAList α dynTableA ts []

variable (α) in
/-- The spread's read row, where there is one. -/
abbrev AdmAOptT (o : Option Term) : Option AP := Alg.AdmAOptT α dynTableA o []

/-! ### The rows at the DynamoDB constructors

Each row is the generic row at `dynSyn`, stated at the DynamoDB carriers: `Attr.l` and `Attr.m`
in place of the formers' prisms, and the primitive row in place of `PrimAdm.admV`. -/

section Rows
variable (t : Term) (ts : List Term)

@[AdmA_rows] theorem AdmA_base (k : GroundKind) : AdmA α (.base k) = inBase k := rfl
/-- The bottom reads no attribute back, and the row is that sentence. -/
@[AdmA_rows] theorem AdmA_never (a : Attr) : AdmA α .never a = false := rfl
/-- The read side of the caller-side restriction: decode, transform, then ask `P`'s row. -/
@[AdmA_rows] theorem AdmA_held (P : Term) (k₀ : DynGen × Bool) (k : Word) :
    AdmA α (.held false t P k₀ k) =
      fun a => AdmA α t a && refineReads α t (fun w => Adm α P ((α.word (k₀ :: k)).2 w)) a := by
  funext a
  rw [AdmA, Alg.AdmA_held_eq (S := dynSyn)]
  rfl
/-- The stored predicate is the truth, so the read row of `refine` asks the caller predicate of
    the read alone. -/
@[AdmA_rows] theorem AdmA_refine (p : Pred) (pA : Alg.Syn.PredA dynSyn) :
    AdmA α (.refine t p pA) = fun a => AdmA α t a && refineReads α t p.eval a := by
  funext a
  rw [AdmA, Alg.AdmA_refine_eq (S := dynSyn)]
  rfl
/-- The read side of the same disjunction; every option, object included, is admitted by
    attempt. -/
@[AdmA_rows] theorem AdmA_union_row : AdmA α (.union ts) = fun a => anyP (AdmAList α ts) a := rfl
/-- **`set` asks its own codec**, for the reason the value side gives: a read over the elements
    alone is exact only where the element reads injectively and at one member. -/
@[AdmA_rows] theorem AdmA_set : AdmA α (.set t) = fun a => ((setCodec (denote α t)).p a).isSome :=
  funext (Alg.AdmA_eq_isSome (.set t) [])
/-- **One row**, for the reason the value side gives. -/
@[AdmA_rows] theorem AdmA_list (pre suf : List Term) (sp : Option Term) :
    AdmA α (.list pre sp suf) = fun a =>
      match a with
      | .l as => alignPL (AdmAList α pre) (AdmAOptT α sp) (AdmAList α suf) as
      | _ => false := by
  funext a; cases a <;> rfl
@[AdmA_rows] theorem AdmA_object (b : Body) : AdmA α (.object b) = AdmABody α b := rfl
/-- The read side: `opaque` reads every attribute. -/
@[AdmA_rows] theorem AdmA_opaq : AdmA α .opaq = fun _ => true := rfl
/-- A closed variable is the bottom, and `mu` asks its own codec, as `opaq` does. -/
@[AdmA_rows] theorem AdmA_var (i : Nat) : AdmA α (.var i) = fun _ => false := rfl
@[AdmA_rows] theorem AdmA_mu : AdmA α (.mu t) = fun a => ((denote α (.mu t)).p a).isSome :=
  funext (Alg.AdmA_eq_isSome (.mu t) [])
/-- The payload row reads a map attribute by its names, and reads no other attribute. -/
@[AdmA_rows] theorem AdmABody_mk (fields : Finset Name) (fld : {k // k ∈ fields} → ObjectSlot)
    (wild : Option Term) : AdmABody α (.mk fields fld wild) = fun a =>
      match a with
      | .m keys g =>
          valPresentT .dual fields fld keys &&
          objAdmV ⟨fields, fun k => AdmAField α (fld k)⟩ (AdmAWild α wild) keys g
      | _ => false := by
  funext a
  cases a
  all_goals rfl
@[AdmA_rows] theorem AdmAField_req : AdmAField α (.req t) = AdmA α t := rfl
@[AdmA_rows] theorem AdmAField_optional : AdmAField α (.optional t) = AdmA α t := rfl
@[AdmA_rows] theorem AdmAWild_none : AdmAWild α none = none := rfl
@[AdmA_rows] theorem AdmAWild_some : AdmAWild α (some t) = some (AdmA α t) := rfl
@[AdmA_rows] theorem AdmAList_nil : AdmAList α [] = [] := rfl
@[AdmA_rows] theorem AdmAList_cons : AdmAList α (t :: ts) = AdmA α t :: AdmAList α ts := rfl
@[AdmA_rows] theorem AdmAOptT_none : AdmAOptT α none = none := rfl
@[AdmA_rows] theorem AdmAOptT_some : AdmAOptT α (some t) = some (AdmA α t) := rfl

end Rows


variable (α) in
/-- `⋁` of `AdmA` over a union's options; sound, and inexact for the reason the value side
    gives. -/
def AdmAAny (ts : List Term) (a : Attr) : Bool := anyP (AdmAList α ts) a

@[simp] theorem AdmAAny_nil (a : Attr) : AdmAAny α [] a = false := rfl

@[simp] theorem AdmAAny_cons (t : Term) (ts : List Term) (a : Attr) :
    AdmAAny α (t :: ts) a = (AdmA α t a || AdmAAny α ts a) := rfl

/-- `AdmA`'s literal row, named — for the reason `Adm_literal` gives. -/
@[simp, AdmA_rows] theorem AdmA_literal (k : GroundKind) (x : k.Carrier) (a : Attr) :
    AdmA α (.literal k x) a = inL k x a := rfl

variable (α) in
/-- The converse direction on the attribute side: the row is `dom(p)`, not a bound on it. -/
def ExactA (t : Term) : Prop := ∀ a, AdmA α t a = true ↔ ((denote α t).p a).isSome

/-- `select`'s filter is the term list's, mapped — `filter_AdmList`'s twin. Every row is exact,
    so the filter moves through the map with no hypothesis. -/
theorem filter_AdmAList (opts : List Term) (a : Attr) :
    (denoteList α opts).filter (fun c => (c.p a).isSome)
      = (opts.filter (fun t => AdmA α t a)).map (denote α) := by
  rw [denoteList_eq, List.filter_map]
  congr 2
  funext t
  exact (Alg.AdmA_eq_isSome t [] a).symm

/-- **Every attribute row is exact**, as on the value side. The term language proves it once
    for every universe (`Alg.AdmA_exact`), and this is that theorem at DynamoDB. The numeric
    rows read the attribute payload directly, so a row reaches `dom(p)` with no reader
    between. -/
theorem AdmA_exact (t : Term) : ExactA α t := Alg.AdmA_exact t []

/-! ### The same equation on the read side

The value side needs only `AdmWild`, which is `none` exactly where the body declares no open
block. The read side reads the block the same way: an undeclared name under a closed body is
refused, and each name's own presence pair handles a declared absent name. -/

/-- Soundness of every attribute row, a corollary, as on the value side: `AdmA_exact` carries no
    hypothesis, so the weaker half comes free. -/
theorem AdmA_sound (t : Term) {a v} (hp : (denote α t).p a = some v) : AdmA α t a = true :=
  (AdmA_exact t a).mpr (by rw [hp]; rfl)

/-- **`AdmA` sees a refinement that reads nothing.** `refine(string, ⊥)` reads nothing, and
    `AdmA` says so: the row decodes with `baseCodec .string` and applies `⊥`. -/
theorem AdmA_refine_bot (a : Attr) : AdmA α (.refine .string (.closure (fun _ => false)) ()) a = false := by
  simp [AdmA_rows, Pred.eval]
  cases a <;> simp [denote_rows, prism_rows, orient_rows]

end

end Calculus
