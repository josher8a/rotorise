import Calculus.Lang.ExactV
import Calculus.Dynamo.Lang.Soundness

variable {α : Calculus.Table}

/-!
# §5 — exactness on the value side

§5 used to state admission as a family of per-aspect tables, and every one of them was an
**over**-approximation. `⊤` is sound for every term, so a row that claims nothing can never
fail, and every defect caught in those tables was an imprecision rather than an
unsoundness. `Adm` is admission as a *domain* instead: exact at every constructor.
-/

namespace Calculus

open Alg (ObjectSlot.isReq Term.depth)

noncomputable section

/-! ## The rows a term's subterms hand up

`Adm t` is a *predicate*, and every container row below is a combinator on the predicates its
subterms compute — which is what `denote` does with codecs one level down. The shape is not a
matter of taste: `Term.object`'s field table is a **function**, `sizeOf` is blind to functions,
and a well-founded recursion therefore cannot reach a field's term. A structural recursion can,
and a structural recursion is what this shape buys — the same reason `denote` is structural and
`fieldSem`/`wildSem` are its companions rather than its arguments.
-/

/-- A value-side row, once the subterms' rows are known. -/
abbrev VP := Value → Bool

/- `entryP` and `objAdmV` are the generic rows of `Calculus.Lang.ExactV`. `valPresentT` is the
   generic guard, and no caller reaches it by field notation. -/
export Alg (valPresentT)

/-- What the literal codec **writes**, exactly.

    **This was `inL` conjoined with `Numeral.WF`, and the conjunct is now the carrier's.**
    The second conjunct existed because at `number` an alternative outside §1's `D` was *held*
    and not *written*, so membership alone over-claimed — the same (B) failure ~~LiteralD~~
    forbade in a derivable term, stated here as a fact about the codec, which had no premise to
    lean on. `GroundKind.number.Carrier` is `WFNumeral`, so `inL`'s own row splits on the gate
    and there is no alternative left for the conjunct to catch.

    The retired per-aspect row was always `inL`
    and was therefore inexact at `number` by exactly this conjunct, while the joint row carried
    it and so `Adm_exact` covered the literal. The defect is closed rather than patched:
    nothing was added to make the two agree. -/
noncomputable def AdmLit (k : GroundKind) (x : k.Carrier) (v : Value) : Bool :=
  inL k x v

/-! ## The rows that ask their own codec

    `opaque` and `mu` are the two recursive terms, and their rows below **do not describe a
    set at all**. Each asks the codec it denotes:

        Adm  .opaq    v = ((muCodec opaqStep).e v).isSome
        Adm  (.mu b)  v = ((denote (.mu b)).e v).isSome

    and the read rows do the same with `p`. Three things follow.

    *It is exact by construction.* `denote`'s row is that codec, so the row and `dom(e)` are
    the same function, and `ExactV`/`ExactA` at the term is `Iff.rfl`. That is not a sharp
    analysis of a recursive term; it is the analysis *declining* to be one, and the exactness
    is the codec's, borrowed.

    *It is as precise as the semantics is.* `muCodec` recurses on the *input's own depth*,
    and a row over the term cannot see past the top constructor. Deferring sees all of it,
    because it does not look. `opaque`'s domain is every value (`opaq_total`).

    *Nothing here knows anything about the implementation.* Swap the body of `opaque` — a
    different numeric policy, a different set of options — and every theorem downstream is
    still true and still proved, because none of them mentions what the codec answers.

    A variable is read closed, as the bottom, so its row is `false`. A variable reads its
    binder's stage only inside `muCodec`, and no row reaches inside it.

    ### The warranty behind the row

    `opaque` carries no premise. `Obligations .opaq = True`, and it is `True` because the
    laws are *theorems* here: `lawful_opaq` and `carrier_opaq` (`Opaque.lean`), from the
    guard of its body. A `mu` owes the premises of its body at each stage, and `soundnessIn`
    turns them into the laws of the limit. The row asks a codec **the calculus warrants**.

    ### What "unanalysable" turned out to mean

    `held` was on the unanalysable list because its adapter is a pair of Lean functions, and
    a function is not something a reader can look inside. But a row is not a reader: it is a
    function with the term and the table in hand, and the table gives the word of the term its
    pair `f` and `g` as data. It can apply them. `(c.through f g).e v = c.e (f v)` holds by
    `Iff.rfl`, so `held`'s writable set is the subterm's pulled back along `f` and cut by the caller-side term's row, with no
    appeal to `held`'s iso obligation.

    Three senses had been running together: (i) the term does not carry the information —
    true of nothing here; (ii) the domain cannot be computed without running the codec — true
    of `opaq`, and the reason the row *does* run it, at the price of being
    `noncomputable`; (iii) a reader cannot see through it — true of `held` and
    `opaq`, and not a property of the calculus. -/

/-! ## DynamoDB is an instance

The structure of `Adm` and its exactness are the term language's (`Alg.Adm`, `Alg.Adm_exact`).
DynamoDB supplies the primitive rows, `inBase` and `AdmLit`, and their exactness. -/

/-- The DynamoDB primitive rows: `inBase` at a base and `AdmLit` at a literal. -/
noncomputable instance dynPrimAdm : Alg.PrimAdm dynSyn where
  admV
    | .base k => inBase k
    | .literal k x => AdmLit k x
  admV_exact
    | .base k, v => by
        show inBase k v = true ↔ ((denote (fun _ => (id, id)) (.base k)).e v).isSome = true
        cases k <;> cases v <;> simp [inBase, denote_rows, stringCodec, numberCodec,
          booleanCodec, binaryCodec, nullCodec]
    -- `numberCodec` is read through `numberCodec_e_isSome` rather than unfolded: its `dite` is a
    -- string parser, and `simp` inside it runs out of heartbeats.
    | .literal k x, v => by
        show AdmLit k x v = true ↔ ((denote (fun _ => (id, id)) (.literal k x)).e v).isSome = true
        cases k <;> cases v <;>
          simp [AdmLit, denote_rows, literalCodec, baseCodec, inL,
                stringCodec, booleanCodec, binaryCodec, nullCodec, inD]

variable (α) in
/-- **The joint admission predicate**: the generic row at DynamoDB, at the closed environment.
    A corpus term is closed, so its variables are bound inside it. One structural recursion
    over the term, with the containers recursing through *this*, which is exactly what the
    retired per-aspect rows failed to do. **Every row is exact** (`Adm_exact`). -/
abbrev Adm (t : Term) : VP := Alg.Adm α dynTableA t []

variable (α) in
/-- The payload's row: the declared names are present, and every present name's value is
    admitted by its slot or by the open block. -/
abbrev AdmBody (b : Body) : VP := Alg.AdmBody α dynTableA b []

variable (α) in
/-- A slot's row is its term's. The presence marker is `valPresentT`'s business, so it does
    not reach this row. -/
abbrev AdmField (s : ObjectSlot) : VP := Alg.AdmField α dynTableA s []

variable (α) in
/-- The open block's row, where the body has one: `rcOf`'s mirror. A body with no open
    block refuses, so an undeclared name is refused on the way *out* as well. -/
abbrev AdmWild (w : Option Term) : Option VP := Alg.AdmWild α dynTableA w []

variable (α) in
/-- The options' rows, in order: `denoteList`'s mirror. -/
abbrev AdmList (ts : List Term) : List VP := Alg.AdmList α dynTableA ts []

variable (α) in
/-- The spread's row, where there is one. -/
abbrev AdmOptT (o : Option Term) : Option VP := Alg.AdmOptT α dynTableA o []

/-! ### The rows at the DynamoDB constructors

Each row is the generic row at `dynSyn`, stated at the DynamoDB carriers: `Value.arr` and
`Value.map` in place of the formers' prisms, and the primitive row in place of `PrimAdm.admV`. -/

section Rows
variable (t : Term) (ts : List Term)

@[Adm_rows] theorem Adm_base (k : GroundKind) : Adm α (.base k) = inBase k := rfl
/-- The bottom admits no value, and the row is that sentence. -/
@[Adm_rows] theorem Adm_never (v : Value) : Adm α .never v = false := rfl
/-- The stored predicate is the truth, so the row of `refine` is the caller-side row. -/
@[Adm_rows] theorem Adm_refine (p : Pred) (pA : Alg.Syn.PredA dynSyn) :
    Adm α (.refine t p pA) = fun v => Adm α t v && p.eval v := by
  funext v
  have h : Alg.gate (Alg.denote α dynTableA t []) (fun _ => true) v =
      Alg.Adm α dynTableA t [] v :=
    (Alg.gate_true _ _).trans (Alg.Adm_eq_isSome t [] v).symm
  show (Alg.Adm α dynTableA t [] v && p.eval v &&
    Alg.gate (Alg.denote α dynTableA t []) (fun _ => true) v) =
    (Alg.Adm α dynTableA t [] v && p.eval v)
  rw [h]
  cases Alg.Adm α dynTableA t [] v <;> simp
/-- The stored word is the identity, so the stored gate reads the stored outer at the write. -/
@[Adm_rows] theorem Adm_held (P PA : Term) (k : Word) (kA : List (Alg.Syn.GenA dynSyn × Bool)) :
    Adm α (.held t P PA k kA) = fun v => Adm α t ((α.word k).1 v) && Adm α P v &&
      Alg.gate (denote α t) (fun a => ((denote α PA).p a).isSome) ((α.word k).1 v) := by
  simp only [Adm, Alg.Adm, dynTableA_word]
  rfl
/-- `select` attempts every option, so the row is the disjunction of the options' rows. -/
@[Adm_rows] theorem Adm_union_row : Adm α (.union ts) = fun v => anyP (AdmList α ts) v := rfl
/-- **`set` asks its own codec**, as `opaq` and `mu` do. A row over the elements alone is exact
    only where the element writes injectively and at one member, and an arbitrary element term
    does neither: a `held` can collide two elements, and a `union` can mix `S` and `N`. -/
@[Adm_rows] theorem Adm_set : Adm α (.set t) = fun v => ((setCodec (denote α t)).e v).isSome := rfl
/-- **One row for the one positional container.** `array` and `tuple` are shapes of this term,
    and `alignPL` is the row both shapes reduce to. -/
@[Adm_rows] theorem Adm_list (pre suf : List Term) (sp : Option Term) :
    Adm α (.list pre sp suf) = fun v =>
      match v with
      | .arr vs => alignPL (AdmList α pre) (AdmOptT α sp) (AdmList α suf) vs
      | _ => false := by
  funext v; cases v <;> rfl
@[Adm_rows] theorem Adm_object (b : Body) : Adm α (.object b) = AdmBody α b := rfl
/-- **The second row that asks its own codec**: `denote .opaq` *is* `muCodec opaqStep`, so this
    is `dom(e)` rather than a description of it, and the row's exactness is `Iff.rfl`. -/
@[Adm_rows] theorem Adm_opaq : Adm α .opaq = fun v => ((muCodec opaqStep).e v).isSome := rfl
/-- A closed variable is the bottom. -/
@[Adm_rows] theorem Adm_var (i : Nat) : Adm α (.var i) = fun _ => false := rfl
/-- The second recursive term asks its own codec, for the reason `opaq` does. -/
@[Adm_rows] theorem Adm_mu : Adm α (.mu t) = fun v => ((denote α (.mu t)).e v).isSome := rfl
@[Adm_rows] theorem AdmBody_mk (fields : Finset Name) (fld : {k // k ∈ fields} → ObjectSlot)
    (wild : Option Term) : AdmBody α (.mk fields fld wild) = fun v =>
      match v with
      | .map keys g =>
          valPresentT fields fld keys &&
          objAdmV ⟨fields, fun k => AdmField α (fld k)⟩ (AdmWild α wild) keys g
      | _ => false := by
  funext v; cases v <;> rfl
@[Adm_rows] theorem AdmField_req : AdmField α (.req t) = Adm α t := rfl
@[Adm_rows] theorem AdmField_optional : AdmField α (.optional t) = Adm α t := rfl
@[Adm_rows] theorem AdmWild_none : AdmWild α none = none := rfl
@[Adm_rows] theorem AdmWild_some : AdmWild α (some t) = some (Adm α t) := rfl
@[Adm_rows] theorem AdmList_nil : AdmList α [] = [] := rfl
@[Adm_rows] theorem AdmList_cons : AdmList α (t :: ts) = Adm α t :: AdmList α ts := rfl
@[Adm_rows] theorem AdmOptT_none : AdmOptT α none = none := rfl
@[Adm_rows] theorem AdmOptT_some : AdmOptT α (some t) = some (Adm α t) := rfl

end Rows

/-- `valPresentT` in the form the object row uses: a declared name that must be present is
    present. -/
theorem valPresentT_req (fields : Finset Name) (fld : {k // k ∈ fields} → ObjectSlot)
    (keys : Finset Name) :
    valPresentT fields fld keys
      = decide (∀ k : {k // k ∈ fields}, ObjectSlot.isReq (fld k) = true → k.1 ∈ keys) := by
  unfold valPresentT
  refine decide_eq_decide.mpr ⟨fun hh k hreq => ?_, fun hh k => ?_⟩
  · have hk := hh k
    cases hf : fld k with
    | req t => rw [hf] at hk; exact of_decide_eq_true hk
    | optional t => rw [hf] at hreq; exact absurd hreq (by simp [ObjectSlot.isReq])
  · cases hf : fld k with
    | optional t => rfl
    | req t => exact decide_eq_true (hh k (by rw [hf]; rfl))


/-- A present name that the body declares goes through that name's field. -/
theorem objAdmV_row {c : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (hB : objAdmV ⟨c.fields, fun k => AdmField α (c.at k)⟩ (AdmWild α c.wild) keys g = true)
    {k : Name} (hk : k ∈ keys) (hc : k ∈ c.fields) :
    AdmField α (c.at ⟨k, hc⟩) (g ⟨k, hk⟩) = true := by
  unfold objAdmV at hB
  have hh := of_decide_eq_true hB ⟨k, hk⟩
  rwa [entryP, MapOf.at, dif_pos hc] at hh

/-- A present name the body does not declare goes through the open block: an open body claims
    the name, and the block's row admits the name's value. -/
theorem objAdmV_wild {c : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (hB : objAdmV ⟨c.fields, fun k => AdmField α (c.at k)⟩ (AdmWild α c.wild) keys g = true)
    {k : Name} (hk : k ∈ keys) (hnc : k ∉ c.fields) {w : Term}
    (hw : c.wild = some w) : Adm α w (g ⟨k, hk⟩) = true := by
  unfold objAdmV at hB
  have hh := of_decide_eq_true hB ⟨k, hk⟩
  rwa [entryP, MapOf.at, dif_neg hnc, hw, AdmWild_some] at hh


variable (α) in
/-- `⋁` of `Adm` over a union's options, named — sound, and *not* exact. -/
noncomputable def AdmAny (ts : List Term) (v : Value) : Bool := anyP (AdmList α ts) v

@[simp] theorem AdmAny_nil (v : Value) : AdmAny α [] v = false := rfl

@[simp] theorem AdmAny_cons (t : Term) (ts : List Term) (v : Value) :
    AdmAny α (t :: ts) v = (Adm α t v || AdmAny α ts v) := rfl

theorem Adm_union (opts : List Term) (v : Value) :
    Adm α (.union opts) v = AdmAny α opts v := rfl

/-- A list admits a value exactly when one of its terms does. -/
theorem AdmAny_iff : ∀ {os : List Term} {v : Value},
    AdmAny α os v = true ↔ ∃ t ∈ os, Adm α t v = true
  | [], v => by simp
  | t :: ts, v => by
      rw [AdmAny_cons, Bool.or_eq_true, AdmAny_iff]
      constructor
      · rintro (h | ⟨u, hu, h⟩)
        · exact ⟨t, by simp, h⟩
        · exact ⟨u, by simp [hu], h⟩
      · rintro ⟨u, hu, h⟩
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact Or.inl h
        · exact Or.inr ⟨u, hu', h⟩

/-- `Adm`'s literal row. The row's pattern is *dependent*, since `ls`'s type mentions `k`, so
    the row is stated once here, at an applied value. -/
@[simp, Adm_rows] theorem Adm_literal (k : GroundKind) (x : k.Carrier) (v : Value) :
    Adm α (.literal k x) v = AdmLit k x v := rfl

variable (α) in
/-- §5's converse direction: the row is `dom(e)`, not merely a bound on it. -/
def ExactV (t : Term) : Prop := ∀ v, Adm α t v = true ↔ ((denote α t).e v).isSome

/-- A traversal succeeds exactly when every entry does. -/
theorem traverse_isSome_iff {α β : Type} (f : α → Option β) : ∀ xs : List α,
    (traverse f xs).isSome = true ↔ ∀ x ∈ xs, (f x).isSome = true := by
  intro xs
  induction xs with
  | nil => simp [traverse]
  | cons x xs ih =>
    simp only [traverse, List.mem_cons]
    cases hx : f x with
    | none => simp [hx]
    | some y =>
      cases htr : traverse f xs with
      | none =>
        have hno : ¬ (∀ z ∈ xs, (f z).isSome = true) := by
          intro hall; have := ih.mpr hall; rw [htr] at this; simp at this
        constructor
        · intro hc; simp at hc
        · intro hall; exact absurd (fun z hz => hall z (Or.inr hz)) hno
      | some ys =>
        have hall : ∀ z ∈ xs, (f z).isSome = true := ih.mp (by rw [htr]; rfl)
        simp only [Option.isSome_some, true_iff]
        rintro z (rfl | hz)
        · rw [hx]; rfl
        · exact hall z hz

/-- Each option's row *is* its attempt — given that option's exactness, which is where the
    exactness hypothesis is spent. -/
theorem isSome_e_eq_Adm {t : Term} (h : ExactV α t) (v : Value) :
    ((denote α t).e v).isSome = Adm α t v := by
  exact Bool.coe_iff_coe.mp (by simpa using (h v).symm)

/-- **The option list's filter is the term list's, mapped.** It is an induction rather than a
    rewrite because the agreement above is per-option and hypothesis-bearing. -/
theorem filter_AdmList {opts : List Term} (h : ∀ t ∈ opts, ExactV α t) (v : Value) :
    (denoteList α opts).filter (fun c => (c.e v).isSome)
      = (opts.filter (fun t => Adm α t v)).map (denote α) := by
  induction opts with
  | nil => rfl
  | cons t ts ih =>
    have ht : ExactV α t := h t (by simp)
    have hts : ∀ t' ∈ ts, ExactV α t' := fun t' h' => h t' (by simp [h'])
    simp only [denote_rows, List.filter_cons, isSome_e_eq_Adm ht, ih hts]
    cases hb : Adm α t v <;> simp []

/-- **Every row is exact.** Not a bound on `dom(e)`: `dom(e)`, at every constructor and with no
    hypothesis. The term language proves it once for every universe (`Alg.Adm_exact`), from the
    exactness of the primitive rows, and this is that theorem at DynamoDB. `Adm_sound` is
    `(Adm_exact t v).mpr`. -/
theorem Adm_exact (t : Term) : ExactV α t := Alg.Adm_exact t []

/-- §5's empty-container argument, **derived**: the exact row still admits `[]`. -/
theorem Adm_array_nil (c : Term) : Adm α (.array c) (.arr []) = true := by
  simp [Term.array, Adm_rows, alignPL, alignP, zipP]

/-- …and it is strictly sharper than the `⊤` that was standing in for it. -/
theorem Adm_array_sharp : Adm α (.array (.literal .string "A")) (.arr [.str "B"]) = false := by
  simp [Term.array, Adm_rows, alignPL, alignP, zipP, AdmLit, inL]

/-- Nested, which the old row could not see at any depth. -/
theorem Adm_array_nested :
    Adm α (.array (.array (.literal .string "A"))) (.arr [.arr [.str "B"]]) = false := by
  simp [Term.array, Adm_rows, alignPL, alignP, zipP, AdmLit, inL]


/-- Soundness of every row — **now a corollary.**

    This was a hundred-and-twenty-line recursion on `Term.depth`, separate from `Adm_exact`
    because exactness was proved *given* the subterms' exactness and soundness could assume no
    such thing: `set` and `union` were loose, so a row over them had to be argued monotone
    instead. Both rows are exact now, `Adm_exact` carries no hypothesis, and the
    separate proof was proving the weaker half of something already available.

    The scaffolding it needed — ~~SoundV~~, ~~alignP_sound~~ and the per-constructor soundness
    lemmas — goes with it. -/
theorem Adm_sound (t : Term) {v a} (he : (denote α t).e v = some a) : Adm α t v = true :=
  (Adm_exact t v).mpr (by rw [he]; rfl)

/-! ### No escape hatch

**No row may be `false`, and there is nowhere to put an excuse.** An earlier apparatus —
~~Analysable~~, ~~Excuse~~ and their twins — forced a row per constructor and made adding a `false`
row cost a counterexample. `Alg.Adm_exact : ∀ t, ExactV t`, exhaustive over `Term` with no
hypothesis, forces a *proof* per constructor instead, which is the stronger form of the same
discipline: a new constructor cannot be added without one. -/

end

end Calculus
