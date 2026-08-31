import Calculus.Discharge
import Calculus.Soundness

/-!
# §5 — exactness: what `κ` and `adm` were computing between them

`κ`, `ident`, `adm` and `admA` are **over**-approximations, and that is the whole of the
problem this file exists to fix. `⊤` is sound for every term, so a row that claims nothing
is a row that can never fail, and every one of the defects in `docs/codec-formalization.md`
§4 is an imprecision rather than an unsoundness. A soundness obligation attached to each row
would have caught none of them: `fun _ => true` discharges it with `rfl`.

What catches them is the **converse** direction, and stating it turns up three things the
per-table form obscured.

* **Exactness is a property of the row, not of `adm`.** `adm .string` is `⊤`; it is `κ` that
  carries the kind. Neither is exact alone, and their conjunction is.
* **The conjunction does not survive `held`.** `f` may change a value's kind, so
  `κ (held t f g)` must be `none`, and there is no `κ` left to pair the subterm's `adm`
  with. The gate has to be absorbed into the row — `Adm (.held t f _) v = Adm t (f v)`.
* **The list rows were recursing on the wrong thing.** `array`, `record` and `union` took
  `⋀`/`⋁` of `adm` alone, where exactness needs `⋀`/`⋁` of the *joint* predicate. That is
  one defect with three faces, and it is why §5 could justify `⊤` at a container with an
  argument (the empty array) that is true and proves far less than it was asked to.

`Adm` below is that joint predicate as a single recursion. It is exact for sixteen of the
twenty-three constructors (`Adm_exact`); the other seven are `Analysable`'s `false` rows,
each for a stated reason, and three of those reasons have witnesses here.
-/

namespace Calculus

noncomputable section

mutual

/-- What the literal codec **writes**, exactly.

    `inL` is the prism, and at `number` that is not the whole story: with `Attr.n` carrying
    §1's `Numerals`, an alternative outside `D` is *held* and not *written*, so a row testing
    membership alone would over-claim. The second conjunct is that gap — the same (B) failure
    `LiteralD` exists to forbid in a derivable term, stated here as a fact about the codec,
    which has no premise to lean on.

    Uniform in the base rather than a case per base: `inL k ls (.num d)` can only hold at
    `k = .number`, so the numeral conjunct is `true` wherever it is not the point. -/
noncomputable def AdmLit (k : GroundKind) (ls : NEFinset k.Carrier) (v : Value) : Bool :=
  inL k ls v && (match v with | .num d => Numeral.WF d.toDec | _ => true)

/-- **The joint admission predicate.** What `κ` and `adm` compute between them, as one
    structural recursion — and the containers recurse with *this*, which is exactly what
    the old rows failed to do.

    Rows for the seven `Analysable`-false constructors are sound over-approximations, kept
    so that `Adm` is total; no exactness is claimed for them. -/
noncomputable def Adm : Term → Value → Bool
  | .string   => fun v => match v with | .str _ => true | _ => false
  | .boolean  => fun v => match v with | .bool _ => true | _ => false
  | .binary   => fun v => match v with | .bin _ => true | _ => false
  | .null     => fun v => match v with | .null => true | _ => false
  | .number   => inD
  | .decimal  => isStored
  | .literal k ls => AdmLit k ls
  | .custom ce _ => fun v => (ce v).isSome
  | .array c  => fun v => match v with | .arr xs => AdmAll c xs | _ => false
  -- `record` needs no list companion either: `M`'s entries are a function on the key
  -- set, so "every entry admits" is one `decide` over that set, the way the three `set`
  -- rows are one `decide` over theirs.
  | .record c => fun v =>
      match v with | .map _ f => decide (∀ k, Adm c (f k) = true) | _ => false
  | .refine t q => fun v => Adm t v && q v
  | .legacy t _ => Adm t
  | .lazy t     => Adm t
  | .held t f _ => fun v => Adm t (f v)
  | .nullable t => fun v => Adm t v || (match v with | .null => true | _ => false)
  | .union opts => fun v => AdmAny opts v
  -- `set` recurses like the other containers, and adds nothing. Homogeneity is not a
  -- row's problem — §1's three set types are three constructors, so an element's kind is
  -- fixed by which one it is — and non-emptiness is not one either, now that `℘⁺fin` is
  -- the payload type. What is left is the element recursion.
  | .set c      => fun v =>
      match v with
      | .strSet S => decide (∀ s ∈ S.1, Adm c (.str s) = true)
      | .numSet S => decide (∀ d ∈ S.1, Adm c (.num d) = true)
      | .binSet S => decide (∀ b ∈ S.1, Adm c (.bin b) = true)
      | _ => false
  | .tuple _ _  => fun v => match v with | .arr _ => true | _ => false
  | .object _ _ _ => fun v => match v with | .map _ _ => true | _ => false
  | .dunion d opts => fun v =>
      match tagOfV d v with
      | some tag => decide (tag ∈ allTags d opts)
      | none => false
  | .opaq _ => fun _ => true

/-- `⋀` of `Adm` over a container's elements. -/
noncomputable def AdmAll : Term → List Value → Bool
  | _, [] => true
  | c, x :: xs => Adm c x && AdmAll c xs

/-- `⋁` of `Adm` over a union's options. Sound, but *not* exact — `select` demands
    exactly one admitting option, so a union is exact only under (U). -/
noncomputable def AdmAny : List Term → Value → Bool
  | [], _ => false
  | t :: ts, v => Adm t v || AdmAny ts v

end

/-- `Adm`'s literal row, named.

    Nothing should `simp [Adm]` at a literal: the row's pattern is *dependent* — `ls`'s type
    mentions `k` — so generating the table's equation lemmas across it is expensive enough to
    exhaust the heartbeat budget in proofs that used to close in one step. Stating the row once
    contains that cost, and every literal proof below rewrites with this instead. -/
@[simp] theorem Adm_literal (k : GroundKind) (ls : NEFinset k.Carrier) (v : Value) :
    Adm (.literal k ls) v = AdmLit k ls v := by unfold Adm; rfl

/-- §5's converse direction: the row is `dom(e)`, not merely a bound on it. -/
def ExactV (t : Term) : Prop := ∀ v, Adm t v = true ↔ ((denote t).e v).isSome

/-- The terms whose rows carry an exactness proof, subterms included. The `false` rows are
    the hatch, and each has a reason:

    * `opaq` — `opaqCodecω`'s domain recurses on the *input's* depth; no syntactic set names it.
    * `union` — `select` admits only when **exactly one** option does, so `⋁` is exact
      precisely under (U), which is a semantic obligation rather than a syntactic row.
    * `dunion` — the tag is checked, the matched option's own admission is not.
    * `set` — `asWireSet` also demands payload homogeneity, a fact about attributes.
    * `object`, `tuple` — name admission and alignment.
    * `nullable` — `ownsNull` is a disjunction over *both* halves, so a read that reaches
      the null point suppresses the wrapper while the write still refuses it
      (`not_ExactV_nullable`).

    This list is the escape hatch, and it is closed: a row cannot be left vague by
    accident, only by being added here, in the open. -/
def Analysable : Term → Bool
  | .string | .boolean | .binary | .null | .number | .decimal
  | .literal _ _ | .custom _ _ => true
  | .array c | .record c | .refine c _ | .legacy c _ | .lazy c
  | .held c _ _ => Analysable c
  | .opaq _ | .object _ _ _ | .tuple _ _ | .set _ | .dunion _ _ | .union _
  | .nullable _ => false

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

/-- `AdmAll` transported across the element's exactness. -/
theorem AdmAll_iff {c : Term} (h : ExactV c) : ∀ xs : List Value,
    AdmAll c xs = true ↔ ∀ x ∈ xs, ((denote c).e x).isSome = true := by
  intro xs; induction xs with
  | nil => simp [AdmAll]
  | cons x xs ih => simp [AdmAll, ih, h x]

/-- **Sixteen of the twenty-three rows are exact.** Not a bound on `dom(e)` — `dom(e)`.

    The `held` case is the one worth reading: it appeals to the subterm at `f v`, which is
    the pullback, and it is one line because `(c.through f g).e v = c.e (f v)` holds by
    `Iff.rfl`. The `array` and `record` cases are the repair of §5's container rows. -/
theorem Adm_exact : ∀ (t : Term), Analysable t = true → ExactV t
  | .string, _ => by intro v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, stringCodec]
  | .boolean, _ => by intro v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, booleanCodec]
  | .binary, _ => by intro v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, binaryCodec]
  | .null, _ => by intro v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, nullCodec]
  | .number, _ => by intro v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, inD]
  | .decimal, _ => by intro v; cases v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, isStored]
  -- three rows into one, and `numberCodec` is read through `numberCodec_e_isSome` rather
  -- than unfolded: its `dite` is a string parser, and `simp` inside it runs out of heartbeats.
  | .literal k ls, _ => by
      intro v
      cases k <;> cases v <;>
        simp [AdmLit, denote, denote, literalCodec, baseCodec, inL,
              stringCodec, booleanCodec, binaryCodec, nullCodec, inD]
  | .custom ce cp, _ => by intro v; simp [Adm, denote, denote]
  | .array c, ha => by
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v
      cases v
      case arr xs =>
        simp only [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec, Option.isSome_map]
        rw [AdmAll_iff hc, ← traverse_isSome_iff]
        cases traverse (denote c).e xs <;> simp
      all_goals simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec]
  | .record c, ha => by
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v
      cases v
      -- The entry-key transport is gone with the traversal: `funImage` is defined
      -- exactly where every entry's `e` is, which is the row verbatim.
      case map keys f =>
        simp only [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec, Option.isSome_map', decide_eq_true_eq,
          funImage_isSome_iff]
        exact forall_congr' fun k => hc (f k)
      -- the other nine rows are refused on both sides, and unfolding `recordCodec`'s
      -- `funImage` to see it is more work than reading it off the two `false`s
      all_goals simp only [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec, Option.map_none',
        Option.isSome_none, Bool.false_eq_true]
  | .refine c q, ha => by
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v; cases hq : q v <;> simp [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.restrict, hq, hc v]
  | .legacy c r, ha => by
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v; simpa [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.extendRead] using hc v
  | .lazy c, ha => by
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v; simpa [Adm, denote] using hc v
  | .held c f g, ha => by
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v; simpa [Adm, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.through] using hc (f v)
  | .set _, ha | .tuple _ _, ha | .object _ _ _, ha | .dunion _ _, ha
  | .union _, ha | .nullable _, ha | .opaq _, ha => by simp [Analysable] at ha


/-- §5's empty-container argument, **derived**: the exact row still admits `[]`. -/
theorem Adm_array_nil (c : Term) : Adm (.array c) (.arr []) = true := by
  simp [Adm, AdmAll]

/-- …and it is strictly sharper than the `⊤` that was standing in for it. -/
theorem Adm_array_sharp : Adm (.array (.literal .string (.of "A" ∅))) (.arr [.str "B"]) = false := by
  simp [Adm, AdmAll, AdmLit, inL, NEFinset.of]

/-- Nested, which the old row could not see at any depth. -/
theorem Adm_array_nested :
    Adm (.array (.array (.literal .string (.of "A" ∅)))) (.arr [.arr [.str "B"]]) = false := by
  simp [Adm, AdmAll, AdmLit, inL, NEFinset.of]

/-- A migration whose *read* reaches the null point while its write does not. -/
def rNull : Attr → Option Value := fun a => match a with | .null => some (.str "x") | _ => none

/-- **Why `nullable` is in the hatch**, with a witness rather than an assertion.
    `ownsNull` is `(e null).isSome || (p null).isSome` — a disjunction over *both* halves.
    A `legacy` that reads the null point makes the guard fire, so `withNull` adds nothing,
    and the wrapper's `e` still refuses `null` — while any row of the shape
    `Adm t v || v = null` claims it. -/
theorem not_ExactV_nullable : ¬ ExactV (.nullable (.legacy .string rNull)) := by
  intro h
  have hadm : Adm (.nullable (.legacy .string rNull)) .null = true := by simp [Adm]
  have := (h .null).mp hadm
  simp only [denote, Codec.withNull, Codec.extendRead] at this
  simp [denote, Codec.withNull, Codec.ownsNull, Codec.extendRead, stringCodec, rNull] at this


/-! ## The hatch, made expensive

`Analysable`'s `false` rows are the last place a vague row can hide. The three exhaustive
recursions above already force a *row* per constructor, so a new `Term` constructor cannot
be added silently. What they do not force is a **reason**: the seven `false` rows could be
eight, and the eighth would cost one identifier and a docstring nobody has to write.

So the excuses are a type. `Excuse.covers` says which term shapes each one may be invoked
for, and `analysable_excused` — exhaustive over `Term` — says every `Analysable`-false term
has one. Filing `array` under `opaqueDepth` is then a type error, and adding a row to the
hatch means naming which of these five things is true of it, in the open, where a reviewer
reads the reason rather than trusting that one existed.

`covers`' catch-all is the one place a catch-all is right, and the polarity is why: it
answers **`false`** — *no excuse covers this* — so a new `Term` constructor lands in "no
excuse available" and `analysable_excused` forces `Analysable` to call it analysable, which
forces `Adm_exact` to prove it. The failure mode of every other catch-all in this
development was that it silently said yes. -/

/-- The five reasons a row may decline to be exact. There is no `other`, deliberately. -/
inductive Excuse where
  /-- The domain recurses on the *input's* own depth, so no syntactic set names it. -/
  | opaqueDepth
  /-- `select` admits only where **exactly one** option does, so `⋁` is exact precisely
      under (U) — a semantic obligation rather than a syntactic row. -/
  | uniqueAdmission
  /-- `asWireSet` demands payload homogeneity: a fact about attributes, not values. -/
  | payloadShape
  /-- Name admission and alignment, which are about the shape of the container's spec. -/
  | nameAdmission
  /-- `ownsNull` is a disjunction over **both** halves, so a read that reaches the null
      point suppresses the wrapper while the write still refuses it. -/
  | nullOwnership
  /-- `q` tests the value a read *produces*, and no syntactic set of attributes bounds
      that. Attribute side only — on the value side `refine` narrows exactly. -/
  | valueUnderRead
  deriving DecidableEq

/-- Which term shapes each excuse may be invoked for. The catch-all answers `false`, so a
    new constructor is *not* excusable by default — see the note above. -/
def Excuse.covers : Excuse → Term → Bool
  | .opaqueDepth,     .opaq _      => true
  | .uniqueAdmission, .union _     => true
  | .uniqueAdmission, .dunion _ _  => true
  | .payloadShape,    .set _       => true
  | .nameAdmission,   .object _ _ _  => true
  | .nameAdmission,   .tuple _ _   => true
  | .nullOwnership,   .nullable _  => true
  | _, _ => false

/-- The subterm a propagating row inherits its answer from. The catch-all is `none` —
    "does not inherit" — so a new constructor must justify itself at the root rather than
    quietly borrowing a subterm's excuse. -/
def inheritsFrom : Term → Option Term
  | .array c | .record c | .refine c _ | .legacy c _ | .lazy c | .held c _ _ => some c
  | _ => none

/-- **Every row that declines exactness either names a reason of the right shape, or
    inherits the refusal from a subterm.** Exhaustive over `Term`, so growing the hatch
    means either producing an `Excuse` that covers the new shape — which requires extending
    `covers`, a visible act — or leaving this proof unclosed. There is no third branch and
    no `other` constructor to reach for. -/
theorem analysable_excused : ∀ (t : Term), Analysable t = false →
    (∃ e : Excuse, e.covers t = true) ∨ (∃ c, inheritsFrom t = some c ∧ Analysable c = false)
  | .opaq _, _      => .inl ⟨.opaqueDepth, rfl⟩
  | .union _, _     => .inl ⟨.uniqueAdmission, rfl⟩
  | .dunion _ _, _  => .inl ⟨.uniqueAdmission, rfl⟩
  | .set _, _       => .inl ⟨.payloadShape, rfl⟩
  | .object _ _ _, _  => .inl ⟨.nameAdmission, rfl⟩
  | .tuple _ _, _   => .inl ⟨.nameAdmission, rfl⟩
  | .nullable _, _  => .inl ⟨.nullOwnership, rfl⟩
  -- The propagating wrappers decline only by inheritance, and say so.
  | .array c, h | .record c, h | .refine c _, h | .legacy c _, h | .lazy c, h
  | .held c _ _, h => .inr ⟨c, rfl, by simpa [Analysable] using h⟩
  -- The exact rows: the hypothesis refutes them, which is the point — a term cannot both
  -- carry an exactness proof and claim an excuse.
  | .string, h | .boolean, h | .binary, h | .null, h | .number, h | .decimal, h
  | .literal _ _, h | .custom _ _, h => nomatch h

/-- **No excuse names an exact row.** The hatch cannot be used as a shortcut past an
    obligation that is provable: a covered shape really does decline. -/
theorem excuse_shapes (e : Excuse) (t : Term) (h : e.covers t = true) :
    Analysable t = false := by
  cases e <;> cases t <;> simp_all [Excuse.covers, Analysable]

/-- …stated the way a reviewer wants it: an exact row has no excuse available to it, so
    the two halves of `analysable_excused` are exclusive as well as exhaustive. -/
theorem not_excused_of_analysable {t : Term} (h : Analysable t = true) :
    ¬ ∃ e : Excuse, e.covers t = true := by
  rintro ⟨e, he⟩
  rw [excuse_shapes e t he] at h
  exact absurd h (by simp)

/-- Entrywise soundness lifted to a container's traversal. Generalised over the codec so
    the fueled and fuel-free forms share it. -/
theorem AdmAll_sound_aux {c : Term} {C : Codec}
    (hc : ∀ {v a}, C.e v = some a → Adm c v = true) :
    ∀ {xs : List Value} {ys}, traverse C.e xs = some ys → AdmAll c xs = true
  | [], _, _ => by simp [AdmAll]
  | x :: xs, ys, h => by
      simp only [traverse] at h
      cases hx : C.e x with
      | none => rw [hx] at h; exact nomatch h
      | some y =>
        cases hxs : traverse C.e xs with
        | none => rw [hx, hxs] at h; exact nomatch h
        | some ys' => simp [AdmAll, hc hx, AdmAll_sound_aux hc hxs]

set_option maxHeartbeats 1000000 in
-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- Soundness of every row. The recursion is on `Term.depth`, which
    is what `κ_sound` and `adm_sound` do: a term recursion here makes the equation compiler
    elaborate all twenty-three heavy cases as one well-founded definition, and it does not
    finish. The heartbeat bump is for the twenty-three-way `cases`, not for any one case. -/
theorem Adm_sound : ∀ (t : Term) {v a},
    (denote t).e v = some a → Adm t v = true
  | t, v, a, he => by
    cases t
    case string => cases v <;> simp_all [Adm, denote, stringCodec]
    case boolean => cases v <;> simp_all [Adm, denote, booleanCodec]
    case binary => cases v <;> simp_all [Adm, denote, binaryCodec]
    case null => cases v <;> simp_all [Adm, denote, nullCodec]
    -- read off the write's `isSome` rather than unfolding the gate: the decision inside
    -- it is `Numeral.WF`'s parser
    case number =>
      have hs : (numberCodec.e v).isSome = true := by
        have h' : numberCodec.e v = some a := he
        rw [h']; rfl
      rw [numberCodec_e_isSome] at hs
      simpa [Adm] using hs
    case decimal =>
      have hs : (decimalCodec.e v).isSome = true := by
        have h' : decimalCodec.e v = some a := he
        rw [h']; rfl
      rw [decimalCodec_e_isSome] at hs
      simpa [Adm] using hs
    -- Three cases into one, and the numeric base no longer needs its own `show`: the codec
    -- **is** `(baseCodec k).restrict (inL k ls)`, so `restrict_e_isSome` and
    -- `numberCodec_e_isSome` answer it without `Codec.restrict` being unfolded into an `if`
    -- over `Numeral.WF`'s parser.
    case literal k ls =>
      have hs : ((denote (.literal k ls)).e v).isSome = true := by rw [he]; rfl
      clear he
      cases k <;> cases v <;>
        simp_all [AdmLit, denote, literalCodec, baseCodec, inL, stringCodec, inD,
                  booleanCodec, binaryCodec, nullCodec]
    case custom ce cp => simp_all [Adm, denote]
    case opaq lossy => simp [Adm]
    case set c =>
      cases v
      case strSet S =>
        simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, setCodec] at he
        have hall := encSet_elem he
        simp only [Adm, decide_eq_true_eq]
        refine fun y hy => ?_
        obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall y hy)
        exact Adm_sound c ha'
      case numSet S =>
        simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, setCodec] at he
        have hall := encSet_elem he
        simp only [Adm, decide_eq_true_eq]
        refine fun y hy => ?_
        obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall y hy)
        exact Adm_sound c ha'
      case binSet S =>
        simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, setCodec] at he
        have hall := encSet_elem he
        simp only [Adm, decide_eq_true_eq]
        refine fun y hy => ?_
        obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall y hy)
        exact Adm_sound c ha'
      all_goals (simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, setCodec] at he; exact nomatch he)
    case tuple ts tl => cases v <;> simp_all [Adm, denote, tupleCodec]
    -- `objectCodecCore` is `carriedCodec` now, so the non-`map` rows are refused by the
    -- value prism rather than by a traversal: `mapV.out` is what says so.
    case object fs r =>
      cases v <;>
        simp_all [Adm, denote, objectCodec, objectCodecCore, carriedCodec, mapV, Ctor.out]
    case array c =>
      cases v
      case arr xs =>
        simp only [Adm]
        simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec] at he
        obtain ⟨ys, hys, -⟩ := Option.map_eq_some'.mp he
        exact AdmAll_sound_aux (fun {v a} h => Adm_sound c h) hys
      all_goals (simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec] at he; exact nomatch he)
    case record c =>
      cases v
      case map keys f =>
        simp only [Adm, decide_eq_true_eq]
        simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec] at he
        obtain ⟨g, hg, -⟩ := Option.map_eq_some'.mp he
        exact fun k => Adm_sound c (funImage_some hg k)
      all_goals (simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec] at he; exact nomatch he)
    case refine c q =>
      obtain ⟨hq, hc⟩ := restrict_e.mp he
      simp [Adm, Adm_sound c hc, hq]
    case legacy c r => simpa [Adm] using Adm_sound c (extendRead_e.mp he)
    case lazy c => simpa [Adm] using Adm_sound c he
    case held c f g => simpa [Adm] using Adm_sound c he
    case nullable c =>
      cases hw : (denote c).ownsNull with
      | true =>
        rw [show (denote (.nullable c)).e = (denote c).e from
          withNull_e_of_owns hw] at he
        simp [Adm, Adm_sound c he]
      | false =>
        rw [show denote (.nullable c) = (denote c).orNull from
          withNull_eq_orNull hw] at he
        rcases orNull_e.mp he with ⟨rfl, -⟩ | ⟨-, hc⟩
        · simp [Adm]
        · simp [Adm, Adm_sound c hc]
    case dunion d opts =>
      have h2 := adm_sound _ he
      have heq : Adm (.dunion d opts) v = adm (.dunion d opts) v := by rw [Adm, adm]; rfl
      rw [heq]; exact h2
    case union opts =>
      simp only [denote, optionSems_eq] at he
      obtain ⟨o, ho, -, hoe⟩ := altCodec_e_admits he
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      rw [optionSemOf_c] at hoe
      -- the recursive call is taken **here**, before the generalisation: `key` quantifies over
      -- an arbitrary list containing `tx`, and a measure on the term cannot bound a call made
      -- inside that. With fuel it did not have to.
      have htx' : Adm tx v = true := Adm_sound tx hoe
      have key : ∀ (ts : List Term), tx ∈ ts → AdmAny ts v = true := by
        intro ts hts
        induction ts with
        | nil => exact absurd hts (by simp)
        | cons t0 ts ih =>
          rcases List.mem_cons.mp hts with rfl | h'
          · simp [AdmAny, htx']
          · simp [AdmAny, ih h']
      simpa [Adm] using key opts htx

termination_by t _ _ => Term.depth t
decreasing_by term_depth_wf

/-! **Every row is a sound over-approximation, the hatch included.**

    `Adm_exact` binds the sixteen analysable rows to `dom(e)` in both directions. The other
    seven had, until this theorem, *no* obligation at all: nothing stopped a hatch row being
    written `fun _ => false`, which would have been an outright unsoundness rather than the
    imprecision every defect in the log so far has been. A hatch row may be **loose**; it
    may not be **wrong**, and that is now checked. -/
/-! ### Every excuse earned

`Excuse` and `covers` say which rows may decline exactness. Nothing so far said the
declining was *warranted*: a constructor could be added naming a shape that is secretly
provable, and the hatch would absorb a row that ought to carry a proof.

So each excuse owes a witness — a term of a shape it covers, for which exactness genuinely
fails. `excuse_witnessed` collects the five. Adding an excuse now costs a counterexample,
and for a shape that is exact there is none to be had.

**What this does not claim**, because the stronger reading is false: *not* every covered
term is inexact. `union []` is covered by `uniqueAdmission` and is perfectly exact — `Adm`
is `false` and so is admission, there being no option to admit. The obligation is that an
excuse names a real phenomenon, not that it is tight on every term of that shape. Widening
`covers` to a shape that is always exact is still caught; widening it to one that is
sometimes exact is not, and that is the residual softness. -/

/-- An adapter that collapses two distinct strings onto one. -/
def collapse : Value → Value := fun _ => .str "x"

/-- **`set`'s row still over-claims, but no longer for the reason §5 gave.** Heterogeneity
    is gone — a value set is typed, so its elements cannot differ in kind. What remains is
    *collision*: the row asks that every element write, and `encSet` asks in addition that
    they write to **distinct** payloads, because a set codec that merged two elements could
    not retract. -/
theorem not_ExactV_set : ¬ ExactV (.set (.held .string collapse (fun v => v))) := by
  intro h
  have h2 := (h (.strSet (.of "a" {"b"}))).mp (by simp [Adm, NEFinset.of, collapse])
  simp (config := { decide := true }) [denote, denote, setCodec, encSet, neSetImage,
        Codec.through, stringCodec, collapse, setImage, sC, nC, bC, NEFinset.of] at h2

/-- `tuple`'s over-claims on alignment: one component against two elements. -/
theorem not_ExactV_tuple : ¬ ExactV (.tuple [.string] none) := by
  intro h
  have := (h (.arr [.str "a", .str "b"])).mp (by simp [Adm])
  simp [denote, denote, denoteList, denoteOpt, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, tupleCodec, align, stringCodec] at this

/-- **(U) failing in its purest form.** `select` writes only where *exactly one* option
    admits, so two copies of one option admit everything and write nothing — while `⋁`
    says yes. No arithmetic, no `Double`, just the counting `select` does. -/
theorem not_ExactV_union : ¬ ExactV (.union [.string, .string]) := by
  intro h
  have := (h (.str "a")).mp (by simp [Adm, AdmAny])
  simp [denote, denote, optionSems, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, specOf, optionSemOf, altCodec, select,
    stringCodec] at this

/-- `opaq`'s ⊤ over-claims, and after the set repair the **only** place it does so is the
    numeral gate: `opaq false` is `refuse`, which writes no number at all.

    This used to be witnessed by `.strSet ∅`, which every one of the eight options refused
    and which needed nothing to construct. `℘⁺fin` has removed that value from the
    language — the repair working — and taken the Double-free witness with it. What is
    left is `.num`, and §1 axiomatizes `Double` with `toDec`, `ofDec`, `roundtrip` and
    `decEq` and **no inhabitant**: `roundtrip` starts from a `Double` rather than producing
    one. So the hypothesis is an inhabitant of §1's number carrier, which is the honest
    form of "numbers exist" and is not assumed anywhere else in the development. -/
theorem not_ExactV_opaq (d : Double) : ¬ ExactV (.opaq false) := by
  intro h
  have h2 := (h (.num d)).mp (by simp [Adm])
  have hd : (denote (Term.opaq false)).e (.num d)
      = (if false then numberCodec else Codec.empty).e (.num d) := by
    show (opaqCodecω false).e (.num d) = _
    simp only [opaqCodecω, Value.depth]
    exact opaqCodec_e_num false 0 d
  rw [hd] at h2
  exact absurd h2 (by simp [Codec.empty])

/-- **Every excuse is earned.** Exhaustive over `Excuse`, so a new constructor must come
    with a term of a shape it covers on which exactness actually fails — which, for a shape
    that is exact, cannot be produced. -/
theorem excuse_witnessed (d : Double) : ∀ (e : Excuse) (t : Term), e.covers t = true →
    ∃ t' : Term, e.covers t' = true ∧ ¬ ExactV t'
  | .opaqueDepth, _, _     => ⟨.opaq false, rfl, not_ExactV_opaq d⟩
  | .uniqueAdmission, _, _ => ⟨.union [.string, .string], rfl, not_ExactV_union⟩
  | .payloadShape, _, _    => ⟨.set (.held .string collapse (fun v => v)), rfl, not_ExactV_set⟩
  | .nameAdmission, _, _   => ⟨.tuple [.string] none, rfl, not_ExactV_tuple⟩
  | .nullOwnership, _, _   => ⟨.nullable (.legacy .string rNull), rfl, not_ExactV_nullable⟩
  -- The two attribute-side reasons cover nothing here, so the hypothesis is unsatisfiable.
  | .valueUnderRead, t, h  => by cases t <;> simp [Excuse.covers] at h

/-! ## The attribute side

`Adm` is the value half. `admA` is the attribute half of §5's tables, and it has no
`Adm`-shaped counterpart — which is the first reason the analysis tables cannot simply be
renamed onto `Adm`. `AdmA` below is that counterpart's definition and its soundness proof.

The mirror is not symmetric, and the asymmetries are §1's rather than this file's: the
numeric rows go through `Double.ofDec`, `refine` cannot narrow a read, and `legacy` widens
one. Each is a row here rather than a remark. -/

mutual

/-- What the literal codec **reads**, exactly.

    Three rows into one, and the `number` row is the only one that is not simply membership:
    the read goes through `Double.ofDec`, and `&& WF` is there because the base's own read is
    `number`'s restricted, so it refuses a numeral whose double re-spells outside `D` even when
    that double is in `ℓ`.

    Note this is `AdmA`'s exact row, not §5's table row (`admALit` in `Discharge`), which is
    `⊤` at `number` and cannot be otherwise — a *syntactic* set of attributes does not bound a
    read that goes through `Double.ofDec`. The two disagreeing at exactly one base is the
    content of `admA_literalN_blind`. -/
noncomputable def AdmALit : (k : GroundKind) → NEFinset k.Carrier → Attr → Bool
  | .string,  ls, .s s    => decide (s ∈ ls.1)
  | .boolean, ls, .bool b => decide (b ∈ ls.1)
  | .binary,  ls, .b b    => decide (b ∈ ls.1)
  | .null,    _,  .null   => true
  | .number,  ls, .n x    => (match Double.ofDec x.1 with
                              | some d => decide (d ∈ ls.1) && Numeral.WF d.toDec
                              | none => false)
  | _, _, _ => false

/-- **The joint admission predicate, attribute side.** The mirror of `Adm` across §1's
    asymmetry, and it is not a symmetric mirror — three rows differ in kind, not degree.

    * `number`, `literalN` and a numeric `literal` go through `Double.ofDec`, which is
      axiomatized. The domain is still *expressible* — `ofDec` is a function and this row
      may call it — so these rows are sharper here than §5's `⊤`, at the cost of being
      `noncomputable`, which `adm` already was.
    * `refine` cannot narrow here: `q` tests the value a read *produces*, and no syntactic
      set of attributes bounds that. The row passes the subterm's through, which is sound
      and not exact.
    * `legacy` is `⊤`, because `extendRead` widens `p` past the subterm's set — the
      asymmetry `not_admA_legacy` records, and the reason `adm` and `admA` split at all. -/
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
  | .custom _ cp => fun a => (cp a).isSome
  | .array c  => fun a => match a with | .l as => AdmAAll c as | _ => false
  | .record c => fun a =>
      match a with | .m _ g => decide (∀ k, AdmA c (g k) = true) | _ => false
  | .held t _ _ => AdmA t
  | .lazy t   => AdmA t
  -- hatch
  | .refine t _ => AdmA t
  -- `legacy` is the read-side **alternative**, not an adapter: `p` is the subterm's channel
  -- falling back to `r`'s, so the domain is the *union* of the two. `r` is data the term
  -- carries, exactly as `held`'s `f` and `custom`'s `cp` are, so the row can apply it.
  | .legacy t r => fun a => AdmA t a || (r a).isSome
  | .nullable t => fun a => AdmA t a || (match a with | .null => true | _ => false)
  | .union opts => fun a => AdmAAny opts a
  | .set _    => fun a => match a with | .ss _ | .ns _ | .bs _ => true | _ => false
  | .tuple _ _ => fun a => match a with | .l _ => true | _ => false
  | .object _ _ _ => fun a => match a with | .m _ _ => true | _ => false
  | .dunion d opts => fun a =>
      match tagOfA d a with
      | some tag => decide (tag ∈ allTags d opts)
      | none => false
  | .opaq _ => fun _ => true

/-- `⋀` of `AdmA` over a container's entries. -/
noncomputable def AdmAAll : Term → List Attr → Bool
  | _, [] => true
  | c, a :: as => AdmA c a && AdmAAll c as

/-- `⋁` over a union's options; sound, and exact only under (U), as on the value side. -/
noncomputable def AdmAAny : List Term → Attr → Bool
  | [], _ => false
  | t :: ts, a => AdmA t a || AdmAAny ts a

end

/-- `AdmA`'s literal row, named — for the reason `Adm_literal` gives. -/
@[simp] theorem AdmA_literal (k : GroundKind) (ls : NEFinset k.Carrier) (a : Attr) :
    AdmA (.literal k ls) a = AdmALit k ls a := by unfold AdmA; rfl

/-! Two bases stated as standalone lemmas, with their carriers written out.

`GroundKind.Carrier` is reducible, so `NEFinset k.Carrier` at a *constructor* `k` is the same
type as `NEFinset Bytes` — but it is not the same *expression*, and `simp` inside the goal
re-derives that on every rewrite. At `binary` (`List UInt8`) and `null` (`Unit`) that was
enough to exhaust the heartbeat budget. Taking the carrier as a plain type in the statement
does the reduction once, at elaboration. -/

theorem AdmALit_binary_exact (ls : NEFinset Bytes) (a : Attr) :
    AdmA (.literal .binary ls) a = true ↔ ((denote (Term.literal .binary ls)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec, Codec.restrict, inL,
          binaryCodec]

theorem AdmALit_null_exact (ls : NEFinset Unit) (a : Attr) :
    AdmA (.literal .null ls) a = true ↔ ((denote (Term.literal .null ls)).p a).isSome = true := by
  cases a <;>
    simp [AdmA_literal, AdmALit, denote, denote, literalCodec, baseCodec, Codec.restrict, inL,
          nullCodec]


/-- Entrywise soundness lifted to a container's traversal, attribute side. -/
theorem AdmAAll_sound_aux {c : Term} {C : Codec}
    (hc : ∀ {a v}, C.p a = some v → AdmA c a = true) :
    ∀ {as : List Attr} {vs}, traverse C.p as = some vs → AdmAAll c as = true
  | [], _, _ => by simp [AdmAAll]
  | x :: as, vs, h => by
      simp only [traverse] at h
      cases hx : C.p x with
      | none => rw [hx] at h; exact nomatch h
      | some y =>
        cases hxs : traverse C.p as with
        | none => rw [hx, hxs] at h; exact nomatch h
        | some vs' => simp [AdmAAll, hc hx, AdmAAll_sound_aux hc hxs]

set_option maxHeartbeats 1000000 in
-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- Soundness of every attribute row; recursion on `Term.depth`, as on the value side. The
-/
theorem AdmA_sound : ∀ (t : Term) {a v},
    (denote t).p a = some v → AdmA t a = true
  | t, a, v, hp => by
    cases t
    case string => cases a <;> simp_all [AdmA, denote, stringCodec]
    case boolean => cases a <;> simp_all [AdmA, denote, booleanCodec]
    case binary => cases a <;> simp_all [AdmA, denote, binaryCodec]
    case null => cases a <;> simp_all [AdmA, denote, nullCodec]
    case number =>
      cases a
      case n x =>
        simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, numberCodec] at hp
        cases hx : Double.ofDec x.1 <;> rw [hx] at hp <;> simp_all [AdmA]
      all_goals (simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, numberCodec] at hp; exact nomatch hp)
    case decimal => cases a <;> simp_all [AdmA, denote, decimalCodec]
    -- One case where there were three, and the shape of the argument is now visible: the
    -- `number` base is the only one whose read goes through `Double.ofDec`, so it is the only
    -- one where the exact row and §5's table row differ. The other four coincide, and
    -- `admA_sound` carries them.
    case literal k ls =>
      cases k
      case number =>
        cases a
        case n x =>
          simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, literalCodec, baseCodec, Codec.restrict, numberCodec, inL] at hp
          cases hx : Double.ofDec x.1 with
          | none => rw [hx] at hp; simp at hp
          | some d =>
            rw [hx] at hp
            by_cases hw : Numeral.WF d.toDec = true <;> simp_all [AdmALit]
        all_goals
          (simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, literalCodec, baseCodec, Codec.restrict, numberCodec, inL] at hp
           exact nomatch hp)
      all_goals
        (rw [show AdmA (.literal _ ls) a = admA (.literal _ ls) a from by
              cases a <;> simp [AdmALit, admA, admALit]]
         exact admA_sound _ hp)
    case custom ce cp => simp_all [AdmA, denote]
    case opaq lossy => simp [AdmA]
    case legacy c r =>
      simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.extendRead] at hp
      cases hc : (denote c).p a with
      | some w => rw [hc] at hp; simp [AdmA, AdmA_sound c hc]
      | none => rw [hc] at hp; simp [AdmA, hp]
    case set c => cases a <;> simp_all [AdmA, denote, setCodec]
    case tuple ts tl => cases a <;> simp_all [AdmA, denote, tupleCodec]
    case object fs r =>
      cases a <;>
        simp_all [AdmA, denote, objectCodec, objectCodecCore, carriedCodec, mA, Ctor.out]
    case array c =>
      cases a
      case l as =>
        simp only [AdmA]
        simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec] at hp
        obtain ⟨vs, hvs, -⟩ := Option.map_eq_some'.mp hp
        exact AdmAAll_sound_aux (fun {a v} h => AdmA_sound c h) hvs
      all_goals (simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec] at hp; exact nomatch hp)
    case record c =>
      cases a
      case m keys g =>
        simp only [AdmA, decide_eq_true_eq]
        simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec] at hp
        obtain ⟨f, hf, -⟩ := Option.map_eq_some'.mp hp
        exact fun k => AdmA_sound c (funImage_some hf k)
      all_goals (simp only [denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec] at hp; exact nomatch hp)
    case refine c q => simpa [AdmA] using AdmA_sound c (restrict_p.mp hp).1
    case lazy c => simpa [AdmA] using AdmA_sound c hp
    case held c f g =>
      obtain ⟨w, hw, -⟩ := through_p.mp hp
      simpa [AdmA] using AdmA_sound c hw
    case nullable c =>
      cases hw : (denote c).ownsNull with
      | true =>
        rw [show (denote (.nullable c)).p = (denote c).p from
          withNull_p_of_owns hw] at hp
        simp [AdmA, AdmA_sound c hp]
      | false =>
        rw [show denote (.nullable c) = (denote c).orNull from
          withNull_eq_orNull hw] at hp
        rcases orNull_p.mp hp with ⟨rfl, -⟩ | ⟨-, hc⟩
        · simp [AdmA]
        · simp [AdmA, AdmA_sound c hc]
    case dunion d opts =>
      have h2 := admA_sound _ hp
      have heq : AdmA (.dunion d opts) a = admA (.dunion d opts) a := by rw [AdmA, admA]; rfl
      rw [heq]; exact h2
    case union opts =>
      simp only [denote, optionSems_eq] at hp
      obtain ⟨o, ho, -, hop⟩ := altCodec_p_admits hp
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      rw [optionSemOf_c] at hop
      -- hoisted for the reason the value side gives: the recursive call cannot live inside a
      -- generalisation over an arbitrary list
      have htx' : AdmA tx a = true := AdmA_sound tx hop
      have key : ∀ (ts : List Term), tx ∈ ts → AdmAAny ts a = true := by
        intro ts hts
        induction ts with
        | nil => exact absurd hts (by simp)
        | cons t0 ts ih =>
          rcases List.mem_cons.mp hts with rfl | h'
          · simp [AdmAAny, htx']
          · simp [AdmAAny, ih h']
      simpa [AdmA] using key opts htx

termination_by t _ _ => Term.depth t
decreasing_by term_depth_wf

/-! **Every attribute row is a sound over-approximation, the hatch included** — the
    attribute-side counterpart of `Adm_sound`, and the same obligation for the same reason.

    Exactness for these rows is **not** yet proved; the value side's `Adm_exact` has no
    mirror here. Until it does, `AdmA` carries one obligation where `Adm` carries two, and
    the analysis tables cannot be migrated onto the pair. -/
/-- The converse direction on the attribute side: the row is `dom(p)`, not a bound on it. -/
def ExactA (t : Term) : Prop := ∀ a, AdmA t a = true ↔ ((denote t).p a).isSome

/-- The attribute-side hatch, wider than the value side's by three rows, and the three are
    the asymmetries §1 imposes rather than anything this file chose.

    * `refine` — `q` tests the value a read *produces*; no syntactic set of attributes
      bounds that. This is the row `admA` could never narrow either, and the reason `adm`
      and `admA` are two functions rather than one.
    * `nullable` — `ownsNull` again, and this side is where the disjunction bites first.

    The remaining six are the same shapes the value side excuses. -/
def AnalysableA : Term → Bool
  | .string | .boolean | .binary | .null | .number | .decimal
  | .literal _ _ | .custom _ _ => true
  | .array c | .record c | .held c _ _ | .lazy c | .legacy c _ => AnalysableA c
  | .refine _ _ | .nullable _ | .union _
  | .set _ | .tuple _ _ | .object _ _ _ | .dunion _ _ | .opaq _ => false

/-- `AdmAAll` transported across the entry's exactness. -/
theorem AdmAAll_iff {c : Term} (h : ExactA c) : ∀ as : List Attr,
    AdmAAll c as = true ↔ ∀ a ∈ as, ((denote c).p a).isSome = true := by
  intro as; induction as with
  | nil => simp [AdmAAll]
  | cons a as ih => simp [AdmAAll, ih, h a]

/-- **Fourteen of the twenty-three attribute rows are exact.** Two fewer than the value
    side, and the two are `refine` and `legacy` — the pair whose asymmetry is the reason
    §5 needed `adm` and `admA` rather than one function.

    The numeric rows are the interesting ones: they reach `dom(p)` through `Double.ofDec`,
    which is axiomatized, and are exact anyway — a row may *call* an axiomatized function
    even though no finite set of numerals describes its domain. §5 wrote `⊤` there. -/
theorem AdmA_exact : ∀ (t : Term), AnalysableA t = true → ExactA t
  | .string, _ => by intro a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, stringCodec]
  | .boolean, _ => by intro a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, booleanCodec]
  | .binary, _ => by intro a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, binaryCodec]
  | .null, _ => by intro a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, nullCodec]
  | .number, _ => by
      intro a
      cases a
      case n x =>
        simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, numberCodec]
        cases hx : Double.ofDec x.1 <;> simp [hx]
      all_goals simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, numberCodec]
  | .decimal, _ => by intro a; cases a <;> simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, decimalCodec]
  -- Three rows into one. The `number` base is the only one needing `Double.ofDec`, and it is
  -- also the only one where unfolding `numberCodec` is safe here: the `simp only` fixes the
  -- shape before `Numeral.WF`'s parser can be reached.
  | .literal k ls, _ => by
      intro a
      cases k
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
      case string =>
        cases a <;> simp [AdmALit, denote, denote, literalCodec, baseCodec, Codec.restrict,
                          inL, stringCodec]
      case boolean =>
        cases a <;> simp [AdmALit, denote, denote, literalCodec, baseCodec, Codec.restrict,
                          inL, booleanCodec]
      case binary => exact AdmALit_binary_exact ls a
      case null => exact AdmALit_null_exact ls a
  | .custom ce cp, _ => by intro a; simp [AdmA, denote, denote]
  | .array c, ha => by
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a
      cases a
      case l as =>
        simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec]
        rw [AdmAAll_iff hc, ← traverse_isSome_iff]
        cases traverse (denote c).p as <;> simp
      all_goals simp [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, arrayCodec]
  | .record c, ha => by
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a
      cases a
      case m keys g =>
        simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec, Option.isSome_map', decide_eq_true_eq,
          funImage_isSome_iff]
        exact forall_congr' fun k => hc (g k)
      all_goals simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, recordCodec, Option.map_none',
        Option.isSome_none, Bool.false_eq_true]
  | .held c f g, ha => by
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a
      simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.through]
      rw [hc a]
      cases (denote c).p a <;> simp
  | .lazy c, ha => by
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a; simpa [AdmA, denote] using hc a
  | .legacy c r, ha => by
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a
      simp only [AdmA, denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.extendRead]
      cases hx : (denote c).p a <;> simp [hc a, hx]
  | .refine _ _, ha | .nullable _, ha | .union _, ha
  | .set _, ha | .tuple _ _, ha | .object _ _ _, ha | .dunion _ _, ha
  | .opaq _, ha => by simp [AnalysableA] at ha

/-! ### The attribute side's excuses, and their witnesses

The value side's five reasons apply here too, and two more do — `refine`, which cannot
narrow a read because `q` tests the value a read *produces*, and `legacy`, which widens one
by construction. Those two cover nothing on the value side, which is why `excuse_witnessed`
is stated with the covering as a hypothesis: an excuse must be witnessed **on the side it is
used on**, and neither side has to answer for the other's reasons. -/

/-- `set`'s member gate over-claims on the read side: `AdmA` accepts all three wire
    families, and `set(string)` reads only `SS`. The empty run used to be the witness;
    a numeric run is the one that survives typing, and `Numeral` is `String`, so it needs
    no axiom to construct. -/
theorem not_ExactA_set : ¬ ExactA (.set .string) := by
  intro h
  have h2 := (h (.ns (.of (.of "1") ∅))).mp (by simp [AdmA])
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h2
  replace hv : decSet stringCodec Attr.n (NEFinset.of (WFNumeral.of "1") ∅) = some v := hv
  have := decSet_elem hv (WFNumeral.of "1") (NEFinset.mem_of _ ∅)
  simp [stringCodec] at this

/-- Alignment again, read side. -/
theorem not_ExactA_tuple : ¬ ExactA (.tuple [.string] none) := by
  intro h
  have := (h (.l [.s "a", .s "b"])).mp (by simp [AdmA])
  simp [denote, denote, denoteList, denoteOpt, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, tupleCodec, align, stringCodec] at this

/-- (U) failing, read side: two options admit and `select` reads nothing. -/
theorem not_ExactA_union : ¬ ExactA (.union [.string, .string]) := by
  intro h
  have := (h (.s "a")).mp (by simp [AdmA, AdmAAny])
  simp [denote, denote, optionSems, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, specOf, optionSemOf, altCodec, select,
    stringCodec] at this

/-- `opaq`'s ⊤ over-claims on the read side too, and here the surviving witness needs no
    `Double`: `opaq false` is `refuse`, so it reads no `N` — and therefore no `NS`, whose
    payloads are read through the same option. The empty wire set used to say this; a
    numeric wire set says it now, and `Numeral` is `String`. -/
theorem not_ExactA_opaq : ¬ ExactA (.opaq false) := by
  intro h
  have h2 := (h (.ns (.of (.of "1") ∅))).mp (by simp [AdmA])
  have hd : (denote (Term.opaq false)).p (.ns (.of (.of "1") ∅))
      = (setCodec (opaqCodec 1 false)).p (.ns (.of (.of "1") ∅)) := by
    show (opaqCodecω false).p _ = _
    simp only [opaqCodecω, Attr.depth]
    exact opaqCodec_p_ns false 1 _
  rw [hd] at h2
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h2
  replace hv : decSet (opaqCodec 1 false) Attr.n (NEFinset.of (WFNumeral.of "1") ∅)
      = some v := hv
  have hel := decSet_elem hv (WFNumeral.of "1") (NEFinset.mem_of _ ∅)
  rw [opaqCodec_p_n] at hel
  simp [Codec.empty] at hel

/-- Writes the null point — half of a pair whose write reaches it and whose read does not,
    the mirror of `rNull`, and the reason `nullable` is in both hatches rather than one. -/
def ceNull : Value → Option Attr := fun v => match v with | .null => some .null | _ => none
/-- …and reads nothing at all. -/
def cpNone : Attr → Option Value := fun _ => none

theorem not_ExactA_nullable : ¬ ExactA (.nullable (.custom ceNull cpNone)) := by
  intro h
  have h2 := (h .null).mp (by simp [AdmA])
  simp [denote, denote, Codec.withNull, Codec.ownsNull, ceNull, cpNone] at h2

/-- `refine` cannot narrow a read: `q` refuses everything, and `AdmA` cannot see it. -/
theorem not_ExactA_refine : ¬ ExactA (.refine .string (fun _ => false)) := by
  intro h
  have h2 := (h (.s "a")).mp (by simp [AdmA])
  simp [denote, denote, Codec.restrict, stringCodec] at h2


/-- Which shapes each excuse may be invoked for **on the attribute side**. Two rows have no
    value-side counterpart, and the catch-all answers `false` for the same reason it does
    there: a new constructor is not excusable by default. -/
def Excuse.coversA : Excuse → Term → Bool
  | .opaqueDepth,     .opaq _      => true
  | .uniqueAdmission, .union _     => true
  | .uniqueAdmission, .dunion _ _  => true
  | .payloadShape,    .set _       => true
  | .nameAdmission,   .object _ _ _  => true
  | .nameAdmission,   .tuple _ _   => true
  | .nullOwnership,   .nullable _  => true
  | .valueUnderRead,  .refine _ _  => true
  | _, _ => false

/-- The subterm a propagating **attribute** row inherits from. `refine` and `legacy` are
    absent, which is the whole of the asymmetry: they propagate on the value side and are
    excused here. -/
def inheritsFromA : Term → Option Term
  | .array c | .record c | .held c _ _ | .lazy c | .legacy c _ => some c
  | _ => none

/-- Every attribute row that declines exactness names a covering reason or inherits one. -/
theorem analysableA_excused : ∀ (t : Term), AnalysableA t = false →
    (∃ e : Excuse, e.coversA t = true) ∨ (∃ c, inheritsFromA t = some c ∧ AnalysableA c = false)
  | .opaq _, _      => .inl ⟨.opaqueDepth, rfl⟩
  | .union _, _     => .inl ⟨.uniqueAdmission, rfl⟩
  | .dunion _ _, _  => .inl ⟨.uniqueAdmission, rfl⟩
  | .set _, _       => .inl ⟨.payloadShape, rfl⟩
  | .object _ _ _, _  => .inl ⟨.nameAdmission, rfl⟩
  | .tuple _ _, _   => .inl ⟨.nameAdmission, rfl⟩
  | .nullable _, _  => .inl ⟨.nullOwnership, rfl⟩
  | .refine _ _, _  => .inl ⟨.valueUnderRead, rfl⟩
  | .array c, h | .record c, h | .held c _ _, h | .lazy c, h | .legacy c _, h =>
      .inr ⟨c, rfl, by simpa [AnalysableA] using h⟩
  | .string, h | .boolean, h | .binary, h | .null, h | .number, h | .decimal, h
  | .literal _ _, h | .custom _ _, h => nomatch h

/-- No attribute-side excuse names an exact row. -/
theorem excuseA_shapes (e : Excuse) (t : Term) (h : e.coversA t = true) :
    AnalysableA t = false := by
  cases e <;> cases t <;> simp_all [Excuse.coversA, AnalysableA]

/-- **Every attribute-side excuse is earned**, on the side it is used on. -/
theorem excuseA_witnessed : ∀ (e : Excuse) (t : Term), e.coversA t = true →
    ∃ t' : Term, e.coversA t' = true ∧ ¬ ExactA t'
  | .opaqueDepth, _, _     => ⟨.opaq false, rfl, not_ExactA_opaq⟩
  | .uniqueAdmission, _, _ => ⟨.union [.string, .string], rfl, not_ExactA_union⟩
  | .payloadShape, _, _    => ⟨.set .string, rfl, not_ExactA_set⟩
  | .nameAdmission, _, _   => ⟨.tuple [.string] none, rfl, not_ExactA_tuple⟩
  | .nullOwnership, _, _   => ⟨.nullable (.custom ceNull cpNone), rfl, not_ExactA_nullable⟩
  | .valueUnderRead, _, _  => ⟨.refine .string (fun _ => false), rfl, not_ExactA_refine⟩

/-! ## Re-deriving §5's separations on the pair

`SepV` and `SepA` are what the discharge machinery actually consumes, and they are stated
on `κ`/`adm`/`admA`. Before any of that can move to `Adm`/`AdmA`, two things have to be
true: the joint predicate must be at least as tight as the row it replaces, and every
discharge §5 already has must survive.

`Adm_le_adm` and `AdmA_le_admA` are the first. `sepJV_of_sepV` and `sepJA_of_sepA` are the
second — nothing is lost.

The interesting result is that the two sides do **not** re-derive the same way. On the value
side `κ`'s disjunct is subsumed: `Adm` folds the kind gate into its own rows and
`Adm_kind` proves it lands where `κ` says, so `SepJV` is a single clause. On the attribute
side the member disjunct survives, because `setMember` sends one value kind to three
attribute members and `AdmA`'s `set` row admits all three. `sepJA_needs_member` is the pair
that shows it doing work. -/

/-- `⋁` of `Adm` refines `⋁` of `adm`, option by option. -/
theorem AdmAny_le_admList : ∀ (ts : List Term) (v : Value),
    (∀ t ∈ ts, Adm t v = true → adm t v = true) →
    AdmAny ts v = true → admList ts v = true
  | [], _, _, h => by simp [AdmAny] at h
  | t :: ts, v, hall, h => by
      simp only [AdmAny, Bool.or_eq_true] at h
      simp only [admList, Bool.or_eq_true]
      rcases h with h | h
      · exact Or.inl (hall t (by simp) h)
      · exact Or.inr (AdmAny_le_admList ts v (fun t' ht' => hall t' (by simp [ht'])) h)

/-- **`Adm` refines `adm`.** Every row of the joint predicate is at least as tight as the
    row it replaces, which is what lets every existing discharge carry over unchanged. -/
theorem Adm_le_adm : ∀ (t : Term) (v : Value), Adm t v = true → adm t v = true
  | .string, _, _ => rfl
  | .boolean, _, _ => rfl
  | .binary, _, _ => rfl
  | .null, _, _ => rfl
  | .set _, _, _ => rfl
  | .tuple _ _, _, _ => rfl
  | .object _ _ _, _, _ => rfl
  | .array _, _, _ => rfl
  | .record _, _, _ => rfl
  | .opaq _, _, _ => rfl
  | .number, v, h => by simpa [adm] using (by simpa [Adm] using h : inD v = true)
  | .decimal, v, h => by simpa [adm] using (by simpa [Adm] using h : isStored v = true)
  -- `Adm` is *strictly* stronger at the numeric base: it carries `WF`, which §5's table does
  -- not, so the containment drops a conjunct there rather than being `exact`. At the other
  -- four the two rows are the same predicate — `inL` — which is what one rule makes visible.
  | .literal k ls, v, h => by
      rw [adm]
      rw [Adm_literal] at h
      exact (Bool.and_eq_true _ _ ▸ h : inL k ls v = true ∧ _).1
  | .custom ce cp, v, h => by rw [adm]; rw [Adm] at h; exact h
  | .dunion d opts, v, h => by rw [adm]; rw [Adm] at h; exact h
  | .refine t q, v, h => by
      rw [Adm, Bool.and_eq_true] at h
      rw [adm, Bool.and_eq_true]
      exact ⟨Adm_le_adm t v h.1, h.2⟩
  | .legacy t r, v, h => by
      rw [adm]; exact Adm_le_adm t v (by rw [Adm] at h; exact h)
  | .lazy t, v, h => by
      rw [adm]; exact Adm_le_adm t v (by rw [Adm] at h; exact h)
  | .held t f g, v, h => by
      rw [adm]; exact Adm_le_adm t (f v) (by rw [Adm] at h; exact h)
  | .nullable t, v, h => by
      rw [Adm, Bool.or_eq_true] at h
      rw [adm, Bool.or_eq_true]
      rcases h with h | h
      · exact Or.inl (Adm_le_adm t v h)
      · exact Or.inr h
  | .union opts, v, h => by
      rw [adm]
      exact AdmAny_le_admList opts v (fun t' _ => Adm_le_adm t' v) (by rw [Adm] at h; exact h)


/-- …and lands in `⋃ κ`, which is what `union`'s kind row claims. -/
theorem AdmAny_kind : ∀ (ts : List Term) (ks : List Kind) (v : Value),
    κList ts = some ks →
    (∀ t ∈ ts, ∀ ks', κ t = some ks' → Adm t v = true → v.kind ∈ ks') →
    AdmAny ts v = true → v.kind ∈ ks
  | [], _, _, _, _, h => by simp [AdmAny] at h
  | t :: ts, ks, v, hk, hall, h => by
      simp only [AdmAny, Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨ks', hks', hsub⟩ := κList_mem hk t (by simp)
        exact hsub _ (hall t (by simp) ks' hks' h)
      · have : ∀ t' ∈ ts, ∀ ks', κ t' = some ks' → Adm t' v = true → v.kind ∈ ks' :=
          fun t' ht' => hall t' (by simp [ht'])
        replace hk : (match κ t, κList ts with
          | some k0, some k1 => some (k0 ++ k1) | _, _ => none) = some ks := hk
        cases h0 : κ t with
        | none => rw [h0] at hk; exact nomatch hk
        | some k0 =>
          cases h1 : κList ts with
          | none => rw [h0, h1] at hk; exact nomatch hk
          | some k1 =>
            rw [h0, h1] at hk
            have hks : ks = k0 ++ k1 := by simpa using hk.symm
            subst hks
            exact List.mem_append.mpr (Or.inr (AdmAny_kind ts k1 v h1 this h))

/-- **`Adm` lands in `κ`.** Wherever `κ` names a kind list at all, an `Adm`-admitted value
    has one of those kinds — so the kind gate `Adm` folds in really is `κ`'s, and `SepV`'s
    first disjunct is subsumed by its second. -/
theorem Adm_kind : ∀ (t : Term) (ks : List Kind) (v : Value),
    κ t = some ks → Adm t v = true → v.kind ∈ ks
  | .string, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .boolean, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .binary, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .null, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .number, _, v, rfl, h => by cases v <;> simp_all [Adm, inD, Value.kind]
  | .decimal, _, v, rfl, h => by cases v <;> simp_all [Adm, isStored, Value.kind]
  | .literal k _, _, v, rfl, h => by
      cases k <;> cases v <;> simp_all [Adm_literal, AdmLit, inL, Value.kind]
  | .set _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .array _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .tuple _ _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .record _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .object _ _ _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .dunion _ _, _, v, rfl, h => by cases v <;> simp_all [Adm, tagOfV, Value.kind]
  | .refine t q, ks, v, hk, h => by
      rw [Adm, Bool.and_eq_true] at h
      exact Adm_kind t ks v (by rw [κ] at hk; exact hk) h.1
  | .legacy t r, ks, v, hk, h => by
      exact Adm_kind t ks v (by rw [κ] at hk; exact hk) (by rw [Adm] at h; exact h)
  | .lazy t, ks, v, hk, h => by
      exact Adm_kind t ks v (by rw [κ] at hk; exact hk) (by rw [Adm] at h; exact h)
  | .nullable t, ks, v, hk, h => by
      rw [κ] at hk
      obtain ⟨ks', hks', rfl⟩ := Option.map_eq_some'.mp hk
      rw [Adm, Bool.or_eq_true] at h
      rcases h with h | h
      · exact List.mem_cons_of_mem _ (Adm_kind t ks' v hks' h)
      · cases v <;> simp_all [Value.kind]
  | .union opts, ks, v, hk, h => by
      exact AdmAny_kind opts ks v (by rw [κ] at hk; exact hk)
        (fun t' _ ks' hk' h' => Adm_kind t' ks' v hk' h') (by rw [Adm] at h; exact h)
  | .held _ _ _, ks, v, hk, h => by rw [κ] at hk; exact nomatch hk
  | .custom _ _, ks, v, hk, h => by rw [κ] at hk; exact nomatch hk
  | .opaq _, ks, v, hk, h => by rw [κ] at hk; exact nomatch hk


/-- `⋁` of `AdmA` refines `⋁` of `admA`. -/
theorem AdmAAny_le_admAList : ∀ (ts : List Term) (a : Attr),
    (∀ t ∈ ts, AdmA t a = true → admA t a = true) →
    AdmAAny ts a = true → admAList ts a = true
  | [], _, _, h => by simp [AdmAAny] at h
  | t :: ts, a, hall, h => by
      simp only [AdmAAny, Bool.or_eq_true] at h
      simp only [admAList, Bool.or_eq_true]
      rcases h with h | h
      · exact Or.inl (hall t (by simp) h)
      · exact Or.inr (AdmAAny_le_admAList ts a (fun t' ht' => hall t' (by simp [ht'])) h)

/-- **`AdmA` refines `admA`**, the attribute-side counterpart of `Adm_le_adm`. -/
theorem AdmA_le_admA : ∀ (t : Term) (a : Attr), AdmA t a = true → admA t a = true
  | .string, _, _ => rfl
  | .boolean, _, _ => rfl
  | .binary, _, _ => rfl
  | .null, _, _ => rfl
  | .number, _, _ => rfl
  | .set _, _, _ => rfl
  | .tuple _ _, _, _ => rfl
  | .object _ _ _, _, _ => rfl
  | .array _, _, _ => rfl
  | .record _, _, _ => rfl
  | .legacy _ _, _, _ => rfl
  | .opaq _, _, _ => rfl
  | .custom _ _, a, h => by rw [admA]; rw [AdmA] at h; exact h
  | .decimal, a, h => by rw [admA]; rw [AdmA] at h; exact h
  | .dunion _ _, a, h => by rw [admA]; rw [AdmA] at h; exact h
  | .literal k ls, a, h => by
      cases k <;> cases a <;> simp_all [AdmA_literal, AdmALit, admA, admALit]
  | .refine t _, a, h => by
      rw [admA]; exact AdmA_le_admA t a (by rw [AdmA] at h; exact h)
  | .held t _ _, a, h => by
      rw [admA]; exact AdmA_le_admA t a (by rw [AdmA] at h; exact h)
  | .lazy t, a, h => by
      rw [admA]; exact AdmA_le_admA t a (by rw [AdmA] at h; exact h)
  | .nullable t, a, h => by
      rw [AdmA, Bool.or_eq_true] at h
      rw [admA, Bool.or_eq_true]
      rcases h with h | h
      · exact Or.inl (AdmA_le_admA t a h)
      · exact Or.inr h
  | .union opts, a, h => by
      rw [admA]
      exact AdmAAny_le_admAList opts a (fun t' _ => AdmA_le_admA t' a)
        (by rw [AdmA] at h; exact h)

/-- **Separation on the joint predicate, value side — one clause.** §5's `SepV` offers a
    choice between disjoint kinds and disjoint admissible sets; `Adm` carries the kind gate
    in its own rows, so the first disjunct is subsumed (`Adm_kind`) and the definition
    collapses. -/
def SepJV (x y : Term) : Prop := ∀ v, Adm x v = true → Adm y v = false

/-- **…and attribute side, which does *not* collapse.** The member disjunct stays, because
    `AdmA` does not bound `μSyn`: a `set` row admits all three wire-set members whatever its
    element term is, so two sets differing only in element member are separated by `μSyn`
    and not by `AdmA` (`sepJA_needs_member`). The asymmetry is `setMember`'s — one value
    kind, three attribute members — and it is why this side keeps two clauses. -/
def SepJA (x y : Term) : Prop :=
  (∃ μx μy, μSyn x = some μx ∧ μSyn y = some μy ∧ μx ≠ μy) ∨
  (∀ a, AdmA x a = true → AdmA y a = false)

/-- **Every §5 value-side discharge carries over**, from either disjunct. -/
theorem sepJV_of_sepV {x y : Term} (h : SepV x y) : SepJV x y := by
  intro v hv
  cases hy : Adm y v with
  | false => rfl
  | true =>
    exfalso
    rcases h with ⟨kx, ky, hkx, hky, hdisj⟩ | hd
    · exact hdisj _ (Adm_kind x kx v hkx hv) (Adm_kind y ky v hky hy)
    · have := hd v (Adm_le_adm x v hv)
      rw [Adm_le_adm y v hy] at this
      exact absurd this (by simp)

/-- …and every attribute-side one. -/
theorem sepJA_of_sepA {x y : Term} (h : SepA x y) : SepJA x y := by
  rcases h with hμ | hd
  · exact Or.inl hμ
  · refine Or.inr fun a ha => ?_
    cases hy : AdmA y a with
    | false => rfl
    | true =>
      exfalso
      have := hd a (AdmA_le_admA x a ha)
      rw [AdmA_le_admA y a hy] at this
      exact absurd this (by simp)

/-- The member disjunct is load-bearing: `set(string)` and `set(number)` differ in `μSyn`
    and are indistinguishable to `AdmA`, which admits `NS` at both. -/
theorem sepJA_needs_member :
    ¬ (∀ a, AdmA (.set .string) a = true → AdmA (.set .number) a = false) := by
  intro h
  exact absurd (h (.ns (.of (.of "1") ∅)) (by simp [AdmA])) (by simp [AdmA])

/-! ## `ident`, and why the pair does not replace it

`ident` is §5's third auxiliary: *the term decides its own membership*. The question the
migration has to answer is whether the joint predicate subsumes it. It does not, and the
reason is worth stating precisely, because it is the one place where `Adm` carries **less**
than the three functions it replaces.

`ident` is not a function of `Adm` — nor of `adm`. `string` and `refine(string, ⊤)` denote
the same pair, have the same `Adm` and the same `adm`, and differ in `ident`, which is
`false` for the bare base and `true` for any `refine`. `ident` is a fact about *how a term
is written*, not about which values it admits, and no predicate on values can recover it.

That is not a gap, because nothing consumes it. `ident` appears in no discharge: none of the
seventeen `uAtCan_*` theorems mentions it. What it does is carry §5's **(K)** — the rule
that was stated as `κ(cᵢ) ∩ κ(cⱼ) = ∅ ∨ ident(cᵢ) ∨ ident(cⱼ)`, found unsound, and replaced
by `SepV`. `ident_of_adm` pins it, `admDisj_ident` recovers the repaired form, and
`not_uAtCan_literal_string` / the two-sided refutation record why the withdrawn form was
wrong.

So `ident` stays where it is, defined on `adm`, and `adm` stays with it. The pair supersedes
`κ`/`adm`/`admA` **for the discharge**; it does not supersede the transcription of §5, and
deleting that would delete the record of what §5 got wrong. -/

/-- A refinement by the trivially-true predicate: same pair, same `Adm`, different `ident`. -/
def qTop : Value → Bool := fun _ => true

/-- The two terms agree on the joint predicate… -/
theorem Adm_string_eq_refine : Adm .string = Adm (.refine .string qTop) := by
  funext v; simp [Adm, qTop]

/-- …and disagree on `ident`. -/
theorem ident_string_ne_refine :
    ident .string ≠ ident (.refine .string qTop) := by
  simp [ident]

/-- **`ident` is not a function of `Adm`.** Two terms with the *same* joint predicate and
    different `ident`, so no definition on the pair can recover it. -/
theorem ident_not_determined_by_Adm :
    ∃ x y : Term, Adm x = Adm y ∧ ident x ≠ ident y :=
  ⟨.string, .refine .string qTop, Adm_string_eq_refine, ident_string_ne_refine⟩

/-- They agree on `adm` too, so this is not an artefact of folding in the kind gate. -/
theorem adm_string_eq_refine : adm .string = adm (.refine .string qTop) := by
  funext v; simp [adm, qTop]

/-- …so `ident` is not a function of `adm` either, by the same pair. -/
theorem ident_not_determined_by_adm :
    ∃ x y : Term, adm x = adm y ∧ ident x ≠ ident y :=
  ⟨.string, .refine .string qTop, adm_string_eq_refine, ident_string_ne_refine⟩

/-- **`SepJV` suffices for the discharge.** This is what "nothing is lost" means: the joint
    predicate is tighter than the rows it replaces, so `SepJV` is a *weaker* statement — but
    `Adm_sound` connects it straight to the denotation, and that is all the discharge needs.
    Where `x` writes, `y` refuses. -/
theorem admitV_of_sepJV {x y : Term} (h : SepJV x y) (v : Value) (a : Attr)
    (hx : (denote x).e v = some a) : ((denote y).e v).isSome = false := by
  have hAx : Adm x v = true := Adm_sound x hx
  have hAy : Adm y v = false := h v hAx
  cases hy : (denote y).e v with
  | none => rfl
  | some b => exact absurd (Adm_sound y hy) (by simp [hAy])

/-- …and on the attribute side, from `SepJA`'s second disjunct. -/
theorem admitA_of_sepJA {x y : Term} (h : ∀ a, AdmA x a = true → AdmA y a = false)
    (a : Attr) (v : Value) (hx : (denote x).p a = some v) :
    ((denote y).p a).isSome = false := by
  have hAx : AdmA x a = true := AdmA_sound x hx
  have hAy : AdmA y a = false := h a hAx
  cases hy : (denote y).p a with
  | none => rfl
  | some w => exact absurd (AdmA_sound y hy) (by simp [hAy])

/-! ### `ident`, pinned from below

The section above concluded that `ident` cannot be recovered from the pair and should
therefore be left alone. That was the wrong conclusion from a correct observation. `ident`
is a table like the other three, it had never been pinned from below either, and the reason
it resists the pair is not that it carries something the pair lacks — it is that it carries
something **nothing** justifies.

`Decides` below is the semantic notion §5's prose describes: two values of the same kind,
one written and one refused, so that the kind does not settle admission and an admission is
therefore evidence. Against it, `ident` is neither an over- nor an under-approximation:

* **Too generous.** `refine(string, ⊤)` is `ident` and decides nothing — `q` is checked on
  both halves and always passes. `ident` cannot see this, because it never looks at `q`.
* **Too stingy.** `object` with a required field refuses the empty map and writes a
  populated one, which is deciding by any reading, and `ident` calls it `false`.

And the `refine` row is not an oversight but an artifact: `ident (refine t q) = true`
unconditionally is what makes `ident_of_adm` go through, since `adm (refine t q)` can refuse
on `q` alone while `ident t` is `false`. The row exists to satisfy the pinning lemma, not
because refinements decide.

`ident` cannot be made exact — whether an arbitrary `q : Value → Bool` narrows anything is
not a syntactic question. What it can be is *honest about which side it errs on*, and at
present it errs on both. Nothing live depends on it: no `uAtCan_*` consumes it, and
`admDisj_ident` derives it rather than assuming it. -/

/-- **What "decides its own membership" actually says.** Two values of the *same kind*, one
    written and one refused: the kind does not settle admission, so an admission is
    evidence. This is the content §5's `ident` gestures at, stated on the denotation. -/
def Decides (t : Term) : Prop :=
  ∃ v w, ((denote t).e v).isSome = true ∧ v.kind = w.kind ∧ ((denote t).e w).isSome = false

/-- `literalS` decides, as §5 says. -/
theorem decides_literalS : Decides (.literal .string (.of "A" ∅)) :=
  ⟨.str "A", .str "B",
   by simp [denote, denote, literalCodec, baseCodec, Codec.restrict, inL, stringCodec,
         NEFinset.of],
   rfl,
   by simp [denote, denote, literalCodec, baseCodec, Codec.restrict, inL, stringCodec,
         NEFinset.of]⟩

/-- `string` does not, as §5 also says. -/
theorem not_decides_string : ¬ Decides .string := by
  rintro ⟨v, w, hv, hk, hw⟩
  simp only [denote, denote] at hv hw
  cases v <;> cases w <;> simp_all [denote, stringCodec, Value.kind]

/-- **`ident` is too generous.** A refinement by the trivially-true predicate is `ident`,
    and decides nothing: `q` is checked on both halves and always passes, so admission is
    no evidence at all. `ident` cannot see this, because it does not look at `q`. -/
theorem ident_refine_top : ident (.refine .string qTop) = true := rfl

theorem not_decides_refine_top : ¬ Decides (.refine .string qTop) := by
  rintro ⟨v, w, hv, hk, hw⟩
  simp only [denote, denote] at hv hw
  cases v <;> cases w <;>
    simp_all [denote, Codec.restrict, stringCodec, qTop, Value.kind]

/-- **And too stingy.** An object with a required field refuses the empty map and writes a
    populated one — two `map`s differing in admission — while `ident` calls it `false`. -/
theorem decides_object :
    Decides (.object {"k"} (fun _ => .req .string) .refuse) := by
  refine ⟨.map {"k"} (fun _ => .str "a"),
          .map ∅ (fun k => absurd k.2 (Finset.not_mem_empty k.1)), ?_, rfl, ?_⟩
  · simp [denote, denote, fieldTable, restSem, fieldSem, restSem,
          objectCodec, objectCodecCore, stringCodec,
          valPresentB, valPresentAt, fieldSem, rcOf, FieldSem.codec, carriedCodec,
          mapV, mA, Ctor.out, Ctor.into, objWrite, entryCodec, MapOf.at, funImage,
          Subtype.forall]
  · simp [denote, denote, fieldTable, restSem, fieldSem, restSem,
          objectCodec, objectCodecCore, stringCodec,
          valPresentB, valPresentAt, fieldSem, rcOf, FieldSem.codec, carriedCodec,
          mapV, mA, Ctor.out, Ctor.into, objWrite, MapOf.at, Subtype.forall]

theorem ident_object : ident (.object {"k"} (fun _ => .req .string) .refuse) = false := rfl

/-! ### …and the two errors are the same combinator

`refine` and `held` are not unrelated rows that happen to be wrong in opposite directions.
They are **one combinator with two adapters**: `Codec.adapt` generalises both, `held` taking
the total `some ∘ f` (`through_e_adapt`) and `refine` the partial identity `partialId q`
(`restrict_e_adapt`). The doc says as much — "the *same* combinator, weaker adapter".

`ident` gives them opposite rows. `refine` is `true` unconditionally; `held` propagates.
So the over-claim and the under-claim are the same mistake seen from two sides, and the
witnesses are duals:

* `refine(string, ⊤)` — the adapter narrows nothing, and `ident` says it decides.
* `held(string, fSplit, _)` — the adapter narrows to one string, and `ident` says it does
  not.

`Adm` has no such split. `Adm_refine_adapt` and `Adm_held_adapt` show it doing the one
thing `adapt` describes on both rows — apply the adapter, then ask the subterm — which is
why it carries `q` and `f` where `ident` carries neither. -/

/-- An adapter that sends one string to itself and everything else off `string`'s carrier.
    Total, so this is a `held` and not a `refine` — and it narrows exactly as a refinement
    would. -/
def fSplit : Value → Value := fun v => match v with | .str "A" => .str "A" | _ => .bool true

/-- **The dual gap.** `held(string, fSplit, _)` writes `"A"` and refuses `"B"` — two values
    of one kind, differing in admission — so it decides. `ident` says `false`. -/
theorem decides_held : Decides (.held .string fSplit (fun v => v)) := by
  refine ⟨.str "A", .str "B", ?_, rfl, ?_⟩
  · simp [denote, denote, Codec.through, stringCodec, fSplit]
  · simp [denote, denote, Codec.through, stringCodec, fSplit]

theorem ident_held_false : ident (.held .string fSplit (fun v => v)) = false := rfl

/-- `Adm` treats the two adapters uniformly: apply it, then ask the subterm. -/
theorem Adm_refine_adapt (t : Term) (q : Value → Bool) (v : Value) :
    Adm (.refine t q) v = ((partialId q v).elim false (Adm t)) := by
  cases hq : q v <;> simp [Adm, partialId, hq]

theorem Adm_held_adapt (t : Term) (f g : Value → Value) (v : Value) :
    Adm (.held t f g) v = ((some (f v)).elim false (Adm t)) := by
  simp [Adm]

/-! ### Adapters and alternatives, and why `legacy` was in the wrong family

`held` and `refine` are `Codec.adapt` with different adapters. `legacy` is **not** an
adapter at all, and asking whether it was is what found the row above.

An adapter *composes*: `adapt`'s read is `(c.p a).bind g`, so it can only lose attributes —
`adapt_p_le`. `legacy`'s read *gains* them: `extendRead`'s `p` is the subterm's channel
falling back to `r`'s, which is a **choice**, not a composition. That is the family
`nullable` belongs to as well (`orNull` adjoins the null point on both sides) and `union`
(`altCodec`, n-ary, both sides). `legacy` is the one-sided member: it reads on two channels
and writes on one.

Placing it correctly is what makes the row exact. §5 called `admA(legacy)` `⊤` because
`extendRead` widens past the subterm's set — true, and the wrong conclusion, because the
thing it widens *by* is `r`, which the term carries. The domain is
`dom(p) ∪ dom(r)`, both halves named, and `AdmA` can apply `r` for the same reason it can
apply `held`'s `f` and `custom`'s `cp`.

So `legacy` leaves the attribute hatch, and the `widenedRead` excuse is deleted rather than
witnessed: it was covering a row that did not need excusing. What survives untouched is
`not_admA_legacy` — §5's *passthrough* really is unsound, and the union is not the
passthrough. -/

/-- An adapter never widens the read domain. -/
theorem adapt_p_le {c : Codec} {f g : Value → Option Value} {a : Attr} :
    ((c.adapt f g).p a).isSome = true → (c.p a).isSome = true := by
  intro h
  simp only [Codec.adapt] at h
  cases hc : c.p a with
  | none => rw [hc] at h; simp at h
  | some _ => rfl

/-- `legacy` is the read-side alternative: the subterm's channel, falling back to `r`'s. -/
theorem legacy_p_alt (t : Term) (r : Attr → Option Value) (a : Attr) :
    (denote (.legacy t r)).p a
      = (match (denote t).p a with | some v => some v | none => r a) := rfl

/-- …so its read domain is the union of the two channels, and both are named. -/
theorem legacy_p_isSome (t : Term) (r : Attr → Option Value) (a : Attr) :
    ((denote (.legacy t r)).p a).isSome = (((denote t).p a).isSome || (r a).isSome) := by
  simp only [legacy_p_alt]
  cases (denote t).p a <;> simp

/-- Which is exactly `AdmA`'s row, so `legacy` widens the read side and is exact anyway. -/
theorem AdmA_legacy_union (t : Term) (r : Attr → Option Value) (a : Attr) :
    AdmA (.legacy t r) a = (AdmA t a || (r a).isSome) := by
  simp [AdmA]

/-- **A discharge §5 could not state.** Two sets over disjoint literals separate, because
    `℘⁺fin` has no empty inhabitant and so the two options share none. The non-emptiness
    is now the *type's*, which is why every branch here ends at `S.2`. -/
theorem sepJV_set_literals :
    SepJV (.set (.literal .string (.of "A" ∅))) (.set (.literal .string (.of "B" ∅))) := by
  intro v hv
  cases v
  case strSet S =>
    simp only [Adm, decide_eq_true_eq] at hv ⊢
    obtain ⟨x, hx⟩ := S.2
    simp only [decide_eq_false_iff_not]
    refine fun hall' => ?_
    have h1 := hv x hx
    have h2 := hall' x hx
    simp [Adm_literal, AdmLit, inL, NEFinset.of] at h1 h2
    exact absurd (h1.symm.trans h2) (by decide)
  all_goals
    first
      | (rename_i S
         simp only [Adm, decide_eq_true_eq] at hv
         obtain ⟨x, hx⟩ := S.2
         exact absurd (hv x hx) (by simp [Adm_literal, AdmLit, inL, NEFinset.of]))
      | simp [Adm] at hv

/-- …and the contrast that shows what the non-emptiness is doing: the *array* pair does not
    separate, because both options admit `[]`. This is §5's empty-container argument in its
    correct scope — it is a fact about `array`, `record` and `object`, not about `set`. -/
theorem not_sepJV_array_literals :
    ¬ SepJV (.array (.literal .string (.of "A" ∅))) (.array (.literal .string (.of "B" ∅))) := by
  intro h
  exact absurd (h (.arr []) (by simp [Adm, AdmAll])) (by simp [Adm, AdmAll])

/-! ### What `set` is, structurally — and the defect that closed

Three readings were worth separating. Two were right and the third found a defect; the
defect is now fixed by the type, and these are the witnesses that it is.

**Not a `union`.** A union is a choice among *codecs*, resolved by (U); a set's elements all
go through **one** codec, so no uniqueness obligation arises. That is why `set` needs no (U)
and `union` does.

**Not `array` with a wrapper either, any more.** It was, while both were lists: the two
shared `traverse c.e vs` and differed only in how the payload list was presented. With the
sets typed there is no shared list to share — `array` traverses a `List Value`, `set` images
a `Finset` — and what survives of the old observation is that the *element* codec is the
same in both.

**And "order does not matter" is now true of the model**, where it was not. §1 types `SS` as
`℘⁺fin(String)` and the reference says the order of a set's values is not preserved and each
value is unique. Three theorems recorded that the model disagreed. They are replaced by the
three below, which say the disagreement is over: an ordering is not a distinction a `Finset`
can make, and a repeat is not an inhabitant it can hold. -/

/-- Two "orderings" of one set are the same value — there is nothing to quotient. -/
theorem set_order_irrelevant :
    (Value.strSet (.of "a" {"b"})) = (Value.strSet (.of "b" {"a"})) :=
  congrArg Value.strSet (Subtype.ext (Finset.ext fun x => by
    simp only [NEFinset.of, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e),
           fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e)⟩))

/-- …and the same attribute. -/
theorem wireSet_order_irrelevant :
    (Attr.ss (.of "a" {"b"})) = (Attr.ss (.of "b" {"a"})) :=
  congrArg Attr.ss (Subtype.ext (Finset.ext fun x => by
    simp only [NEFinset.of, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e),
           fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e)⟩))

/-- A repeat is not an inhabitant: `℘⁺fin` has no multiplicities, and neither does the
    model now. -/
theorem set_no_duplicates :
    (Value.strSet (.of "a" {"a"})) = (Value.strSet (.of "a" ∅)) :=
  congrArg Value.strSet (Subtype.ext (Finset.ext fun x => by
    simp only [NEFinset.of, Finset.mem_insert, Finset.mem_singleton,
      Finset.not_mem_empty, or_false]
    exact ⟨fun h => h.elim id id, fun h => Or.inl h⟩))

/-! ### What (R) would have forced, had the type not settled it

The repair was once going to be a canonical form over lists, and (R) constrained it hard:
retraction is to the *same* value, not an agreeing one, so a codec whose `e` collapsed two
orderings would owe one attribute two readings. `e` could not normalise; it would have had
to accept exactly one representative per set and refuse the rest, with `p` normalising so
that `ker p` collapsed the orderings — §2's sentence, made true by construction.

None of that is needed. `Finset` has one representative per set *as a type*, so there is
nothing for `e` to choose between and nothing for `p` to collapse; `ker p` is equality at
`setCodec` and that is now correct rather than a defect. The constraint is recorded because
it is what rules out the alternative design, not because anything here depends on it.

`Calculus/WireOrder.lean` — the canonical form and the axiom-free order it was built on — was
likewise no longer on the set path, and has been deleted; the `Classical.choice` hazard it
existed to route around is recorded beside `NEFinset` in `Domain.lean`. Nor, as the next section shows, on the map path: the
quotient the kernel refuses is `Finset (Name × Attr)`, and `M` does not need it. -/

/-! ### The reference, checked against the model

`docs/dynamo-datatypes.md` is the official datatype reference. Most of §1 survives it
exactly — `Numeral.WF`'s 38 digits and `-130 … 125` exponent range are the documented
bounds; binary compares unsigned; empty strings and empty binary are permitted, empty lists
and maps are permitted, empty sets are not, and the model already refuses the last.

Two things do not survive, and they are the same defect at two members.

**`SS`/`NS`/`BS`** — *"Each value within a set must be unique. The order of the values within
a set is not preserved."* Recorded above.

**`M`** — *"A map type attribute can store an **unordered** collection of name-value
pairs."* The model's `M` was a `List (Name × Attr)`, so two orderings of one map were two
attributes and a repeated key was writable, which no map has. Three theorems recorded the
disagreement; they are replaced by the three below.

This one was called sharper than the set case for two reasons, and only the first survives.
The model does *state* the intent elsewhere — `Agree` at `M` compares by key and ignores
order — so the two halves of the model disagreed with each other and not merely with the
reference. But the second reason, that maps cannot be repaired by typing, was wrong, and the
correction is the content of this section. `Finset (Name × Attr)` **is** rejected by the
kernel, exactly as `Finset Value` is, the element type being the one under declaration. What
does not follow is that `M` needs the well-formedness route. The pair need not be the
element: §1's `M` is a finite *partial function*, so the names go in a `Finset` over the
concrete type `Name` and the attributes go in a function's codomain — a strictly positive
position, which the kernel accepts:

    | m (keys : Finset Name) (f : {k // k ∈ keys} → Attr)

Unordered, unique-keyed and total-on-its-keys are now facts about the type. No canonical
order, no `Wire.canon`, and nothing for `e` to choose between. -/

/-- Two "orderings" of one map's names are one name set — there is nothing to quotient. -/
theorem mapKeys_order_irrelevant : ({"a", "b"} : Finset Name) = {"b", "a"} :=
  Finset.ext fun x => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e),
           fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e)⟩

/-- …so the codec has one answer where it used to have two. Equal key sets and
    pointwise-equal entries are one attribute (`MapOf.ext`), and one attribute is one
    reading — the order-sensitivity had nowhere left to live. -/
theorem record_p_order_irrelevant
    (g : {k // k ∈ ({"a", "b"} : Finset Name)} → Attr)
    (g' : {k // k ∈ ({"b", "a"} : Finset Name)} → Attr)
    (h : ∀ k (h₁ : k ∈ ({"a", "b"} : Finset Name)) (h₂ : k ∈ ({"b", "a"} : Finset Name)),
      g ⟨k, h₁⟩ = g' ⟨k, h₂⟩) :
    (recordCodec stringCodec).p (.m {"a", "b"} g)
      = (recordCodec stringCodec).p (.m {"b", "a"} g') :=
  congrArg (fun p : MapOf Attr => (recordCodec stringCodec).p (.m p.1 p.2))
    (MapOf.ext (p := ⟨{"a", "b"}, g⟩) (q := ⟨{"b", "a"}, g'⟩) mapKeys_order_irrelevant h)

/-- A repeated key is not an inhabitant: the map that was supposed to carry `"a"` twice is
    the map that carries it once. -/
theorem mapKeys_no_duplicates : ({"a", "a"} : Finset Name) = {"a"} :=
  Finset.ext fun x => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim id id, fun h => Or.inr h⟩

end
end Calculus
