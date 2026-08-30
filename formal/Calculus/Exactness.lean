import Calculus.Discharge
import Calculus.Soundnessω

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
  | .literalS ls => fun v => match v with | .str s => s ∈ ls | _ => false
  | .literalN ls => fun v => match v with | .num d => d ∈ ls | _ => false
  | .literal w => fun v =>
      match w, v with
      | .str s, .str s'   => decide (s' = s)
      | .num d, .num d'   => decide (d' = d)
      | .bool b, .bool b' => decide (b' = b)
      | .bin b, .bin b'   => decide (b' = b)
      | .null, .null      => true
      | _, _              => false
  | .custom ce _ => fun v => (ce v).isSome
  | .array c  => fun v => match v with | .arr xs => AdmAll c xs | _ => false
  | .record c => fun v => match v with | .map kvs => AdmAllSnd c kvs | _ => false
  | .refine t q => fun v => Adm t v && q v
  | .legacy t _ => Adm t
  | .lazy t     => Adm t
  | .held t f _ => fun v => Adm t (f v)
  | .nullable t => fun v => Adm t v || (match v with | .null => true | _ => false)
  | .union opts => fun v => AdmAny opts v
  | .set _      => fun v => match v with | .set _ => true | _ => false
  | .tuple _ _  => fun v => match v with | .arr _ => true | _ => false
  | .object _ _ => fun v => match v with | .map _ => true | _ => false
  | .dunion d opts => fun v =>
      match v with
      | .map kvs =>
        match kvs.lookup d with
        | some (.str tag) => (allTags d opts).contains tag
        | _ => false
      | _ => false
  | .opaq _ => fun _ => true

/-- `⋀` of `Adm` over a container's elements. -/
noncomputable def AdmAll : Term → List Value → Bool
  | _, [] => true
  | c, x :: xs => Adm c x && AdmAll c xs

/-- …and over a record's entry values, the names being carried past unexamined. -/
noncomputable def AdmAllSnd : Term → List (Name × Value) → Bool
  | _, [] => true
  | c, kv :: kvs => Adm c kv.2 && AdmAllSnd c kvs

/-- `⋁` of `Adm` over a union's options. Sound, but *not* exact — `select` demands
    exactly one admitting option, so a union is exact only under (U). -/
noncomputable def AdmAny : List Term → Value → Bool
  | [], _ => false
  | t :: ts, v => Adm t v || AdmAny ts v

end

/-- §5's converse direction: the row is `dom(e)`, not merely a bound on it. -/
def ExactV (t : Term) : Prop := ∀ v, Adm t v = true ↔ ((denoteω t).e v).isSome

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
  | .literalS _ | .literalN _ | .literal _ | .custom _ _ => true
  | .array c | .record c | .refine c _ | .legacy c _ | .lazy c
  | .held c _ _ => Analysable c
  | .opaq _ | .object _ _ | .tuple _ _ | .set _ | .dunion _ _ | .union _
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
    AdmAll c xs = true ↔ ∀ x ∈ xs, ((denoteω c).e x).isSome = true := by
  intro xs; induction xs with
  | nil => simp [AdmAll]
  | cons x xs ih => simp [AdmAll, ih, h x]

/-- …and `AdmAllSnd`. -/
theorem AdmAllSnd_iff {c : Term} (h : ExactV c) : ∀ kvs : List (Name × Value),
    AdmAllSnd c kvs = true ↔ ∀ kv ∈ kvs, ((denoteω c).e kv.2).isSome = true := by
  intro kvs; induction kvs with
  | nil => simp [AdmAllSnd]
  | cons kv kvs ih => simp [AdmAllSnd, ih, h kv.2]

/-- **Sixteen of the twenty-three rows are exact.** Not a bound on `dom(e)` — `dom(e)`.

    The `held` case is the one worth reading: it appeals to the subterm at `f v`, which is
    the pullback, and it is one line because `(c.through f g).e v = c.e (f v)` holds by
    `Iff.rfl`. The `array` and `record` cases are the repair of §5's container rows. -/
theorem Adm_exact : ∀ (t : Term), Analysable t = true → ExactV t
  | .string, _ => by intro v; cases v <;> simp [Adm, denoteω, stringCodec]
  | .boolean, _ => by intro v; cases v <;> simp [Adm, denoteω, booleanCodec]
  | .binary, _ => by intro v; cases v <;> simp [Adm, denoteω, binaryCodec]
  | .null, _ => by intro v; cases v <;> simp [Adm, denoteω, nullCodec]
  | .number, _ => by intro v; cases v <;> simp [Adm, denoteω, numberCodec, inD]
  | .decimal, _ => by intro v; cases v <;> simp [Adm, denoteω, decimalCodec, isStored]
  | .literalS ls, _ => by intro v; cases v <;> simp [Adm, denoteω, literalSCodec]
  | .literalN ls, _ => by intro v; cases v <;> simp [Adm, denoteω, literalNCodec]
  | .literal w, _ => by
      intro v
      cases w <;> cases v <;>
        simp [Adm, denoteω, literalCodec, Codec.restrict, stringCodec, rawNumberCodec,
              booleanCodec, binaryCodec, nullCodec, Codec.empty]
  | .custom ce cp, _ => by intro v; simp [Adm, denoteω]
  | .array c, ha => by
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v
      cases v
      case arr xs =>
        simp only [Adm, denoteω, arrayCodec, Option.isSome_map]
        rw [AdmAll_iff hc, ← traverse_isSome_iff]
        cases traverse (denoteω c).e xs <;> simp
      all_goals simp [Adm, denoteω, arrayCodec]
  | .record c, ha => by
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v
      cases v
      case map kvs =>
        simp only [Adm, denoteω, recordCodec, Option.isSome_map]
        rw [AdmAllSnd_iff hc]
        have hkey : (∀ kv ∈ kvs, ((denoteω c).e kv.2).isSome = true)
                  ↔ (∀ kv ∈ kvs, (encPair (denoteω c) kv).isSome = true) :=
          ⟨fun hall kv hkv => by simpa [encPair] using hall kv hkv,
           fun hall kv hkv => by simpa [encPair] using hall kv hkv⟩
        rw [hkey, ← traverse_isSome_iff]
        cases traverse (encPair (denoteω c)) kvs <;> simp
      all_goals simp [Adm, denoteω, recordCodec]
  | .refine c q, ha => by
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v; cases hq : q v <;> simp [Adm, denoteω, Codec.restrict, hq, hc v]
  | .legacy c r, ha => by
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v; simpa [Adm, denoteω, Codec.extendRead] using hc v
  | .lazy c, ha => by
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v; simpa [Adm, denoteω] using hc v
  | .held c f g, ha => by
      have hc := Adm_exact c (by simpa [Analysable] using ha)
      intro v; simpa [Adm, denoteω, Codec.through] using hc (f v)
  | .set _, ha | .tuple _ _, ha | .object _ _, ha | .dunion _ _, ha
  | .union _, ha | .nullable _, ha | .opaq _, ha => by simp [Analysable] at ha


/-- §5's empty-container argument, **derived**: the exact row still admits `[]`. -/
theorem Adm_array_nil (c : Term) : Adm (.array c) (.arr []) = true := by
  simp [Adm, AdmAll]

/-- …and it is strictly sharper than the `⊤` that was standing in for it. -/
theorem Adm_array_sharp : Adm (.array (.literalS ["A"])) (.arr [.str "B"]) = false := by
  simp [Adm, AdmAll]

/-- Nested, which the old row could not see at any depth. -/
theorem Adm_array_nested :
    Adm (.array (.array (.literalS ["A"]))) (.arr [.arr [.str "B"]]) = false := by
  simp [Adm, AdmAll]

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
  simp [denoteω, Codec.withNull, Codec.ownsNull, Codec.extendRead, stringCodec, rNull] at this


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
  /-- `extendRead` widens `p` past the subterm's set, by construction. Attribute side
      only — on the value side `legacy` is a transparent passthrough. -/
  | widenedRead
  deriving DecidableEq

/-- Which term shapes each excuse may be invoked for. The catch-all answers `false`, so a
    new constructor is *not* excusable by default — see the note above. -/
def Excuse.covers : Excuse → Term → Bool
  | .opaqueDepth,     .opaq _      => true
  | .uniqueAdmission, .union _     => true
  | .uniqueAdmission, .dunion _ _  => true
  | .payloadShape,    .set _       => true
  | .nameAdmission,   .object _ _  => true
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
  | .object _ _, _  => .inl ⟨.nameAdmission, rfl⟩
  | .tuple _ _, _   => .inl ⟨.nameAdmission, rfl⟩
  | .nullable _, _  => .inl ⟨.nullOwnership, rfl⟩
  -- The propagating wrappers decline only by inheritance, and say so.
  | .array c, h | .record c, h | .refine c _, h | .legacy c _, h | .lazy c, h
  | .held c _ _, h => .inr ⟨c, rfl, by simpa [Analysable] using h⟩
  -- The exact rows: the hypothesis refutes them, which is the point — a term cannot both
  -- carry an exactness proof and claim an excuse.
  | .string, h | .boolean, h | .binary, h | .null, h | .number, h | .decimal, h
  | .literalS _, h | .literalN _, h | .literal _, h | .custom _ _, h => nomatch h

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

/-- …and over a record's entries. -/
theorem AdmAllSnd_sound_aux {c : Term} {C : Codec}
    (hc : ∀ {v a}, C.e v = some a → Adm c v = true) :
    ∀ {kvs : List (Name × Value)} {ys},
      traverse (encPair C) kvs = some ys → AdmAllSnd c kvs = true
  | [], _, _ => by simp [AdmAllSnd]
  | kv :: kvs, ys, h => by
      simp only [traverse] at h
      cases hx : encPair C kv with
      | none => rw [hx] at h; exact nomatch h
      | some y =>
        cases hxs : traverse (encPair C) kvs with
        | none => rw [hx, hxs] at h; exact nomatch h
        | some ys' =>
          have hs : (C.e kv.2).isSome = true := by
            simpa [encPair] using congrArg Option.isSome hx
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
          simp [AdmAllSnd, hc hw, AdmAllSnd_sound_aux hc hxs]

set_option maxHeartbeats 1000000 in
/-- Soundness of every row, fueled. The recursion is on **fuel**, not on the term, which
    is what `κ_sound` and `adm_sound` do: a term recursion here makes the equation compiler
    elaborate all twenty-three heavy cases as one well-founded definition, and it does not
    finish. The heartbeat bump is for the twenty-three-way `cases`, not for any one case. -/
theorem Adm_sound_fueled : ∀ (fuel : Nat) (t : Term) {v a},
    (denote fuel t).e v = some a → Adm t v = true
  | 0, _, _, _, he => nomatch he
  | fuel+1, t, v, a, he => by
    cases t
    case string => cases v <;> simp_all [Adm, denote, stringCodec]
    case boolean => cases v <;> simp_all [Adm, denote, booleanCodec]
    case binary => cases v <;> simp_all [Adm, denote, binaryCodec]
    case null => cases v <;> simp_all [Adm, denote, nullCodec]
    case number => cases v <;> simp_all [Adm, denote, numberCodec, inD]
    case decimal => cases v <;> simp_all [Adm, denote, decimalCodec, isStored]
    case literalS ls => cases v <;> simp_all [Adm, denote, literalSCodec]
    case literalN ls => cases v <;> simp_all [Adm, denote, literalNCodec]
    case literal w =>
      cases w <;> cases v <;>
        simp_all [Adm, denote, literalCodec, Codec.restrict, stringCodec, rawNumberCodec,
                  booleanCodec, binaryCodec, nullCodec, Codec.empty]
    case custom ce cp => simp_all [Adm, denote]
    case opaq lossy => simp [Adm]
    case set c => cases v <;> simp_all [Adm, denote, setCodec]
    case tuple ts tl => cases v <;> simp_all [Adm, denote, tupleCodec]
    case object fs r => cases v <;> simp_all [Adm, denote, objectCodec, objectCodecCore]
    case array c =>
      cases v
      case arr xs =>
        simp only [Adm]
        simp only [denote, arrayCodec] at he
        obtain ⟨ys, hys, -⟩ := Option.map_eq_some'.mp he
        exact AdmAll_sound_aux (fun {v a} h => Adm_sound_fueled fuel c h) hys
      all_goals (simp only [denote, arrayCodec] at he; exact nomatch he)
    case record c =>
      cases v
      case map kvs =>
        simp only [Adm]
        simp only [denote, recordCodec] at he
        obtain ⟨ys, hys, -⟩ := Option.map_eq_some'.mp he
        exact AdmAllSnd_sound_aux (fun {v a} h => Adm_sound_fueled fuel c h) hys
      all_goals (simp only [denote, recordCodec] at he; exact nomatch he)
    case refine c q =>
      obtain ⟨hq, hc⟩ := restrict_e.mp he
      simp [Adm, Adm_sound_fueled fuel c hc, hq]
    case legacy c r => simpa [Adm] using Adm_sound_fueled fuel c (extendRead_e.mp he)
    case lazy c => simpa [Adm] using Adm_sound_fueled fuel c he
    case held c f g => simpa [Adm] using Adm_sound_fueled fuel c he
    case nullable c =>
      cases hw : (denote fuel c).ownsNull with
      | true =>
        rw [show (denote (fuel+1) (.nullable c)).e = (denote fuel c).e from
          withNull_e_of_owns hw] at he
        simp [Adm, Adm_sound_fueled fuel c he]
      | false =>
        rw [show denote (fuel+1) (.nullable c) = (denote fuel c).orNull from
          withNull_eq_orNull hw] at he
        rcases orNull_e.mp he with ⟨rfl, -⟩ | ⟨-, hc⟩
        · simp [Adm]
        · simp [Adm, Adm_sound_fueled fuel c hc]
    case dunion d opts =>
      have h2 := adm_sound _ _ he
      have heq : Adm (.dunion d opts) v = adm (.dunion d opts) v := by rw [Adm, adm]; rfl
      rw [heq]; exact h2
    case union opts =>
      simp only [denote] at he
      obtain ⟨o, ho, -, hoe⟩ := altCodec_e_admits he
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      rw [optionSemOf_c] at hoe
      have key : ∀ (ts : List Term), tx ∈ ts → AdmAny ts v = true := by
        intro ts hts
        induction ts with
        | nil => exact absurd hts (by simp)
        | cons t0 ts ih =>
          rcases List.mem_cons.mp hts with rfl | h'
          · simp [AdmAny, Adm_sound_fueled fuel tx hoe]
          · simp [AdmAny, ih h']
      simpa [Adm] using key opts htx

/-- **Every row is a sound over-approximation, the hatch included.**

    `Adm_exact` binds the sixteen analysable rows to `dom(e)` in both directions. The other
    seven had, until this theorem, *no* obligation at all: nothing stopped a hatch row being
    written `fun _ => false`, which would have been an outright unsoundness rather than the
    imprecision every defect in the log so far has been. A hatch row may be **loose**; it
    may not be **wrong**, and that is now checked. -/
theorem Adm_sound (t : Term) {v a} (he : (denoteω t).e v = some a) : Adm t v = true := by
  rw [denoteω_eq t (termDepth t) (Nat.le_refl _)] at he
  exact Adm_sound_fueled _ t he

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

/-- `set`'s kind gate over-claims: `asWireSet` refuses the empty run at every element type. -/
theorem not_ExactV_set : ¬ ExactV (.set .string) := by
  intro h
  have := (h (.set [])).mp (by simp [Adm])
  simp [denoteω, setCodec, traverse, asWireSet] at this

/-- `tuple`'s over-claims on alignment: one component against two elements. -/
theorem not_ExactV_tuple : ¬ ExactV (.tuple [.string] none) := by
  intro h
  have := (h (.arr [.str "a", .str "b"])).mp (by simp [Adm])
  simp [denoteω, denoteωL, denoteωO, tupleCodec, align, stringCodec] at this

/-- **(U) failing in its purest form.** `select` writes only where *exactly one* option
    admits, so two copies of one option admit everything and write nothing — while `⋁`
    says yes. No arithmetic, no `Double`, just the counting `select` does. -/
theorem not_ExactV_union : ¬ ExactV (.union [.string, .string]) := by
  intro h
  have := (h (.str "a")).mp (by simp [Adm, AdmAny])
  simp [denoteω, denoteωOpts, specOf, optionSemOf, altCodec, select, stringCodec] at this

/-- `opaq`'s ⊤ over-claims: every one of its eight options refuses the empty set.

    `opaq false` also refuses every numeral, which would be the more obvious witness — but
    `Double` is axiomatized with only `toDec`, `ofDec`, `roundtrip` and `decEq`, and is not
    even known to be inhabited, so no `.num` value can be *constructed* here. The empty set
    needs nothing. -/
theorem not_ExactV_opaq (lossy : Bool) : ¬ ExactV (.opaq lossy) := by
  intro h
  have h2 := (h (.set [])).mp (by simp [Adm])
  have hd : (denoteω (Term.opaq lossy)).e (.set [])
      = (setCodec (opaqCodec 1 lossy)).e (.set []) := by
    show (opaqCodecω lossy).e (.set []) = _
    simp only [opaqCodecω, Value.depth, Value.depthL]
    exact opaqCodec_e_set lossy 1 []
  rw [hd] at h2
  simp [setCodec, traverse, asWireSet] at h2

/-- **Every excuse is earned.** Exhaustive over `Excuse`, so a new constructor must come
    with a term of a shape it covers on which exactness actually fails — which, for a shape
    that is exact, cannot be produced. -/
theorem excuse_witnessed : ∀ (e : Excuse) (t : Term), e.covers t = true →
    ∃ t' : Term, e.covers t' = true ∧ ¬ ExactV t'
  | .opaqueDepth, _, _     => ⟨.opaq false, rfl, not_ExactV_opaq false⟩
  | .uniqueAdmission, _, _ => ⟨.union [.string, .string], rfl, not_ExactV_union⟩
  | .payloadShape, _, _    => ⟨.set .string, rfl, not_ExactV_set⟩
  | .nameAdmission, _, _   => ⟨.tuple [.string] none, rfl, not_ExactV_tuple⟩
  | .nullOwnership, _, _   => ⟨.nullable (.legacy .string rNull), rfl, not_ExactV_nullable⟩
  -- The two attribute-side reasons cover nothing here, so the hypothesis is unsatisfiable.
  | .valueUnderRead, t, h  => by cases t <;> simp [Excuse.covers] at h
  | .widenedRead, t, h     => by cases t <;> simp [Excuse.covers] at h

/-! ## The attribute side

`Adm` is the value half. `admA` is the attribute half of §5's tables, and it has no
`Adm`-shaped counterpart — which is the first reason the analysis tables cannot simply be
renamed onto `Adm`. `AdmA` below is that counterpart's definition and its soundness proof.

The mirror is not symmetric, and the asymmetries are §1's rather than this file's: the
numeric rows go through `Double.ofDec`, `refine` cannot narrow a read, and `legacy` widens
one. Each is a row here rather than a remark. -/

mutual

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
      | .n x => (match Double.ofDec x with
                 | some d => Numeral.WF d.toDec
                 | none => false)
      | _ => false
  | .decimal  => fun a => match a with | .n x => Numeral.Stored x | _ => false
  | .literalS ls => fun a => match a with | .s s => s ∈ ls | _ => false
  | .literalN ls => fun a =>
      match a with
      | .n x => (match Double.ofDec x with
                 | some d => decide (d ∈ ls)
                 | none => false)
      | _ => false
  | .literal w => fun a =>
      match w, a with
      | .str s, .s s'     => decide (s' = s)
      | .bool b, .bool b' => decide (b' = b)
      | .bin b, .b b'     => decide (b' = b)
      | .null, .null      => true
      | .num d, .n x      => (match Double.ofDec x with
                              | some d' => decide (d' = d)
                              | none => false)
      | _, _              => false
  | .custom _ cp => fun a => (cp a).isSome
  | .array c  => fun a => match a with | .l as => AdmAAll c as | _ => false
  | .record c => fun a => match a with | .m kas => AdmAAllSnd c kas | _ => false
  | .held t _ _ => AdmA t
  | .lazy t   => AdmA t
  -- hatch
  | .refine t _ => AdmA t
  | .legacy _ _ => fun _ => true
  | .nullable t => fun a => AdmA t a || (match a with | .null => true | _ => false)
  | .union opts => fun a => AdmAAny opts a
  | .set _    => fun a => match a with | .ss _ | .ns _ | .bs _ => true | _ => false
  | .tuple _ _ => fun a => match a with | .l _ => true | _ => false
  | .object _ _ => fun a => match a with | .m _ => true | _ => false
  | .dunion d opts => fun a =>
      match a with
      | .m kas =>
        (match kas.lookup d with
         | some (.s tag) => (allTags d opts).contains tag
         | _ => false)
      | _ => false
  | .opaq _ => fun _ => true

/-- `⋀` of `AdmA` over a container's entries. -/
noncomputable def AdmAAll : Term → List Attr → Bool
  | _, [] => true
  | c, a :: as => AdmA c a && AdmAAll c as

/-- …and over a record's entry attributes. -/
noncomputable def AdmAAllSnd : Term → List (Name × Attr) → Bool
  | _, [] => true
  | c, ka :: kas => AdmA c ka.2 && AdmAAllSnd c kas

/-- `⋁` over a union's options; sound, and exact only under (U), as on the value side. -/
noncomputable def AdmAAny : List Term → Attr → Bool
  | [], _ => false
  | t :: ts, a => AdmA t a || AdmAAny ts a

end


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

/-- …and over a record's entries. -/
theorem AdmAAllSnd_sound_aux {c : Term} {C : Codec}
    (hc : ∀ {a v}, C.p a = some v → AdmA c a = true) :
    ∀ {kas : List (Name × Attr)} {vs},
      traverse (decPair C) kas = some vs → AdmAAllSnd c kas = true
  | [], _, _ => by simp [AdmAAllSnd]
  | ka :: kas, vs, h => by
      simp only [traverse] at h
      cases hx : decPair C ka with
      | none => rw [hx] at h; exact nomatch h
      | some y =>
        cases hxs : traverse (decPair C) kas with
        | none => rw [hx, hxs] at h; exact nomatch h
        | some vs' =>
          have hs : (C.p ka.2).isSome = true := by
            simpa [decPair] using congrArg Option.isSome hx
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
          simp [AdmAAllSnd, hc hw, AdmAAllSnd_sound_aux hc hxs]

set_option maxHeartbeats 1000000 in
/-- Soundness of every attribute row, fueled; recursion on fuel, as on the value side. -/
theorem AdmA_sound_fueled : ∀ (fuel : Nat) (t : Term) {a v},
    (denote fuel t).p a = some v → AdmA t a = true
  | 0, _, _, _, hp => nomatch hp
  | fuel+1, t, a, v, hp => by
    cases t
    case string => cases a <;> simp_all [AdmA, denote, stringCodec]
    case boolean => cases a <;> simp_all [AdmA, denote, booleanCodec]
    case binary => cases a <;> simp_all [AdmA, denote, binaryCodec]
    case null => cases a <;> simp_all [AdmA, denote, nullCodec]
    case number =>
      cases a
      case n x =>
        simp only [denote, numberCodec] at hp
        cases hx : Double.ofDec x <;> rw [hx] at hp <;> simp_all [AdmA]
      all_goals (simp only [denote, numberCodec] at hp; exact nomatch hp)
    case decimal => cases a <;> simp_all [AdmA, denote, decimalCodec]
    case literalS ls => cases a <;> simp_all [AdmA, denote, literalSCodec]
    case literalN ls =>
      cases a
      case n x =>
        simp only [denote, literalNCodec] at hp
        cases hx : Double.ofDec x <;> rw [hx] at hp <;> simp_all [AdmA]
      all_goals (simp only [denote, literalNCodec] at hp; exact nomatch hp)
    case literal w =>
      cases w
      case num d =>
        cases a
        case n x =>
          simp only [denote, literalCodec, Codec.restrict, rawNumberCodec] at hp
          cases hx : Double.ofDec x with
          | none => rw [hx] at hp; simp at hp
          | some d' =>
            rw [hx] at hp
            -- keep only `d' = d`: the other conjunct equates the *decoded value* with `v`,
            -- and `simp_all` will happily rewrite the literal's own payload backwards with it
            obtain ⟨h1, -⟩ : d' = d ∧ Value.num d' = v := by simpa using hp
            simp [AdmA, hx, h1]
        all_goals
          (simp only [denote, literalCodec, Codec.restrict, rawNumberCodec] at hp
           exact nomatch hp)
      -- For every payload but `num`, this row and `admA`'s coincide, so its soundness
      -- lemma carries: the two part company only where `Double.ofDec` does.
      -- For every payload but `num` this row and `admA`'s coincide — they part company
      -- only where `Double.ofDec` does — so `admA_sound` carries them.
      case str sv =>
        have heq : AdmA (.literal (.str sv)) a = admA (.literal (.str sv)) a := by
          cases a <;> simp [AdmA, admA]
        rw [heq]; exact admA_sound _ _ hp
      case bool bv =>
        have heq : AdmA (.literal (.bool bv)) a = admA (.literal (.bool bv)) a := by
          cases a <;> simp [AdmA, admA]
        rw [heq]; exact admA_sound _ _ hp
      case bin bv =>
        have heq : AdmA (.literal (.bin bv)) a = admA (.literal (.bin bv)) a := by
          cases a <;> simp [AdmA, admA]
        rw [heq]; exact admA_sound _ _ hp
      case null =>
        have heq : AdmA (.literal .null) a = admA (.literal .null) a := by
          cases a <;> simp [AdmA, admA]
        rw [heq]; exact admA_sound _ _ hp
      -- A container payload has no ground base, so `literalCodec` is `Codec.empty`.
      all_goals (simp only [denote, literalCodec, Codec.empty] at hp; exact nomatch hp)
    case custom ce cp => simp_all [AdmA, denote]
    case opaq lossy => simp [AdmA]
    case legacy c r => simp [AdmA]
    case set c => cases a <;> simp_all [AdmA, denote, setCodec]
    case tuple ts tl => cases a <;> simp_all [AdmA, denote, tupleCodec]
    case object fs r => cases a <;> simp_all [AdmA, denote, objectCodec, objectCodecCore]
    case array c =>
      cases a
      case l as =>
        simp only [AdmA]
        simp only [denote, arrayCodec] at hp
        obtain ⟨vs, hvs, -⟩ := Option.map_eq_some'.mp hp
        exact AdmAAll_sound_aux (fun {a v} h => AdmA_sound_fueled fuel c h) hvs
      all_goals (simp only [denote, arrayCodec] at hp; exact nomatch hp)
    case record c =>
      cases a
      case m kas =>
        simp only [AdmA]
        simp only [denote, recordCodec] at hp
        obtain ⟨vs, hvs, -⟩ := Option.map_eq_some'.mp hp
        exact AdmAAllSnd_sound_aux (fun {a v} h => AdmA_sound_fueled fuel c h) hvs
      all_goals (simp only [denote, recordCodec] at hp; exact nomatch hp)
    case refine c q => simpa [AdmA] using AdmA_sound_fueled fuel c (restrict_p.mp hp).1
    case lazy c => simpa [AdmA] using AdmA_sound_fueled fuel c hp
    case held c f g =>
      obtain ⟨w, hw, -⟩ := through_p.mp hp
      simpa [AdmA] using AdmA_sound_fueled fuel c hw
    case nullable c =>
      cases hw : (denote fuel c).ownsNull with
      | true =>
        rw [show (denote (fuel+1) (.nullable c)).p = (denote fuel c).p from
          withNull_p_of_owns hw] at hp
        simp [AdmA, AdmA_sound_fueled fuel c hp]
      | false =>
        rw [show denote (fuel+1) (.nullable c) = (denote fuel c).orNull from
          withNull_eq_orNull hw] at hp
        rcases orNull_p.mp hp with ⟨rfl, -⟩ | ⟨-, hc⟩
        · simp [AdmA]
        · simp [AdmA, AdmA_sound_fueled fuel c hc]
    case dunion d opts =>
      have h2 := admA_sound _ _ hp
      have heq : AdmA (.dunion d opts) a = admA (.dunion d opts) a := by rw [AdmA, admA]; rfl
      rw [heq]; exact h2
    case union opts =>
      simp only [denote] at hp
      obtain ⟨o, ho, -, hop⟩ := altCodec_p_admits hp
      simp only [List.mem_map] at ho
      obtain ⟨tx, htx, rfl⟩ := ho
      rw [optionSemOf_c] at hop
      have key : ∀ (ts : List Term), tx ∈ ts → AdmAAny ts a = true := by
        intro ts hts
        induction ts with
        | nil => exact absurd hts (by simp)
        | cons t0 ts ih =>
          rcases List.mem_cons.mp hts with rfl | h'
          · simp [AdmAAny, AdmA_sound_fueled fuel tx hop]
          · simp [AdmAAny, ih h']
      simpa [AdmA] using key opts htx

/-- **Every attribute row is a sound over-approximation, the hatch included** — the
    attribute-side counterpart of `Adm_sound`, and the same obligation for the same reason.

    Exactness for these rows is **not** yet proved; the value side's `Adm_exact` has no
    mirror here. Until it does, `AdmA` carries one obligation where `Adm` carries two, and
    the analysis tables cannot be migrated onto the pair. -/
theorem AdmA_sound (t : Term) {a v} (hp : (denoteω t).p a = some v) : AdmA t a = true := by
  rw [denoteω_eq t (termDepth t) (Nat.le_refl _)] at hp
  exact AdmA_sound_fueled _ t hp

/-- The converse direction on the attribute side: the row is `dom(p)`, not a bound on it. -/
def ExactA (t : Term) : Prop := ∀ a, AdmA t a = true ↔ ((denoteω t).p a).isSome

/-- The attribute-side hatch, wider than the value side's by three rows, and the three are
    the asymmetries §1 imposes rather than anything this file chose.

    * `refine` — `q` tests the value a read *produces*; no syntactic set of attributes
      bounds that. This is the row `admA` could never narrow either, and the reason `adm`
      and `admA` are two functions rather than one.
    * `legacy` — `extendRead` widens `p` past the subterm's set, by construction
      (`not_admA_legacy`).
    * `nullable` — `ownsNull` again, and this side is where the disjunction bites first.

    The remaining six are the same shapes the value side excuses. -/
def AnalysableA : Term → Bool
  | .string | .boolean | .binary | .null | .number | .decimal
  | .literalS _ | .literalN _ | .literal _ | .custom _ _ => true
  | .array c | .record c | .held c _ _ | .lazy c => AnalysableA c
  | .refine _ _ | .legacy _ _ | .nullable _ | .union _
  | .set _ | .tuple _ _ | .object _ _ | .dunion _ _ | .opaq _ => false

/-- `AdmAAll` transported across the entry's exactness. -/
theorem AdmAAll_iff {c : Term} (h : ExactA c) : ∀ as : List Attr,
    AdmAAll c as = true ↔ ∀ a ∈ as, ((denoteω c).p a).isSome = true := by
  intro as; induction as with
  | nil => simp [AdmAAll]
  | cons a as ih => simp [AdmAAll, ih, h a]

/-- …and `AdmAAllSnd`. -/
theorem AdmAAllSnd_iff {c : Term} (h : ExactA c) : ∀ kas : List (Name × Attr),
    AdmAAllSnd c kas = true ↔ ∀ ka ∈ kas, ((denoteω c).p ka.2).isSome = true := by
  intro kas; induction kas with
  | nil => simp [AdmAAllSnd]
  | cons ka kas ih => simp [AdmAAllSnd, ih, h ka.2]

/-- **Fourteen of the twenty-three attribute rows are exact.** Two fewer than the value
    side, and the two are `refine` and `legacy` — the pair whose asymmetry is the reason
    §5 needed `adm` and `admA` rather than one function.

    The numeric rows are the interesting ones: they reach `dom(p)` through `Double.ofDec`,
    which is axiomatized, and are exact anyway — a row may *call* an axiomatized function
    even though no finite set of numerals describes its domain. §5 wrote `⊤` there. -/
theorem AdmA_exact : ∀ (t : Term), AnalysableA t = true → ExactA t
  | .string, _ => by intro a; cases a <;> simp [AdmA, denoteω, stringCodec]
  | .boolean, _ => by intro a; cases a <;> simp [AdmA, denoteω, booleanCodec]
  | .binary, _ => by intro a; cases a <;> simp [AdmA, denoteω, binaryCodec]
  | .null, _ => by intro a; cases a <;> simp [AdmA, denoteω, nullCodec]
  | .number, _ => by
      intro a
      cases a
      case n x =>
        simp only [AdmA, denoteω, numberCodec]
        cases hx : Double.ofDec x <;> simp [hx]
      all_goals simp [AdmA, denoteω, numberCodec]
  | .decimal, _ => by intro a; cases a <;> simp [AdmA, denoteω, decimalCodec]
  | .literalS ls, _ => by intro a; cases a <;> simp [AdmA, denoteω, literalSCodec]
  | .literalN ls, _ => by
      intro a
      cases a
      case n x =>
        simp only [AdmA, denoteω, literalNCodec]
        cases hx : Double.ofDec x <;> simp [hx]
      all_goals simp [AdmA, denoteω, literalNCodec]
  | .literal w, _ => by
      intro a
      cases w
      case num d =>
        cases a
        case n x =>
          simp only [AdmA, denoteω, literalCodec, Codec.restrict, rawNumberCodec]
          cases hx : Double.ofDec x <;> simp [hx]
        all_goals simp [AdmA, denoteω, literalCodec, Codec.restrict, rawNumberCodec]
      all_goals
        (cases a <;>
          simp [AdmA, denoteω, literalCodec, Codec.restrict, stringCodec, booleanCodec,
                binaryCodec, nullCodec, Codec.empty])
  | .custom ce cp, _ => by intro a; simp [AdmA, denoteω]
  | .array c, ha => by
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a
      cases a
      case l as =>
        simp only [AdmA, denoteω, arrayCodec]
        rw [AdmAAll_iff hc, ← traverse_isSome_iff]
        cases traverse (denoteω c).p as <;> simp
      all_goals simp [AdmA, denoteω, arrayCodec]
  | .record c, ha => by
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a
      cases a
      case m kas =>
        simp only [AdmA, denoteω, recordCodec]
        rw [AdmAAllSnd_iff hc]
        have hkey : (∀ ka ∈ kas, ((denoteω c).p ka.2).isSome = true)
                  ↔ (∀ ka ∈ kas, (decPair (denoteω c) ka).isSome = true) :=
          ⟨fun hall ka hka => by simpa [decPair] using hall ka hka,
           fun hall ka hka => by simpa [decPair] using hall ka hka⟩
        rw [hkey, ← traverse_isSome_iff]
        cases traverse (decPair (denoteω c)) kas <;> simp
      all_goals simp [AdmA, denoteω, recordCodec]
  | .held c f g, ha => by
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a
      simp only [AdmA, denoteω, Codec.through]
      rw [hc a]
      cases (denoteω c).p a <;> simp
  | .lazy c, ha => by
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a; simpa [AdmA, denoteω] using hc a
  | .refine _ _, ha | .legacy _ _, ha | .nullable _, ha | .union _, ha
  | .set _, ha | .tuple _ _, ha | .object _ _, ha | .dunion _ _, ha
  | .opaq _, ha => by simp [AnalysableA] at ha

/-! ### The attribute side's excuses, and their witnesses

The value side's five reasons apply here too, and two more do — `refine`, which cannot
narrow a read because `q` tests the value a read *produces*, and `legacy`, which widens one
by construction. Those two cover nothing on the value side, which is why `excuse_witnessed`
is stated with the covering as a hypothesis: an excuse must be witnessed **on the side it is
used on**, and neither side has to answer for the other's reasons. -/

/-- `set`'s member gate over-claims: the empty run is refused on this side too. -/
theorem not_ExactA_set : ¬ ExactA (.set .string) := by
  intro h
  have := (h (.ss [])).mp (by simp [AdmA])
  simp [denoteω, setCodec] at this

/-- Alignment again, read side. -/
theorem not_ExactA_tuple : ¬ ExactA (.tuple [.string] none) := by
  intro h
  have := (h (.l [.s "a", .s "b"])).mp (by simp [AdmA])
  simp [denoteω, denoteωL, denoteωO, tupleCodec, align, stringCodec] at this

/-- (U) failing, read side: two options admit and `select` reads nothing. -/
theorem not_ExactA_union : ¬ ExactA (.union [.string, .string]) := by
  intro h
  have := (h (.s "a")).mp (by simp [AdmA, AdmAAny])
  simp [denoteω, denoteωOpts, specOf, optionSemOf, altCodec, select, stringCodec] at this

/-- `opaq`'s ⊤ over-claims: the empty wire set is refused by all eight options. -/
theorem not_ExactA_opaq (lossy : Bool) : ¬ ExactA (.opaq lossy) := by
  intro h
  have h2 := (h (.ss [])).mp (by simp [AdmA])
  have hd : (denoteω (Term.opaq lossy)).p (.ss [])
      = (setCodec (opaqCodec 1 lossy)).p (.ss []) := by
    show (opaqCodecω lossy).p (.ss []) = _
    simp only [opaqCodecω, Attr.depth]
    exact opaqCodec_p_ss lossy 1 []
  rw [hd] at h2
  simp [setCodec] at h2

/-- Writes the null point — half of a pair whose write reaches it and whose read does not,
    the mirror of `rNull`, and the reason `nullable` is in both hatches rather than one. -/
def ceNull : Value → Option Attr := fun v => match v with | .null => some .null | _ => none
/-- …and reads nothing at all. -/
def cpNone : Attr → Option Value := fun _ => none

theorem not_ExactA_nullable : ¬ ExactA (.nullable (.custom ceNull cpNone)) := by
  intro h
  have h2 := (h .null).mp (by simp [AdmA])
  simp [denoteω, Codec.withNull, Codec.ownsNull, ceNull, cpNone] at h2

/-- `refine` cannot narrow a read: `q` refuses everything, and `AdmA` cannot see it. -/
theorem not_ExactA_refine : ¬ ExactA (.refine .string (fun _ => false)) := by
  intro h
  have h2 := (h (.s "a")).mp (by simp [AdmA])
  simp [denoteω, Codec.restrict, stringCodec] at h2

/-- `legacy` is `⊤` here, so it over-claims at every attribute its subterm refuses. -/
theorem not_ExactA_legacy : ¬ ExactA (.legacy .string (fun _ => none)) := by
  intro h
  have h2 := (h (.n "1")).mp (by simp [AdmA])
  simp [denoteω, Codec.extendRead, stringCodec] at h2


/-- Which shapes each excuse may be invoked for **on the attribute side**. Two rows have no
    value-side counterpart, and the catch-all answers `false` for the same reason it does
    there: a new constructor is not excusable by default. -/
def Excuse.coversA : Excuse → Term → Bool
  | .opaqueDepth,     .opaq _      => true
  | .uniqueAdmission, .union _     => true
  | .uniqueAdmission, .dunion _ _  => true
  | .payloadShape,    .set _       => true
  | .nameAdmission,   .object _ _  => true
  | .nameAdmission,   .tuple _ _   => true
  | .nullOwnership,   .nullable _  => true
  | .valueUnderRead,  .refine _ _  => true
  | .widenedRead,     .legacy _ _  => true
  | _, _ => false

/-- The subterm a propagating **attribute** row inherits from. `refine` and `legacy` are
    absent, which is the whole of the asymmetry: they propagate on the value side and are
    excused here. -/
def inheritsFromA : Term → Option Term
  | .array c | .record c | .held c _ _ | .lazy c => some c
  | _ => none

/-- Every attribute row that declines exactness names a covering reason or inherits one. -/
theorem analysableA_excused : ∀ (t : Term), AnalysableA t = false →
    (∃ e : Excuse, e.coversA t = true) ∨ (∃ c, inheritsFromA t = some c ∧ AnalysableA c = false)
  | .opaq _, _      => .inl ⟨.opaqueDepth, rfl⟩
  | .union _, _     => .inl ⟨.uniqueAdmission, rfl⟩
  | .dunion _ _, _  => .inl ⟨.uniqueAdmission, rfl⟩
  | .set _, _       => .inl ⟨.payloadShape, rfl⟩
  | .object _ _, _  => .inl ⟨.nameAdmission, rfl⟩
  | .tuple _ _, _   => .inl ⟨.nameAdmission, rfl⟩
  | .nullable _, _  => .inl ⟨.nullOwnership, rfl⟩
  | .refine _ _, _  => .inl ⟨.valueUnderRead, rfl⟩
  | .legacy _ _, _  => .inl ⟨.widenedRead, rfl⟩
  | .array c, h | .record c, h | .held c _ _, h | .lazy c, h =>
      .inr ⟨c, rfl, by simpa [AnalysableA] using h⟩
  | .string, h | .boolean, h | .binary, h | .null, h | .number, h | .decimal, h
  | .literalS _, h | .literalN _, h | .literal _, h | .custom _ _, h => nomatch h

/-- No attribute-side excuse names an exact row. -/
theorem excuseA_shapes (e : Excuse) (t : Term) (h : e.coversA t = true) :
    AnalysableA t = false := by
  cases e <;> cases t <;> simp_all [Excuse.coversA, AnalysableA]

/-- **Every attribute-side excuse is earned**, on the side it is used on. -/
theorem excuseA_witnessed : ∀ (e : Excuse) (t : Term), e.coversA t = true →
    ∃ t' : Term, e.coversA t' = true ∧ ¬ ExactA t'
  | .opaqueDepth, _, _     => ⟨.opaq false, rfl, not_ExactA_opaq false⟩
  | .uniqueAdmission, _, _ => ⟨.union [.string, .string], rfl, not_ExactA_union⟩
  | .payloadShape, _, _    => ⟨.set .string, rfl, not_ExactA_set⟩
  | .nameAdmission, _, _   => ⟨.tuple [.string] none, rfl, not_ExactA_tuple⟩
  | .nullOwnership, _, _   => ⟨.nullable (.custom ceNull cpNone), rfl, not_ExactA_nullable⟩
  | .valueUnderRead, _, _  => ⟨.refine .string (fun _ => false), rfl, not_ExactA_refine⟩
  | .widenedRead, _, _     => ⟨.legacy .string (fun _ => none), rfl, not_ExactA_legacy⟩

end
end Calculus
