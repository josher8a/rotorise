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
  -- `set` recurses like the other containers, and adds the non-emptiness `asWireSet`
  -- demands. Homogeneity is no longer a row's problem at all: §1's three set types are
  -- three constructors, so an element's kind is fixed by which one it is.
  | .set c      => fun v =>
      match v with
      | .strSet S => decide (S.card ≠ 0) && decide (∀ s ∈ S, Adm c (.str s) = true)
      | .numSet S => decide (S.card ≠ 0) && decide (∀ d ∈ S, Adm c (.num d) = true)
      | .binSet S => decide (S.card ≠ 0) && decide (∀ b ∈ S, Adm c (.bin b) = true)
      | _ => false
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
    case set c =>
      cases v
      case strSet S =>
        simp only [denote, setCodec] at he
        obtain ⟨x, hx⟩ := encSet_nonempty he
        have hall := encSet_elem he
        simp only [Adm, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨Finset.card_ne_zero_of_mem hx, fun y hy => ?_⟩
        obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall y hy)
        exact Adm_sound_fueled fuel c ha'
      case numSet S =>
        simp only [denote, setCodec] at he
        obtain ⟨x, hx⟩ := encSet_nonempty he
        have hall := encSet_elem he
        simp only [Adm, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨Finset.card_ne_zero_of_mem hx, fun y hy => ?_⟩
        obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall y hy)
        exact Adm_sound_fueled fuel c ha'
      case binSet S =>
        simp only [denote, setCodec] at he
        obtain ⟨x, hx⟩ := encSet_nonempty he
        have hall := encSet_elem he
        simp only [Adm, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨Finset.card_ne_zero_of_mem hx, fun y hy => ?_⟩
        obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall y hy)
        exact Adm_sound_fueled fuel c ha'
      all_goals (simp only [denote, setCodec] at he; exact nomatch he)
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

/-- An adapter that collapses two distinct strings onto one. -/
def collapse : Value → Value := fun _ => .str "x"

/-- **`set`'s row still over-claims, but no longer for the reason §5 gave.** Heterogeneity
    is gone — a value set is typed, so its elements cannot differ in kind. What remains is
    *collision*: the row asks that every element write, and `encSet` asks in addition that
    they write to **distinct** payloads, because a set codec that merged two elements could
    not retract. -/
theorem not_ExactV_set : ¬ ExactV (.set (.held .string collapse (fun v => v))) := by
  intro h
  have h2 := (h (.strSet {"a", "b"})).mp (by simp [Adm, collapse])
  simp (config := { decide := true }) [denoteω, setCodec, encSet, Codec.through,
        stringCodec, collapse, setImage, sC, nC, bC] at h2

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
  have h2 := (h (.strSet ∅)).mp (by simp [Adm])
  have hd : (denoteω (Term.opaq lossy)).e (.strSet ∅)
      = (setCodec (opaqCodec 1 lossy)).e (.strSet ∅) := by
    show (opaqCodecω lossy).e (.strSet ∅) = _
    simp only [opaqCodecω, Value.depth]
    exact opaqCodec_e_strSet lossy 1 ∅
  rw [hd] at h2
  simp [setCodec, encSet] at h2

/-- **Every excuse is earned.** Exhaustive over `Excuse`, so a new constructor must come
    with a term of a shape it covers on which exactness actually fails — which, for a shape
    that is exact, cannot be produced. -/
theorem excuse_witnessed : ∀ (e : Excuse) (t : Term), e.covers t = true →
    ∃ t' : Term, e.covers t' = true ∧ ¬ ExactV t'
  | .opaqueDepth, _, _     => ⟨.opaq false, rfl, not_ExactV_opaq false⟩
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
  -- `legacy` is the read-side **alternative**, not an adapter: `p` is the subterm's channel
  -- falling back to `r`'s, so the domain is the *union* of the two. `r` is data the term
  -- carries, exactly as `held`'s `f` and `custom`'s `cp` are, so the row can apply it.
  | .legacy t r => fun a => AdmA t a || (r a).isSome
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
    case legacy c r =>
      simp only [denote, Codec.extendRead] at hp
      cases hc : (denote fuel c).p a with
      | some w => rw [hc] at hp; simp [AdmA, AdmA_sound_fueled fuel c hc]
      | none => rw [hc] at hp; simp [AdmA, hp]
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
    * `nullable` — `ownsNull` again, and this side is where the disjunction bites first.

    The remaining six are the same shapes the value side excuses. -/
def AnalysableA : Term → Bool
  | .string | .boolean | .binary | .null | .number | .decimal
  | .literalS _ | .literalN _ | .literal _ | .custom _ _ => true
  | .array c | .record c | .held c _ _ | .lazy c | .legacy c _ => AnalysableA c
  | .refine _ _ | .nullable _ | .union _
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
  | .legacy c r, ha => by
      have hc := AdmA_exact c (by simpa [AnalysableA] using ha)
      intro a
      simp only [AdmA, denoteω, Codec.extendRead]
      cases hx : (denoteω c).p a <;> simp [hc a, hx]
  | .refine _ _, ha | .nullable _, ha | .union _, ha
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
  have := (h (.ss ∅)).mp (by simp [AdmA])
  simp [denoteω, setCodec, decSet] at this

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
  have h2 := (h (.ss ∅)).mp (by simp [AdmA])
  have hd : (denoteω (Term.opaq lossy)).p (.ss ∅)
      = (setCodec (opaqCodec 1 lossy)).p (.ss ∅) := by
    show (opaqCodecω lossy).p (.ss ∅) = _
    simp only [opaqCodecω, Attr.depth]
    exact opaqCodec_p_ss lossy 1 ∅
  rw [hd] at h2
  simp [setCodec, decSet] at h2

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
  | .object _ _, _  => .inl ⟨.nameAdmission, rfl⟩
  | .tuple _ _, _   => .inl ⟨.nameAdmission, rfl⟩
  | .nullable _, _  => .inl ⟨.nullOwnership, rfl⟩
  | .refine _ _, _  => .inl ⟨.valueUnderRead, rfl⟩
  | .array c, h | .record c, h | .held c _ _, h | .lazy c, h | .legacy c _, h =>
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
  | .object _ _, _, _ => rfl
  | .array _, _, _ => rfl
  | .record _, _, _ => rfl
  | .opaq _, _, _ => rfl
  | .number, v, h => by simpa [adm] using (by simpa [Adm] using h : inD v = true)
  | .decimal, v, h => by simpa [adm] using (by simpa [Adm] using h : isStored v = true)
  | .literalS ls, v, h => by rw [adm]; rw [Adm] at h; exact h
  | .literalN ls, v, h => by rw [adm]; rw [Adm] at h; exact h
  | .literal w, v, h => by rw [adm]; rw [Adm] at h; exact h
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
  | .literalS _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .literalN _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .literal w, _, v, rfl, h => by cases w <;> cases v <;> simp_all [Adm, Value.kind]
  | .set _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .array _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .tuple _ _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .record _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .object _ _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
  | .dunion _ _, _, v, rfl, h => by cases v <;> simp_all [Adm, Value.kind]
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
  | .literalN _, _, _ => rfl
  | .set _, _, _ => rfl
  | .tuple _ _, _, _ => rfl
  | .object _ _, _, _ => rfl
  | .array _, _, _ => rfl
  | .record _, _, _ => rfl
  | .legacy _ _, _, _ => rfl
  | .opaq _, _, _ => rfl
  | .custom _ _, a, h => by rw [admA]; rw [AdmA] at h; exact h
  | .decimal, a, h => by rw [admA]; rw [AdmA] at h; exact h
  | .literalS _, a, h => by rw [admA]; rw [AdmA] at h; exact h
  | .dunion _ _, a, h => by rw [admA]; rw [AdmA] at h; exact h
  | .literal w, a, h => by
      cases w <;> cases a <;> simp_all [AdmA, admA]
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
  exact absurd (h (.ns ∅) (by simp [AdmA])) (by simp [AdmA])

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
    (hx : (denoteω x).e v = some a) : ((denoteω y).e v).isSome = false := by
  have hAx : Adm x v = true := Adm_sound x hx
  have hAy : Adm y v = false := h v hAx
  cases hy : (denoteω y).e v with
  | none => rfl
  | some b => exact absurd (Adm_sound y hy) (by simp [hAy])

/-- …and on the attribute side, from `SepJA`'s second disjunct. -/
theorem admitA_of_sepJA {x y : Term} (h : ∀ a, AdmA x a = true → AdmA y a = false)
    (a : Attr) (v : Value) (hx : (denoteω x).p a = some v) :
    ((denoteω y).p a).isSome = false := by
  have hAx : AdmA x a = true := AdmA_sound x hx
  have hAy : AdmA y a = false := h a hAx
  cases hy : (denoteω y).p a with
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
  ∃ v w, ((denoteω t).e v).isSome = true ∧ v.kind = w.kind ∧ ((denoteω t).e w).isSome = false

/-- `literalS` decides, as §5 says. -/
theorem decides_literalS : Decides (.literalS ["A"]) :=
  ⟨.str "A", .str "B", by simp [denoteω, literalSCodec], rfl,
   by simp [denoteω, literalSCodec]⟩

/-- `string` does not, as §5 also says. -/
theorem not_decides_string : ¬ Decides .string := by
  rintro ⟨v, w, hv, hk, hw⟩
  cases v <;> cases w <;> simp_all [denoteω, stringCodec, Value.kind]

/-- **`ident` is too generous.** A refinement by the trivially-true predicate is `ident`,
    and decides nothing: `q` is checked on both halves and always passes, so admission is
    no evidence at all. `ident` cannot see this, because it does not look at `q`. -/
theorem ident_refine_top : ident (.refine .string qTop) = true := rfl

theorem not_decides_refine_top : ¬ Decides (.refine .string qTop) := by
  rintro ⟨v, w, hv, hk, hw⟩
  cases v <;> cases w <;>
    simp_all [denoteω, Codec.restrict, stringCodec, qTop, Value.kind]

/-- **And too stingy.** An object with a required field refuses the empty map and writes a
    populated one — two `map`s differing in admission — while `ident` calls it `false`. -/
theorem decides_object :
    Decides (.object [("k", .req .string)] .refuse) := by
  refine ⟨.map [("k", .str "a")], .map [], ?_, rfl, ?_⟩
  · simp [denoteω, denoteωF, denoteωR, objectCodec, objectCodecCore, stringCodec,
          valPresentB, encEntry, denoteωField, rcOf, traverse, FieldSem.codec]
  · simp [denoteω, denoteωF, denoteωR, objectCodec, objectCodecCore, stringCodec,
          valPresentB, encEntry, denoteωField, rcOf, traverse, FieldSem.codec]

theorem ident_object : ident (.object [("k", .req .string)] .refuse) = false := rfl

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
  · simp [denoteω, Codec.through, stringCodec, fSplit]
  · simp [denoteω, Codec.through, stringCodec, fSplit]

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
    (denoteω (.legacy t r)).p a
      = (match (denoteω t).p a with | some v => some v | none => r a) := rfl

/-- …so its read domain is the union of the two channels, and both are named. -/
theorem legacy_p_isSome (t : Term) (r : Attr → Option Value) (a : Attr) :
    ((denoteω (.legacy t r)).p a).isSome = (((denoteω t).p a).isSome || (r a).isSome) := by
  simp only [legacy_p_alt]
  cases (denoteω t).p a <;> simp

/-- Which is exactly `AdmA`'s row, so `legacy` widens the read side and is exact anyway. -/
theorem AdmA_legacy_union (t : Term) (r : Attr → Option Value) (a : Attr) :
    AdmA (.legacy t r) a = (AdmA t a || (r a).isSome) := by
  simp [AdmA]

/-- **A discharge §5 could not state.** Two sets over disjoint literals separate, because
    `asWireSet` refuses the empty run and so the two options share no inhabitant. -/
theorem sepJV_set_literals :
    SepJV (.set (.literalS ["A"])) (.set (.literalS ["B"])) := by
  intro v hv
  cases v
  case strSet S =>
    simp only [Adm, Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
    obtain ⟨hne, hall⟩ := hv
    obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp hne
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine Or.inr fun hall' => ?_
    have h1 := hall x hx
    have h2 := hall' x hx
    simp [Adm] at h1 h2
    exact absurd (h1.symm.trans h2) (by decide)
  all_goals simp [Adm] at hv ⊢

/-- …and the contrast that shows what the non-emptiness is doing: the *array* pair does not
    separate, because both options admit `[]`. This is §5's empty-container argument in its
    correct scope — it is a fact about `array`, `record` and `object`, not about `set`. -/
theorem not_sepJV_array_literals :
    ¬ SepJV (.array (.literalS ["A"])) (.array (.literalS ["B"])) := by
  intro h
  exact absurd (h (.arr []) (by simp [Adm, AdmAll])) (by simp [Adm, AdmAll])

/-! ### What `set` is, structurally — and one thing it is not

Three readings are worth separating, because two are right and the third turns up a defect.

**Not a `union`.** A union is a choice among *codecs*, resolved by (U); `set`'s elements all
go through **one** codec, so no uniqueness obligation arises. That is the whole reason `set`
is exact-modulo-homogeneity while `union` is exact only under (U).

**Yes, `array` with a partial wrapper.** `setCodec_e_via_arrayCodec`: the two share
`traverse c.e vs` exactly, and differ only in how the payload list is presented — the total
constructor `Attr.l` against the partial `asWireSet`. Every difference between the rows is
that partiality: the non-emptiness `set` gains, and the homogeneity that keeps it out of
`Analysable`. `set` is not `entrywise`, which takes a total `Ctor`; it is the same traversal
under a wrapper that can fail.

**But not "order does not matter".** §1 types `SS` as `℘⁺fin(String)` — non-empty,
*unordered* — and §2 names set orderings as the first of three reasons `ker p` is not
equality: "two orderings of one set are distinct attributes reading to one value". The model
does not do that. `Value.set` is a `List Value` with no quotient and no well-formedness
predicate, so orderings are preserved on both halves (`set_p_order_sensitive`,
`set_e_order_sensitive`) and duplicates survive (`set_e_keeps_duplicates`).

Nothing here is unsound — the laws hold of the model as written. What is false is §2's
stated *reason* for the quotient, at least as the formalization realises §1: two orderings
read to two values, so `ker p` is equality at `setCodec` and the collapse §2 attributes to
sets does not happen. -/

/-- `set` and `array` are one entrywise product with two presentations: the same
    `traverse c.e vs`, wrapped by a *total* constructor in one case and a *partial* one in
    the other. Every difference between the two rows is `asWireSet`'s partiality. -/
theorem setCodec_e_via_arrayCodec (c : Codec) (vs : List Value) :
    (setCodec c).e (.set vs)
      = ((arrayCodec c).e (.arr vs)).bind
          (fun a => match a with | .l as => asWireSet as | _ => none) := by
  simp only [setCodec, arrayCodec]
  cases traverse c.e vs <;> rfl

/-- **The model's wire sets are ordered.** Two orderings of one set read to two *different*
    values, so `ker p` is equality here — where §2 of the calculus says the quotient
    collapses precisely because "two orderings of one set are distinct attributes reading
    to one value". -/
theorem set_p_order_sensitive :
    (setCodec stringCodec).p (.ss ["a", "b"])
      ≠ (setCodec stringCodec).p (.ss ["b", "a"]) := by
  simp [setCodec, stringCodec, traverse]

/-- …and on the write side too: two orderings of one value are two attributes. -/
theorem set_e_order_sensitive :
    (setCodec stringCodec).e (.set [.str "a", .str "b"])
      ≠ (setCodec stringCodec).e (.set [.str "b", .str "a"]) := by
  simp [setCodec, stringCodec, traverse, asWireSet, strPayloads, sC]

/-- Duplicates survive as well, which `℘⁺fin` does not permit. -/
theorem set_e_keeps_duplicates :
    (setCodec stringCodec).e (.set [.str "a", .str "a"]) = some (.ss ["a", "a"]) := by
  simp [setCodec, stringCodec, traverse, asWireSet, strPayloads, sC]

/-! ### Fixing `set`: what (R) allows, and what it forbids

`Value.set` is a list and §1's `SS` is `℘⁺fin`, so the model admits orderings and duplicates
the domain does not. Repairing that is constrained from the start, and the constraint is
worth stating before any design: **`e` cannot normalise.**

(R) is `retract : c.e t = some a → c.p a = some t` — retraction to the *same* value, not to
an agreeing one. So if two orderings of one set both write, they must write *different*
attributes: a codec collapsing them would owe one attribute two readings
(`retract_forbids_insensitive_e`), and the same argument kills duplicate-collapsing on the
write side (`retract_forbids_dedup_e`).

What is allowed is the other half. `Carrier` asks only `dom(e) ⊆ T`, not equality, so `e`
may *refuse* the non-canonical representatives while `T` keeps holding them. And nothing
constrains `p` to be injective — it is a quotient by design (§2). So the repair is forced
into one shape:

* `e` accepts exactly one representative per set — the payload-sorted, duplicate-free one —
  and refuses the rest.
* `p` normalises, so every ordering of a wire set reads to that one value.

Which is exactly §2's sentence, made true: *two orderings of one set are distinct attributes
reading to one value*. It is currently false only because the model never picked a
representative.

The canonicity test lives on the **payloads**, not on values: `asWireSet` already has
`List String`, `List Numeral` and `List Bytes` in hand, all with decidable orders, so no
order on `Value` — and none on the axiomatized `Double` — is needed. -/

/-- **`e` cannot be order-insensitive.** (R) is retraction to the *same* value, not to an
    agreeing one, so if two orderings of a set both write, they write different attributes.
    A codec whose `e` collapsed them would have to read that one attribute back as two
    values. -/
theorem retract_forbids_insensitive_e {c : Codec} (h : LawfulCore c)
    {x y : Value} (hne : x ≠ y) {a : Attr}
    (h1 : c.e (.set [x, y]) = some a) (h2 : c.e (.set [y, x]) = some a) : False := by
  have r1 := h.retract h1
  have r2 := h.retract h2
  rw [r1] at r2
  simp at r2
  exact hne r2.1

/-- The same argument kills duplicate-collapsing on the write side. -/
theorem retract_forbids_dedup_e {c : Codec} (h : LawfulCore c)
    {x : Value} {a : Attr}
    (h1 : c.e (.set [x]) = some a) (h2 : c.e (.set [x, x]) = some a) : False := by
  have r1 := h.retract h1
  have r2 := h.retract h2
  rw [r1] at r2
  simp at r2

/-! ### The reference, checked against the model

`docs/dynamo-datatypes.md` is the official datatype reference. Most of §1 survives it
exactly — `Numeral.WF`'s 38 digits and `-130 … 125` exponent range are the documented
bounds; binary compares unsigned; empty strings and empty binary are permitted, empty lists
and maps are permitted, empty sets are not, and the model already refuses the last.

Two things do not survive, and they are the same defect at two members.

**`SS`/`NS`/`BS`** — *"Each value within a set must be unique. The order of the values within
a set is not preserved."* Recorded above.

**`M`** — *"A map type attribute can store an **unordered** collection of name-value
pairs."* The model's `M` is a `List (Name × Attr)`, so two orderings of one map are two
attributes (`record_p_order_sensitive`, `record_e_order_sensitive`), and a repeated key is
writable (`record_e_keeps_duplicate_keys`), which no map has.

This one is sharper than the set case for two reasons. First, the model already *states* the
intent elsewhere: `Agree` at `M` is lookup-based, comparing by key and ignoring order — so
the two halves of the model disagree with each other, not merely with the reference. Second,
maps cannot be repaired by typing. `Finset String` is admissible at `SS` because the element
type is concrete; `Finset (Name × Attr)` is rejected by the kernel exactly as `Finset Value`
is, the element type being the one under declaration. So `M` needs the well-formedness route
on **both** sides — unique keys, canonically ordered — which is what `Wire.canon` provides,
keyed by the name. -/

/-- The reference: *"A map type attribute can store an **unordered** collection of
    name-value pairs."* The model's `M` is a `List (Name × Attr)`, so two orderings of one
    map are two attributes — the same defect as `SS`/`NS`/`BS`, one level up. -/
theorem record_p_order_sensitive :
    (recordCodec stringCodec).p (.m [("a", .s "x"), ("b", .s "y")])
      ≠ (recordCodec stringCodec).p (.m [("b", .s "y"), ("a", .s "x")]) := by
  simp [recordCodec, stringCodec, decPair, traverse]

/-- …and on the write side. -/
theorem record_e_order_sensitive :
    (recordCodec stringCodec).e (.map [("a", .str "x"), ("b", .str "y")])
      ≠ (recordCodec stringCodec).e (.map [("b", .str "y"), ("a", .str "x")]) := by
  simp [recordCodec, stringCodec, encPair, traverse]

/-- And a map may carry a repeated key, which no map has. -/
theorem record_e_keeps_duplicate_keys :
    ((recordCodec stringCodec).e (.map [("a", .str "x"), ("a", .str "y")])).isSome = true := by
  simp [recordCodec, stringCodec, encPair, traverse]

end
end Calculus
