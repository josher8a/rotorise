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

end
end Calculus
