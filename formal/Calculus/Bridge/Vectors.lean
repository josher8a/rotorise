import Calculus.Dynamo.Lang.Denote

/-!
# The vector checker — how a generated test vector becomes a kernel-checked theorem

The correspondence between this model and `src/` was stated as prose: the TypeScript codec is
claimed to compute what `denote` denotes. Nothing checked it.
This file is the Lean half of the bridge that does: a generator emits one line per vector,
and the *kernel* — not a tactic, not `#eval` — decides whether the model agrees.

Three facts about this development force the shape of what follows, and each of them killed
an easier design first.

**`denote` is `noncomputable`, but the kernel still evaluates it.** The map attribute carries
a function on its key set, so no compiler can run `denote`; `#eval` and
`native_decide` are both unavailable, and that is not a toolchain gap to be worked around.
What *is* available is definitional unfolding: `(denote t).e v = some a` is `rfl` for every
term form, including deeply nested ones, in well under a second. So a vector is checked by
being *typechecked*, and the certificate is a theorem rather than a program's output.

**Except through `M`.** A *whole-structure* equation on a map result is not `rfl`, and
`with_unfolding_all` does not rescue it. `Attr.m` carries `f : {k // k ∈ keys} → Attr`, and
the closure the codec builds is pointwise equal to a written one without being
*definitionally* equal to it — the funext gap, which no amount of unfolding closes. The key
set reduces, each value at a key reduces, `isSome` reduces; only the assembled function does
not. That single fact is why this file exists: `aeq` never compares two functions, it
compares them **at every key of a key set that it has already checked is the same set**, and
that is a decidable proposition the kernel is happy to settle.

**No `DecidableEq Attr`, and none is coming.** the host's decidable equality is an axiom (so it does not
reduce) and `.m`'s function field is not comparable anyway. `aeq` is therefore not a
decision procedure that was derived and then used; it is written by hand, and its agreement
with equality is *proved* (`aeq_same`, `aeq_differ`) rather than assumed. Those two theorems
are what a vector line is worth: without them `check … = .same` says only that a function
this file defines returned a constructor.

## Fuel, and why the verdict is three-valued

`aeq` recurses on a `Nat` of fuel. That is not a modelling choice about `Attr` — `Attr` is
finite and a structural comparator would terminate — it is what makes the function
*structurally* recursive on its first argument, and only a structurally recursive function
reduces in the kernel. A well-founded definition elaborates to `WellFounded.fix`, which does
not unfold by `rfl`; this was measured, not assumed, and it is also why the list case is a
separate first-order helper (`zipAll`) taking the comparator as a parameter rather than a
`mutual` block: `mutual` fell back to well-founded recursion and every `rfl` below stopped
working.

Fuel that runs out is then the obvious hole. A `Bool` comparator has nowhere to put
"exhausted" but `false`, which is the same answer it gives for "these differ" — so a vector
file could be *silently* certifying nothing, and a negative vector could be passing for the
wrong reason. `Verdict` has a third constructor instead, and the honesty is a theorem in
both directions:

* `.same` implies the two attributes are equal — fuel never manufactures agreement;
* `.differ` implies they are *not* equal — so a negative vector is a real refutation, not a
  budget failure;
* `.exhausted` implies nothing, and cannot be mistaken for either, because a generated line
  reads `= .same` or `= .differ` and an exhausted run matches neither. A vector file that
  under-fuels does not pass quietly; it fails to compile.

`.differ` deliberately dominates `.exhausted` when the two meet (`Verdict.and`): a witnessed
difference at one field is a difference in the whole attribute whatever happened at its
siblings, and weakening that to `.exhausted` would throw away a refutation the checker
already holds.
-/

namespace Calculus

/-! ## The verdict -/

/-- The result of comparing two attributes under a fuel budget. Three-valued because two of
    the answers are claims — `aeq_same` and `aeq_differ` discharge them — and the third is
    the admission that no claim is being made. -/
inductive Verdict where
  /-- Equal, and provably so. -/
  | same
  /-- Unequal, and provably so — a witnessed difference, not a failure to look. -/
  | differ
  /-- The budget ran out before the question was settled. Carries no information. -/
  | exhausted
deriving DecidableEq, Repr

/-- Combining the verdicts of two components. `differ` wins over `exhausted`: one component
    known to differ settles the whole, regardless of what a sibling ran out of fuel on.
    `exhausted` wins over `same` for the mirror reason — every component must be settled
    before agreement is. -/
def Verdict.and : Verdict → Verdict → Verdict
  | .differ, _ => .differ
  | _, .differ => .differ
  | .exhausted, _ => .exhausted
  | _, .exhausted => .exhausted
  | .same, .same => .same

@[simp] theorem Verdict.and_same_iff {u v : Verdict} :
    Verdict.and u v = .same ↔ u = .same ∧ v = .same := by
  cases u <;> cases v <;> simp [Verdict.and]

@[simp] theorem Verdict.and_differ_iff {u v : Verdict} :
    Verdict.and u v = .differ ↔ u = .differ ∨ v = .differ := by
  cases u <;> cases v <;> simp [Verdict.and]

/-! ## Set equality, constructively

`DecidableEq (Finset α)` exists in mathlib and is **classical** — `#print axioms` on
`decide (ka = kb)` reports `Classical.choice`, which is outside this development's sanctioned
base (`Axioms.lean`). The comparator would have inherited it and every vector line with it.
That is the axiom guard doing exactly the job the audit records it for, and the repair is the
comparator's, not the guard's.

Two bounded membership quantifiers are decidable without choice — `Finset.decidableMem` is
clean — and mutual inclusion is equality by `Finset.Subset.antisymm`, which is clean too. So
set equality is written out rather than synthesised, and this is the only place in the file
where the obvious spelling was the wrong one. -/

/-- Finset equality by mutual inclusion: decidable, choice-free, and reducible.

    A cheaper spelling exists and was measured rather than argued about: `a.card = b.card`
    together with `b ⊆ a` is equality by `Finset.eq_of_subset_of_card_le`, which is also
    choice-free, and it runs about 25% faster on the key comparison — roughly 30 ms against
    40 ms per two-field object vector. It is not taken, because that 10 ms sits inside a
    64 ms vector whose cost is the object codec's, and mutual inclusion is the form whose
    soundness is one `Finset.Subset.antisymm` with nothing to get wrong. Recorded so the
    trade is a decision rather than an oversight. -/
def fsetEq {α : Type} [DecidableEq α] (a b : Finset α) : Bool :=
  decide (∀ k ∈ a, k ∈ b) && decide (∀ k ∈ b, k ∈ a)

@[simp] theorem fsetEq_iff {α : Type} [DecidableEq α] {a b : Finset α} :
    fsetEq a b = true ↔ a = b := by
  constructor
  · intro h
    simp only [fsetEq, Bool.and_eq_true, decide_eq_true_eq] at h
    exact Finset.Subset.antisymm h.1 h.2
  · rintro rfl; simp [fsetEq]

/-! ## The two first-order helpers

Both take the comparator as a parameter. That keeps `aeq` a single non-mutual definition
recursing on fuel alone, which is what the kernel needs, and it lets each helper's soundness
be proved once against an abstract comparator instead of once per recursive call site. -/

/-- Componentwise comparison of two lists. Length mismatch is a `differ` and not an
    `exhausted`: two lists of different lengths are unequal, and `zipWith` would have
    silently truncated the longer one into agreement. -/
def zipAll (r : Attr → Attr → Verdict) : List Attr → List Attr → Verdict
  | [], [] => .same
  | a :: as, b :: bs => Verdict.and (r a b) (zipAll r as bs)
  | _, _ => .differ

/-- The value a map holds at a name, as a total function — `none` off the key set.

    This is the whole trick of the `M` case. Two maps are compared by looking each of them
    up at the same *name*, never by handing the kernel their two closures; `mapAt` is what
    turns "the function field" into a first-order question the kernel can answer. -/
def mapAt (keys : Finset Name) (f : {k // k ∈ keys} → Attr) (k : Name) : Option Attr :=
  if h : k ∈ keys then some (f ⟨k, h⟩) else none

/-- One row of a map comparison: the two lookups at one name, compared. -/
def mapRow (r : Attr → Attr → Verdict)
    (ka : Finset Name) (fa : {k // k ∈ ka} → Attr)
    (kb : Finset Name) (fb : {k // k ∈ kb} → Attr) (k : Name) : Verdict :=
  match mapAt ka fa k, mapAt kb fb k with
  | some x, some y => r x y
  | none, none => .same
  | _, _ => .differ

/-! ## The comparator -/

/-- Structural comparison of two attributes under a fuel budget.

    The `M` case is two `Finset`-bounded quantifiers — decidable, hence reducible — rather
    than a verdict folded over the key set. Three details of it were each forced by
    something, and none of them is arbitrary.

    **Why an `∃` at all, when `¬∀` would do.** The `differ` branch has to produce a
    *witness*: `aeq_differ` needs a key at which the two maps disagree in order to
    contradict an assumed equality. Extracting one from the negation of the `∀` is
    `not_forall`, which is classical, and `Classical.choice` is outside this development's
    sanctioned base (`Axioms.lean`). So the existential is asked directly.

    **Why the `∀` is asked first.** Both quantifiers traverse the key set, so the order
    decides which answer pays for one pass and which pays for two. A generated vector file
    is overwhelmingly `.same` lines, and putting the `∃` first made every one of them pay
    the `differ` search before the agreement it was going to find anyway: measured at 50
    two-field object vectors, 32.5 s the wrong way round against 4.0 s this way. The
    exhausted case still pays both, which is the right thing to make expensive.

    **Why both quantifiers range over `kb` and not `ka`.** This is the difference between a
    usable checker and an unusable one, and it is invisible in the statement — `fsetEq ka kb`
    has already been checked, so the two ranges are extensionally the same set and the proof
    below does not care which is written. The kernel cares a great deal. `ka` is the key set
    the *codec* produced, buried under `funImage` and `carriedCodec`, and forcing the
    `Finset.decidableBAll` instance to whnf through it re-does that work at every step of the
    traversal; `kb` is the key set the *vector* wrote, a literal that reduces at once.
    Quantifying over the expected side rather than the computed one took a two-field object
    vector from 630 ms to 64 ms — a 10× that no change to the comparator's logic could have
    bought, since the logic is identical. The rule for anyone extending this: **iterate over
    the written side, look up on the computed side.** -/
def aeq : Nat → Attr → Attr → Verdict
  | 0, _, _ => .exhausted
  | _ + 1, .s a,    .s b    => if a = b then .same else .differ
  | _ + 1, .n a,    .n b    => if a.1 = b.1 then .same else .differ
  | _ + 1, .b a,    .b b    => if a = b then .same else .differ
  | _ + 1, .bool a, .bool b => if a = b then .same else .differ
  | _ + 1, .null,   .null   => .same
  | _ + 1, .ss a,   .ss b   => if fsetEq a.1 b.1 then .same else .differ
  | _ + 1, .ns a,   .ns b   => if fsetEq a.1 b.1 then .same else .differ
  | _ + 1, .bs a,   .bs b   => if fsetEq a.1 b.1 then .same else .differ
  | n + 1, .l a,    .l b    => zipAll (aeq n) a b
  | n + 1, .m ka fa, .m kb fb =>
      if fsetEq ka kb then
        if decide (∀ k ∈ kb, mapRow (aeq n) ka fa kb fb k = .same) then .same
        else if decide (∃ k ∈ kb, mapRow (aeq n) ka fa kb fb k = .differ) then .differ
        else .exhausted
      else .differ
  | _ + 1, _, _ => .differ

/-- What a generated vector line compares: the codec's `Option Attr` against the expected
    one. `some`/`none` mismatch is a `differ` — a codec that refused where the vector
    expects a write is a genuine disagreement, not an unsettled question. -/
def check (n : Nat) : Option Attr → Option Attr → Verdict
  | none, none => .same
  | some a, some b => aeq n a b
  | _, _ => .differ

/-! ## What a vector line is worth

These are the theorems that turn `check 8 x y = .same := rfl` from a fact about `aeq` into a
fact about the codec. Both directions are proved; neither is assumed. -/

/-- `zipAll` against an abstract comparator, both directions at once. -/
theorem zipAll_sound {r : Attr → Attr → Verdict}
    (hs : ∀ x y, r x y = .same → x = y) (hd : ∀ x y, r x y = .differ → x ≠ y) :
    ∀ as bs : List Attr,
      (zipAll r as bs = .same → as = bs) ∧ (zipAll r as bs = .differ → as ≠ bs)
  | [], [] => ⟨fun _ => rfl, fun h => by simp [zipAll] at h⟩
  | [], _ :: _ => ⟨fun h => by simp [zipAll] at h, fun _ h => by cases h⟩
  | _ :: _, [] => ⟨fun h => by simp [zipAll] at h, fun _ h => by cases h⟩
  | a :: as, b :: bs => by
    obtain ⟨ihs, ihd⟩ := zipAll_sound hs hd as bs
    refine ⟨fun h => ?_, fun h heq => ?_⟩
    · simp only [zipAll, Verdict.and_same_iff] at h
      exact congrArg₂ List.cons (hs _ _ h.1) (ihs h.2)
    · obtain ⟨ha, hb⟩ := List.cons.inj heq
      simp only [zipAll, Verdict.and_differ_iff] at h
      exact h.elim (fun h' => hd _ _ h' ha) (fun h' => ihd h' hb)

/-- **The certificate.** `.same` is equality and `.differ` is disequality; `.exhausted`
    claims nothing, and is the only thing fuel exhaustion can produce. -/
theorem aeq_sound : ∀ (n : Nat) (a b : Attr),
    (aeq n a b = .same → a = b) ∧ (aeq n a b = .differ → a ≠ b)
  | 0, _, _ => ⟨fun h => by simp [aeq] at h, fun h => by simp [aeq] at h⟩
  | n + 1, a, b => by
    have ihs : ∀ x y, aeq n x y = .same → x = y := fun x y => (aeq_sound n x y).1
    have ihd : ∀ x y, aeq n x y = .differ → x ≠ y := fun x y => (aeq_sound n x y).2
    match a, b with
    | .s _, .s _ | .b _, .b _ | .bool _, .bool _ =>
      refine ⟨fun h => ?_, fun h hq => ?_⟩ <;>
        · simp only [aeq] at h; split at h <;> simp_all
    | .n _, .n _ | .ss _, .ss _ | .ns _, .ns _ | .bs _, .bs _ =>
      refine ⟨fun h => ?_, fun h hq => ?_⟩ <;>
        · simp only [aeq] at h; split at h <;> simp_all [Subtype.ext_iff]
    | .null, .null => exact ⟨fun _ => rfl, fun h => by simp [aeq] at h⟩
    | .l as, .l bs =>
      obtain ⟨hs, hd⟩ := zipAll_sound ihs ihd as bs
      exact ⟨fun h => congrArg Attr.l (hs h), fun h hq => hd h (by cases hq; rfl)⟩
    | .m ka fa, .m kb fb =>
      refine ⟨fun h => ?_, fun h hq => ?_⟩
      · -- `.same`: the key sets are equal and every key's values agree, so `funext` closes
        -- the gap that defeated `rfl` in the first place
        simp only [aeq] at h
        split at h
        · next hk =>
          obtain rfl := fsetEq_iff.mp hk
          split at h
          · next hall =>
            have hall' := of_decide_eq_true hall
            refine congrArg (Attr.m ka) (funext fun k => ?_)
            have := hall' k.1 k.2
            simp only [mapRow, mapAt, dif_pos k.2] at this
            exact ihs _ _ this
          · split at h <;> exact absurd h (by simp)
        · exact absurd h (by simp)
      · simp only [aeq] at h
        split at h
        · next hk =>
          obtain rfl := fsetEq_iff.mp hk
          split at h
          · exact absurd h (by simp)
          · split at h
            · next hex =>
              obtain ⟨k, hk, hrow⟩ := of_decide_eq_true hex
              cases hq
              simp only [mapRow, mapAt, dif_pos hk] at hrow
              exact ihd _ _ hrow rfl
            · exact absurd h (by simp)
        · next hk => cases hq; exact hk (by simp [fsetEq])
    | .s _, .n _ | .s _, .b _ | .s _, .bool _ | .s _, .null | .s _, .ss _ | .s _, .ns _
    | .s _, .bs _ | .s _, .l _ | .s _, .m _ _
    | .n _, .s _ | .n _, .b _ | .n _, .bool _ | .n _, .null | .n _, .ss _ | .n _, .ns _
    | .n _, .bs _ | .n _, .l _ | .n _, .m _ _
    | .b _, .s _ | .b _, .n _ | .b _, .bool _ | .b _, .null | .b _, .ss _ | .b _, .ns _
    | .b _, .bs _ | .b _, .l _ | .b _, .m _ _
    | .bool _, .s _ | .bool _, .n _ | .bool _, .b _ | .bool _, .null | .bool _, .ss _
    | .bool _, .ns _ | .bool _, .bs _ | .bool _, .l _ | .bool _, .m _ _
    | .null, .s _ | .null, .n _ | .null, .b _ | .null, .bool _ | .null, .ss _
    | .null, .ns _ | .null, .bs _ | .null, .l _ | .null, .m _ _
    | .ss _, .s _ | .ss _, .n _ | .ss _, .b _ | .ss _, .bool _ | .ss _, .null
    | .ss _, .ns _ | .ss _, .bs _ | .ss _, .l _ | .ss _, .m _ _
    | .ns _, .s _ | .ns _, .n _ | .ns _, .b _ | .ns _, .bool _ | .ns _, .null
    | .ns _, .ss _ | .ns _, .bs _ | .ns _, .l _ | .ns _, .m _ _
    | .bs _, .s _ | .bs _, .n _ | .bs _, .b _ | .bs _, .bool _ | .bs _, .null
    | .bs _, .ss _ | .bs _, .ns _ | .bs _, .l _ | .bs _, .m _ _
    | .l _, .s _ | .l _, .n _ | .l _, .b _ | .l _, .bool _ | .l _, .null
    | .l _, .ss _ | .l _, .ns _ | .l _, .bs _ | .l _, .m _ _
    | .m _ _, .s _ | .m _ _, .n _ | .m _ _, .b _ | .m _ _, .bool _ | .m _ _, .null
    | .m _ _, .ss _ | .m _ _, .ns _ | .m _ _, .bs _ | .m _ _, .l _ =>
      exact ⟨fun h => by simp [aeq] at h, fun _ hq => by cases hq⟩

/-- `.same` is equality. This is the theorem a generated vector line is cashed against. -/
theorem aeq_same {n : Nat} {a b : Attr} (h : aeq n a b = .same) : a = b := (aeq_sound n a b).1 h

/-- `.differ` is disequality — so a negative vector refutes rather than merely fails. -/
theorem aeq_differ {n : Nat} {a b : Attr} (h : aeq n a b = .differ) : a ≠ b :=
  (aeq_sound n a b).2 h

/-- The wrapper's `.same`, lifted to the `Option Attr` a codec actually returns. -/
theorem check_same {n : Nat} {x y : Option Attr} (h : check n x y = .same) : x = y := by
  match x, y with
  | none, none => rfl
  | some a, some b => exact congrArg some (aeq_same h)
  | none, some _ | some _, none => simp [check] at h

/-- And its `.differ`. -/
theorem check_differ {n : Nat} {x y : Option Attr} (h : check n x y = .differ) : x ≠ y := by
  match x, y with
  | none, none => simp [check] at h
  | some a, some b => exact fun hq => aeq_differ h (Option.some.inj hq)
  | none, some _ | some _, none => exact fun hq => by cases hq

/-! ## The `Value` twin, for the read side

`aeq` compares `Attr`. A read-side vector's answer is a `Value`, and `Value.map` carries a
function exactly as `Attr.m` does — so a read resolution landing on a map met the same funext
gap `aeq` was built to cross, with nothing to cross it. Five of the union bridge's read pairs
were recorded as unstatable for want of this.

**The construction transfers unchanged**, which is the result rather than the code: the same
fuel, the same `Verdict`, the same two-quantifier `map` case, the same `mapAt` trick of comparing
two closures only at names. Both rules `aeq`'s docstring records carry over and are not
re-derived here — ask the `∀` before the `∃`, and **quantify over the expected side's key set,
not the codec's**, which is the 10× nobody can see in the statement.

**No row differs now, and that is the change.** `veq` answered `.exhausted` at `.num` and
`.numSet` while the numeric carrier was a host type whose equality was an axiom. `N` is carried
exactly, so both rows compare the numeral text and decide, as every other leaf row does.
`Verdict.exhausted` keeps its meaning, "carries no information", and the fuel row is what answers
it. The read pairs this file once recorded as unstatable for want of a numeric comparison are not
re-measured here. -/

def zipAllV (r : Value → Value → Verdict) : List Value → List Value → Verdict
  | [], [] => .same
  | a :: as, b :: bs => Verdict.and (r a b) (zipAllV r as bs)
  | _, _ => .differ

def mapAtV (keys : Finset Name) (f : {k // k ∈ keys} → Value) (k : Name) : Option Value :=
  if h : k ∈ keys then some (f ⟨k, h⟩) else none

def mapRowV (r : Value → Value → Verdict)
    (ka : Finset Name) (fa : {k // k ∈ ka} → Value)
    (kb : Finset Name) (fb : {k // k ∈ kb} → Value) (k : Name) : Verdict :=
  match mapAtV ka fa k, mapAtV kb fb k with
  | some x, some y => r x y
  | none, none => .same
  | _, _ => .differ

/-- `aeq`'s construction over `Value`. Every leaf row decides. The two numeric rows compare the
    numeral text, where they answered `.exhausted` through a host's axiomatised equality. -/
def veq : Nat → Value → Value → Verdict
  | 0, _, _ => .exhausted
  | _ + 1, .str a,  .str b  => if a = b then .same else .differ
  | _ + 1, .bool a, .bool b => if a = b then .same else .differ
  | _ + 1, .bin a,  .bin b  => if a = b then .same else .differ
  | _ + 1, .null,   .null   => .same
  -- **`N` DECIDES now.** Its equality is the numeral text's, so these two rows stopped being
  -- `.exhausted` when the carrier stopped being a host type.
  | _ + 1, .num a,  .num b  => if a.1 = b.1 then .same else .differ
  | _ + 1, .numSet a, .numSet b => if fsetEq a.1 b.1 then .same else .differ
  | _ + 1, .strSet a, .strSet b => if fsetEq a.1 b.1 then .same else .differ
  | _ + 1, .binSet a, .binSet b => if fsetEq a.1 b.1 then .same else .differ
  | n + 1, .arr a,  .arr b  => zipAllV (veq n) a b
  | n + 1, .map ka fa, .map kb fb =>
      if fsetEq ka kb then
        if decide (∀ k ∈ kb, mapRowV (veq n) ka fa kb fb k = .same) then .same
        else if decide (∃ k ∈ kb, mapRowV (veq n) ka fa kb fb k = .differ) then .differ
        else .exhausted
      else .differ
  | _ + 1, _, _ => .differ

def vcheck (n : Nat) : Option Value → Option Value → Verdict
  | none, none => .same
  | some a, some b => veq n a b
  | _, _ => .differ

/-- `zipAll_sound` over `Value`: an elementwise verdict lifts to the list, both ways. -/
theorem zipAllV_sound {r : Value → Value → Verdict}
    (hs : ∀ x y, r x y = .same → x = y) (hd : ∀ x y, r x y = .differ → x ≠ y) :
    ∀ as bs : List Value,
      (zipAllV r as bs = .same → as = bs) ∧ (zipAllV r as bs = .differ → as ≠ bs)
  | [], [] => ⟨fun _ => rfl, fun h => by simp [zipAllV] at h⟩
  | [], _ :: _ => ⟨fun h => by simp [zipAllV] at h, fun _ h => by cases h⟩
  | _ :: _, [] => ⟨fun h => by simp [zipAllV] at h, fun _ h => by cases h⟩
  | a :: as, b :: bs => by
    obtain ⟨ihs, ihd⟩ := zipAllV_sound hs hd as bs
    refine ⟨fun h => ?_, fun h heq => ?_⟩
    · simp only [zipAllV, Verdict.and_same_iff] at h
      exact congrArg₂ List.cons (hs _ _ h.1) (ihs h.2)
    · obtain ⟨ha, hb⟩ := List.cons.inj heq
      simp only [zipAllV, Verdict.and_differ_iff] at h
      exact h.elim (fun h' => hd _ _ h' ha) (fun h' => ihd h' hb)

/-- **The certificate**, `aeq_sound`'s twin: `.same` is equality and `.differ` is disequality.
    `.exhausted` says nothing, which is what the fuel row answers and why it needs no case
    here: a row that never says `.same` has nothing to prove. -/
theorem veq_sound : ∀ (n : Nat) (a b : Value),
    (veq n a b = .same → a = b) ∧ (veq n a b = .differ → a ≠ b)
  | 0, _, _ => ⟨fun h => by simp [veq] at h, fun h => by simp [veq] at h⟩
  | n + 1, a, b => by
    have ihs : ∀ x y, veq n x y = .same → x = y := fun x y => (veq_sound n x y).1
    have ihd : ∀ x y, veq n x y = .differ → x ≠ y := fun x y => (veq_sound n x y).2
    match a, b with
    | .str _, .str _ | .bin _, .bin _ | .bool _, .bool _ =>
      refine ⟨fun h => ?_, fun h hq => ?_⟩ <;>
        · simp only [veq] at h; split at h <;> simp_all
    | .num _, .num _ =>
      refine ⟨fun h => ?_, fun h hq => ?_⟩ <;>
        · simp only [veq] at h; split at h <;> simp_all [Subtype.ext_iff]
    | .strSet _, .strSet _ | .binSet _, .binSet _ | .numSet _, .numSet _ =>
      refine ⟨fun h => ?_, fun h hq => ?_⟩ <;>
        · simp only [veq] at h; split at h <;> simp_all [Subtype.ext_iff]
    | .null, .null => exact ⟨fun _ => rfl, fun h => by simp [veq] at h⟩
    | .arr as, .arr bs =>
      obtain ⟨hs, hd⟩ := zipAllV_sound ihs ihd as bs
      exact ⟨fun h => congrArg Value.arr (hs h), fun h hq => hd h (by cases hq; rfl)⟩
    | .map ka fa, .map kb fb =>
      refine ⟨fun h => ?_, fun h hq => ?_⟩
      · simp only [veq] at h
        split at h
        · next hk =>
          obtain rfl := fsetEq_iff.mp hk
          split at h
          · next hall =>
            have hall' := of_decide_eq_true hall
            refine congrArg (Value.map ka) (funext fun k => ?_)
            have := hall' k.1 k.2
            simp only [mapRowV, mapAtV, dif_pos k.2] at this
            exact ihs _ _ this
          · split at h <;> exact absurd h (by simp)
        · exact absurd h (by simp)
      · simp only [veq] at h
        split at h
        · next hk =>
          obtain rfl := fsetEq_iff.mp hk
          split at h
          · exact absurd h (by simp)
          · split at h
            · next hex =>
              obtain ⟨k, hk, hrow⟩ := of_decide_eq_true hex
              cases hq
              simp only [mapRowV, mapAtV, dif_pos hk] at hrow
              exact ihd _ _ hrow rfl
            · exact absurd h (by simp)
        · next hk => cases hq; exact hk (by simp [fsetEq])
    -- every mismatched pair. The cross product is spelled out because both halves need the
    -- CONSTRUCTORS: `simp [veq]` reduces the row only when it knows them, and `cases hq`
    -- discharges `a = b` only when they visibly differ. A `| _, _ =>` catch-all typechecks
    -- as a pattern and then proves neither half.
    | .str _, .num _ | .str _, .bool _ | .str _, .bin _
    | .str _, .null | .str _, .strSet _ | .str _, .numSet _
    | .str _, .binSet _ | .str _, .arr _ | .str _, .map _ _
    | .num _, .str _ | .num _, .bool _ | .num _, .bin _
    | .num _, .null | .num _, .strSet _ | .num _, .numSet _
    | .num _, .binSet _ | .num _, .arr _ | .num _, .map _ _
    | .bool _, .str _ | .bool _, .num _ | .bool _, .bin _
    | .bool _, .null | .bool _, .strSet _ | .bool _, .numSet _
    | .bool _, .binSet _ | .bool _, .arr _ | .bool _, .map _ _
    | .bin _, .str _ | .bin _, .num _ | .bin _, .bool _
    | .bin _, .null | .bin _, .strSet _ | .bin _, .numSet _
    | .bin _, .binSet _ | .bin _, .arr _ | .bin _, .map _ _
    | .null, .str _ | .null, .num _ | .null, .bool _
    | .null, .bin _ | .null, .strSet _ | .null, .numSet _
    | .null, .binSet _ | .null, .arr _ | .null, .map _ _
    | .strSet _, .str _ | .strSet _, .num _ | .strSet _, .bool _
    | .strSet _, .bin _ | .strSet _, .null | .strSet _, .numSet _
    | .strSet _, .binSet _ | .strSet _, .arr _ | .strSet _, .map _ _
    | .numSet _, .str _ | .numSet _, .num _ | .numSet _, .bool _
    | .numSet _, .bin _ | .numSet _, .null | .numSet _, .strSet _
    | .numSet _, .binSet _ | .numSet _, .arr _ | .numSet _, .map _ _
    | .binSet _, .str _ | .binSet _, .num _ | .binSet _, .bool _
    | .binSet _, .bin _ | .binSet _, .null | .binSet _, .strSet _
    | .binSet _, .numSet _ | .binSet _, .arr _ | .binSet _, .map _ _
    | .arr _, .str _ | .arr _, .num _ | .arr _, .bool _
    | .arr _, .bin _ | .arr _, .null | .arr _, .strSet _
    | .arr _, .numSet _ | .arr _, .binSet _ | .arr _, .map _ _
    | .map _ _, .str _ | .map _ _, .num _ | .map _ _, .bool _
    | .map _ _, .bin _ | .map _ _, .null | .map _ _, .strSet _
    | .map _ _, .numSet _ | .map _ _, .binSet _ | .map _ _, .arr _ =>
      exact ⟨fun h => by simp [veq] at h, fun _ hq => by cases hq⟩

/-- `.same` lifted to the `Option Value` a codec's read actually returns — what a generated
    read-resolution line is cashed against, as `check_same` is on the write side. -/
theorem vcheck_same {n : Nat} {x y : Option Value} (h : vcheck n x y = .same) : x = y := by
  match x, y with
  | none, none => rfl
  | some a, some b => exact congrArg some ((veq_sound n a b).1 h)
  | none, some _ | some _, none => simp [vcheck] at h

/-! ## The shape of a generated vector

A vector file emitted by the generator is one line per case, and reads:

```
theorem v0 : check 8 ((denote t).e v) (some a) = .same := rfl
```

`rfl` does the work: the kernel unfolds `denote`, runs the codec on the value, and settles
the comparison — no tactic, no `decide` on an undecidable equality, no compiled code. The
line's content is then recovered with `check_same v0 : (denote t).e v = some a`.

A rejection vector is the same line with `.differ`, and by `check_differ` it is a proof that
the codec does *not* write that attribute. Under-fuelling either one produces `.exhausted`,
which matches neither right-hand side and fails the build — the property that makes the
generator's fuel argument something the kernel checks rather than something a reader trusts.

### Fuel, and what a vector line costs

Fuel is a bound on *attribute* depth, not on the term's, and `check n` is exact once `n`
exceeds the nesting of the written attribute — `Attr.nesting` in `Nesting.lean` counts the
same layers. A generator should emit the depth it knows it built plus one; there is no reason
to be generous, because **fuel is not a cost driver**. The comparator's work is bounded by
the attribute, not by the budget: 50 two-field object vectors cost the same at `check 2` as
at `check 8`, to within noise. Over-fuelling is free, and under-fuelling fails loudly, so a
generator that cannot compute the depth should pass a constant.

What a vector costs is what the *codec* costs, and that is a fact about `denote`, not about
this file. Marginal cost per vector, over the ~0.8 s import baseline:

| vector | ms |
|---|---|
| scalar (`string`) | ~5 |
| two-element `array` | ~8 |
| two-key `record` | ~19 |
| one-field `object` | ~25 |
| two-field `object` | ~64 |
| `object` nested two deep | ~90 |

Linear in the number of vectors — 100 two-field object vectors cost the same per vector as
50 — so a file of a few hundred is seconds, not minutes, and the bridge is affordable in CI.

**One line per vector, never a batch.** Folding 200 vectors into a single `List.all` and one
`rfl` does not amortise anything and actively fails: it exceeds `maxHeartbeats` at 200000,
where the same 200 written out as separate lines compile in 19 s. Each `rfl` gets its own
heartbeat budget, and distinct vectors share no structure for a batch to exploit.

`number` can carry **positive** vectors now. `Value.num` carries a `WFNumeral`, which is a
`String` subtype carrying its own well-formedness proof, so a closed numeric value is one literal
and reduces like text. This paragraph recorded the opposite while the carrier was an axiom with no
closed terms, and `decimal` was named the numeric escape hatch for that reason. Whether the corpus
holds such a vector is a separate question, and this paragraph does not answer it. `Attr.n`'s row
compares the underlying text, which is the carrier's own equality.

**It has refusal vectors, and that took the impossibility being put in the right place.** A
refusal names the term and a value the term *rejects*, so it needs no inhabitant of the codec's
own carrier: `(denote Term.number).e (Value.str "x") = none` is `rfl`. `Term.number` is a closed
term and always was; the generator refused to emit it, on the ground that no value could be named
at it — true of an agreement, false of a refusal, and stated as a fact about the syntax. The
generator's own value emitter already reported the real impossibility, at `Value.num`, so moving
nothing and *deleting* the term-level refusal was the whole fix.

A numeric `literal` is the case that does not follow, and the contrast is the useful part:
`Term.literal GroundKind.number ls` needs `ls : NEFinset WFNumeral`, so **the term itself** has no
closed expression and no vector of either kind reaches it. Term-inexpressible and
value-inexpressible are two boundaries, and this file's old sentence had them as one.
-/

end Calculus
