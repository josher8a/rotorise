import Calculus.Equations
import Calculus.Soundness
import Calculus.Discharge

/-!
# §6's "Do not hold" table, refuted

Nine rows of §6 assert that a rewrite *fails*, and none was machine-checked — the most
suspicious remaining surface, given that mechanizing §5's *positive* discharger claims
refuted three of them.

They are stated here against `denote`, which is what makes them readable: a claim about
`≡` is a claim about `T`, `μ`, `e` and `p` together, and until the denotation lost its
fuel every such statement carried a budget that had nothing to do with the equation.

A note on what refuting one of these means. `Codec.Equiv` is §6's `≡` — same held set,
same member, `e` and `p` agreeing *where both are defined*. So the cheapest honest
refutation is usually a held-set separation: one side holds a value the other does not.
That is stronger than an `e`/`p` disagreement would be, because `≡` deliberately tolerates
a shrinking domain but never a differing `T`.

§2's independence claim is here too, and for the same reason: it is a claim that something
*fails*, so its evidence is a counter-model and not a proof.
-/

namespace Calculus

/-! ## §2's four laws are independent

§2 asserts "The four are independent" and offers no witness. Independence *is* a family of
counter-models — for each law, a codec satisfying the other three and failing that one — so
the claim was four objects, and four objects were what the specification did not have.

They are stated at `Codec`, not at `Term`, which is what makes this independence rather than
a remark about the terms that happen to exist: a law the language cannot violate is still a
law the definition does not imply. Each is as small as `𝔸` allows — a pair of partial
functions on strings, `T` everything, and a member named only where the law needs one.

The `cM` case is the one worth reading twice. (W) and (MP) both constrain members, and it is
tempting to take one for a special case of the other. `cM` declares no member at all, so (W)
holds for the only reason it can hold without saying anything, and (MP) fails regardless. Its
three positive halves are exactly `LawfulCore` — which is not a coincidence but the same
residue `legacy` leaves (§5), arriving from the other direction. -/

/-- **(R) fails alone.** Every string is written to one attribute, so the write forgets which
    string it was; nothing else notices. -/
def cR : Codec where
  T := fun _ => True
  μ := some Member.S
  e := fun v => (match v with | .str _ => some (.s "x") | _ => none)
  p := fun a => (match a with | .s "x" => some (.str "a") | _ => none)

/-- `cR` loses the value: `"b"` is written and `"a"` is read back. -/
theorem cR_notR : ¬ (∀ {t a}, cR.e t = some a → cR.p a = some t) := by
  intro h; have := @h (.str "b") (.s "x") rfl; simp [cR] at this
/-- …but everything readable re-encodes. -/
theorem cR_C : ∀ {a t}, cR.p a = some t → (cR.e t).isSome := by
  intro a t h; cases a <;> simp [cR] at h; split at h <;> simp_all [cR]; subst_vars; rfl
/-- …the declared member is the only one written. -/
theorem cR_W : ∀ {μ}, cR.μ = some μ → ∀ {t a}, cR.e t = some a → a.member = μ := by
  intro μ hμ t a h; cases t <;> simp [cR] at h hμ; subst h; subst hμ; rfl
/-- …and a read re-written lands on the attribute it was read from. Losing the *value* is
    not losing the *member*, which is the distance between (R) and (MP). -/
theorem cR_MP : ∀ {a t a'}, cR.p a = some t → cR.e t = some a' → Agree a' a := by
  intro a t a' hp he; cases a <;> simp [cR] at hp; split at hp <;> simp_all [cR]; subst_vars
  simp [cR] at he; subst_vars; exact .s _ _

/-- **(C) fails alone.** Reads every `S`, writes only `"a"` — so `p` escapes `dom(e)`. -/
def cC : Codec where
  T := fun _ => True
  μ := some Member.S
  e := fun v => (match v with | .str "a" => some (.s "a") | _ => none)
  p := fun a => (match a with | .s s => some (.str s) | _ => none)

/-- `cC` retracts on the one value it writes. -/
theorem cC_R : ∀ {t a}, cC.e t = some a → cC.p a = some t := by
  intro t a h; cases t <;> simp [cC] at h; split at h <;> simp_all [cC]; subst_vars; rfl
/-- …and names its member. -/
theorem cC_W : ∀ {μ}, cC.μ = some μ → ∀ {t a}, cC.e t = some a → a.member = μ := by
  intro μ hμ t a h; cases t <;> simp [cC] at h hμ; split at h <;> simp_all [cC]; subst_vars; rfl
/-- …but `"b"` is readable and not writable, which is (C) and nothing else. -/
theorem cC_notC : ¬ (∀ {a t}, cC.p a = some t → (cC.e t).isSome) := by
  intro h; have := @h (.s "b") (.str "b") rfl; simp [cC] at this
/-- …and (MP) survives, being quantified over what `e` actually returns. -/
theorem cC_MP : ∀ {a t a'}, cC.p a = some t → cC.e t = some a' → Agree a' a := by
  intro a t a' hp he; cases a <;> simp [cC] at hp; subst hp; simp [cC] at he
  split at he <;> simp_all; subst he; exact .s _ _

/-- **(W) fails alone.** A bijection on its domain that declares `μ = S` and writes `"z"` to
    `BOOL`. The pair is as well behaved as a pair can be; only the *declaration* is a lie. -/
def cW : Codec where
  T := fun _ => True
  μ := some Member.S
  e := fun v =>
    (match v with | .str s => if s = "z" then some (.bool true) else some (.s s) | _ => none)
  p := fun a =>
    (match a with
     | .bool true => some (.str "z")
     | .s s => if s = "z" then none else some (.str s)
     | _ => none)

/-- `cW` writes `⟨BOOL, true⟩` while naming `S`. -/
theorem cW_notW : ¬ (∀ {μ}, cW.μ = some μ → ∀ {t a}, cW.e t = some a → a.member = μ) := by
  intro h; have := @h .S rfl (.str "z") (.bool true) (by simp [cW]); simp [Attr.member] at this
/-- …and is a retraction all the same: the two branches are disjoint by construction. -/
theorem cW_R : ∀ {t a}, cW.e t = some a → cW.p a = some t := by
  intro t a h
  cases t <;> simp only [cW] at h
  case str s =>
    split at h
    · next hz => subst hz; cases h; rfl
    · next hz => cases h; simp only [cW]; rw [if_neg hz]
  all_goals exact absurd h (by simp)
/-- …everything readable re-encodes… -/
theorem cW_C : ∀ {a t}, cW.p a = some t → (cW.e t).isSome := by
  intro a t h
  cases a <;> simp only [cW] at h
  case s s =>
    split at h
    · exact absurd h (by simp)
    · next hz => cases h; simp only [cW]; rw [if_neg hz]; rfl
  case bool b =>
    cases b
    · exact absurd h (by simp)
    · cases h; simp only [cW]; rfl
  all_goals exact absurd h (by simp)
/-- …and no read re-written changes a stored member. (W) constrains the *declaration*
    against `ran(e)`; (MP) constrains `ran(e)` against `dom(p)`, and only the first is
    broken here. -/
theorem cW_MP : ∀ {a t a'}, cW.p a = some t → cW.e t = some a' → Agree a' a := by
  intro a t a' hp he
  cases a <;> simp only [cW] at hp
  case s s =>
    split at hp
    · exact absurd hp (by simp)
    · next hz => cases hp; simp only [cW] at he; rw [if_neg hz] at he; cases he; exact .s _ _
  case bool b =>
    cases b
    · exact absurd hp (by simp)
    · cases hp; simp only [cW] at he; simp at he; subst he; exact .bool _ _
  all_goals exact absurd hp (by simp)

/-- **(MP) fails alone.** Declares no member, and reads `⟨BOOL, true⟩` back as a string it
    writes to `S` — so a stored `BOOL` becomes an `S` on the way through. -/
def cM : Codec where
  T := fun _ => True
  μ := none
  e := fun v => (match v with | .str s => some (.s s) | _ => none)
  p := fun a =>
    (match a with | .s s => some (.str s) | .bool true => some (.str "z") | _ => none)

/-- `cM` retracts. -/
theorem cM_R : ∀ {t a}, cM.e t = some a → cM.p a = some t := by
  intro t a h; cases t <;> simp [cM] at h; subst h; rfl
/-- …and everything readable re-encodes. -/
theorem cM_C : ∀ {a t}, cM.p a = some t → (cM.e t).isSome := by
  intro a t h
  cases a <;> simp only [cM] at h
  case s s => cases h; rfl
  case bool b =>
    cases b
    · exact absurd h (by simp)
    · cases h; rfl
  all_goals exact absurd h (by simp)
/-- (W) holds vacuously, which is the only way a `⊤`-membered codec can satisfy it. -/
theorem cM_W : ∀ {μ}, cM.μ = some μ → ∀ {t a}, cM.e t = some a → a.member = μ := by
  intro μ hμ; exact absurd hμ (by simp [cM])
/-- So the three that hold are exactly `LawfulCore` — the same residue `legacy` leaves. -/
theorem cM_core : LawfulCore cM := ⟨cM_R, cM_C, cM_W⟩
/-- …and (MP) is what is left to break: `⟨BOOL, true⟩` reads as `"z"` and re-writes to
    `⟨S, "z"⟩`, which `Agree` does not relate. -/
theorem cM_notMP : ¬ (∀ {a t a'}, cM.p a = some t → cM.e t = some a' → Agree a' a) := by
  intro h; have := @h (.bool true) (.str "z") (.s "z") rfl rfl; cases this

/-! ## `lazy(γ) ≢ γ(∗)`

§6 singles this row out: "the pair is the same and the μ is not … `≡` compares the index
too, and this is the row where that matters." The model says exactly that — the two
denotations differ in `μ` alone, and `Codec.Equiv` sees it. -/

/-- The pairs really are the same: `lazy` changes only the index. -/
theorem lazy_e_eq (t : Term) : (denote (.lazy t)).e = (denote t).e := rfl

theorem lazy_p_eq (t : Term) : (denote (.lazy t)).p = (denote t).p := rfl

/-- And the index really does differ: `lazy` concludes `⊤`, `string` names `S`. -/
theorem lazy_μ_ne : (denote (.lazy .string)).μ ≠ (denote .string).μ := by
  simp [denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, stringCodec]

/-- §6: `lazy(γ) ≢ γ(∗)` — refuted on the member index, with the pair identical. -/
theorem not_equiv_lazy : ¬ Codec.Equiv (denote (.lazy .string)) (denote .string) :=
  fun h => lazy_μ_ne h.member

/-! ## `union(c₁ … cₙ) ≢ union(c₁ … cₙ, c)`

Not closed under extension. The held set grows, so `≡` fails before (D) or (K) are even
consulted — which is the stronger statement, since §6 justifies the row by well-formedness
and the model shows it fails for a more basic reason. -/

theorem not_equiv_union_extend :
    ¬ Codec.Equiv (denote (.union [.string])) (denote (.union [.string, .boolean])) := by
  intro h
  have hb := (h.heldSet (.bool true)).mpr
  simp [denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, optionSems, denoteμs, optionSemOf, specOf, OptionSem.byAttempt,
        altCodec, select, stringCodec, booleanCodec] at hb

/-! ## `union(array(c₁), array(c₂)) ≢ array(union(c₁, c₂))`

§6: "Left: a sequence homogeneous in one option. Right: a sequence of either,
elementwise." The witness is the shortest heterogeneous sequence. -/

/-- `["A", "B"]` is an array of either literal, but homogeneous in neither. -/
theorem not_equiv_union_array :
    ¬ Codec.Equiv
        (denote (.union [.array (.literal .string (.of "A" ∅)), .array (.literal .string (.of "B" ∅))]))
        (denote (.array (.union [.literal .string (.of "A" ∅), .literal .string (.of "B" ∅)]))) := by
  intro h
  have hv := (h.heldSet (.arr [.str "A", .str "B"])).mpr
  simp [denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, optionSems, denoteμs, optionSemOf, specOf, OptionSem.byAttempt,
        altCodec, select, arrayCodec, literalCodec, baseCodec, Codec.restrict, inL,
        stringCodec, NEFinset.of, HLit] at hv

/-! ## `tuple(c₁ … cₙ, rest(c))` is neither a tuple nor an array of unions

§6: "a fixed head with a repeating tail is neither: a tuple has no tail and an array has
no head." Both halves separate on held sets, and each witness is the shortest one that
isolates the missing feature. -/

/-- Against the plain tuple: a second element the tail accepts and the tuple has no
    position for. -/
theorem not_equiv_tupleTail_tuple :
    ¬ Codec.Equiv (denote (.tuple [.string] (some .string)))
                  (denote (.tuple [.string] none)) := by
  intro h
  have hv := (h.heldSet (.arr [.str "a", .str "b"])).mp
  -- `simp`'s classical push-neg turned this into an existential and pulled
  -- `Classical.choice` in with it; the implication is the constructive shape.
  simp only [denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denoteList, denoteOpt, tupleCodec, align, stringCodec,
    Option.map_some', List.all_cons, List.all_nil, Bool.and_true, Bool.true_and,
    Option.some.injEq, exists_eq_left', List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hv
  exact absurd (hv (by rintro p (rfl | rfl) <;> exact ⟨_, rfl⟩))
    (by rintro ⟨ps, hps, -⟩; simp at hps)

/-- Against the array: the empty sequence, which an array holds and a fixed head cannot. -/
theorem not_equiv_tupleTail_array :
    ¬ Codec.Equiv (denote (.tuple [.string] (some .string)))
                  (denote (.array (.union [.string]))) := by
  intro h
  have hv := (h.heldSet (.arr [])).mpr
  simp [denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, denoteList, denoteOpt, optionSems, denoteμs, optionSemOf, specOf,
        OptionSem.byAttempt, altCodec, select, tupleCodec, align, arrayCodec, stringCodec] at hv

/-! ## `refine(held(c, f, g), q) ≢ held(refine(c, q), f, g)`

§6: "the refinement applies on opposite sides of the iso, so `q` is a subset of different
sets." The model makes that literal — one held set says `q v`, the other says `q (f v)`. -/

/-- A constant-on-strings iso half, and a predicate that tells `"A"` from `"B"`. -/
def isoF : Value → Value
  | .str _ => .str "A"
  | v => v

def predA : Value → Bool
  | .str s => s == "A"
  | _ => false

/-- At `"B"`: the outer refinement rejects it, the inner one never sees it — `f` has
    already replaced it with `"A"`. -/
theorem not_equiv_refine_held :
    ¬ Codec.Equiv (denote (.refine (.held .string isoF id) predA))
                  (denote (.held (.refine .string predA) isoF id)) := by
  intro h
  have hv := (h.heldSet (.str "B")).mpr
  simp [denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, Codec.through, Codec.restrict, stringCodec, isoF, predA] at hv

/-! ## `legacy(c, r)` breaks (MP), and `e ∘ p ≢ id`

Two rows, one witness. (MP) is *member* agreement (`≼`), so a migration only breaks it by
reading an attribute of one member into a value that writes another — which is precisely
what a member-changing migration is, and precisely why §6 says a `legacy` attribute cannot
be an index key.

Note that a value-changing `r` would *not* refute (MP): `Agree.s x y` holds for any two
strings. The row needs the member to move, and that is worth knowing before writing a
migration one believes is safe. -/

/-- Reads an `N` into a string value — so the re-encoding lands on `S`. -/
def migrateNtoS : Attr → Option Value
  | .n _ => some (.str "x")
  | _ => none

theorem legacy_p_n : (denote (.legacy .string migrateNtoS)).p (.n (.of "1")) = some (.str "x") :=
  rfl

theorem legacy_e_x : (denote (.legacy .string migrateNtoS)).e (.str "x") = some (.s "x") :=
  rfl

/-- §6: `legacy(c, r)` breaks (MP). The migration reads `N` and writes `S`. -/
theorem legacy_breaks_MP : ¬ Lawful (denote (.legacy .string migrateNtoS)) := by
  intro h
  have hag := h.agree legacy_p_n legacy_e_x
  cases hag

/-- §6: `e ∘ p ≢ id` — equality holds only on `Can(c)`, and this attribute is off it. -/
theorem e_comp_p_ne_id :
    ∃ (c : Codec) (a : Attr) (v : Value), c.p a = some v ∧ c.e v ≠ some a :=
  ⟨denote (.legacy .string migrateNtoS), .n (.of "1"), .str "x", legacy_p_n, by
    rw [legacy_e_x]; intro hc; exact nomatch hc⟩

/-! ## `optional(optional(c))` — not derivable, by construction

This row needs no theorem, and could not have one: it is enforced by the syntax. `Field`
(Term.lean) has three constructors — `req`, `optional`, `fallback` — and every one takes a
`Term`. None takes a `Field`, so `optional(optional(c))` cannot be written down, and
neither can `optional(fallback(c, v))` or `fallback(optional(c), v)`.

That is the stratification §4 of the specification asks for, and the model gets it from
the type rather than from a side condition — which is the stronger place to get it. It is
also `C3`'s sharpest test for a port (§5): a library that lets `optional(c)` appear where a
codec is expected has no corresponding `Term`, and the mapping fails there rather than
quietly succeeding.
-/

/-! ## `set(union(c₁, c₂))` — not derivable, and now not writable

§6: "the premise on `set` demands a member, and a union of options writing different
members has none." This was the one row that is a claim about the *judgement* rather than
about `≡`, and the model settled it from the member index alone: `(set)` concluded
`some μS`, `μSyn` of a heterogeneous union is `none`, and `typed_μSyn` said the two must
agree. ~~not_typed_set_union~~ was that proof.

**It cannot be stated any more.** `Term.set` takes a `SetBase`, so
`set(union(string, boolean))` is not a term — the elaborator refuses it where a derivation
used to fail. That is the same closure `HeldSet.lean` records for `strSet ∅` and the map
defect for duplicate keys: a witness that something is excluded is worth having exactly
while it is expressible, and when the type takes over the exclusion the witness goes with
it. What §6's row asked of the judgement is now the constructor's argument type.

The union on its own is unaffected, and is still worth exhibiting: it was never the union
that was underivable, only the `set` above it. -/

/-- The union on its own is fine — it is the `set` above it that has no derivation. -/
theorem typed_union_string_boolean :
    Typed (.union [.string, .boolean])
      (HUnion [fun v => ∃ s, v = .str s, fun v => ∃ b, v = .bool b]) none :=
  .union (.cons .string (.cons .boolean .nil)) <| by
    -- (D): neither held set contains the other — a string is never a boolean.
    rw [DIncomp, List.pairwise_cons]
    refine ⟨fun T hT => ?_, List.pairwise_singleton _ _⟩
    rw [List.mem_singleton] at hT; subst hT
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨b, hb⟩ := h (.str "") ⟨"", rfl⟩; exact nomatch hb
    · obtain ⟨s, hs⟩ := h (.bool true) ⟨true, rfl⟩; exact nomatch hs

/-! ## What `≡` cannot see about associativity

`Equations.equiv_altCodec_assoc` proves §6's associativity row *unconditionally* — no (D),
no (K), no (U). That is not a contradiction of §6's hedge; it is a fact about `≡`.

`≡` requires `e` and `p` to agree only where **both** are defined. At an input where the
nested option is ambiguous, the left side's inner union fails and the outer one resolves
anyway, while the right side sees three admitting options and refuses. One side defined,
the other not — so `≡` asks nothing, and the row holds.

The behavioural difference is real all the same, and it is exactly what §6's prose
describes. Here it is, so that the unconditional row is not mistaken for a licence to
rewrite across the two forms freely: at `"A"`, with `string` outside and two copies of
`literal("A")` nested inside, the left encodes and the right refuses.

Both terms violate (U), which is the point — §6 conditions the row on precisely that, and
the model shows the condition is needed for *interchangeability*, not for `≡`. -/

/-- Left: the outer union resolves, because the inner one has already failed. -/
theorem assoc_left_e :
    (denote (.union [.string, .union [.literal .string (.of "A" ∅), .literal .string (.of "A" ∅)]])).e (.str "A")
      = some (.s "A") := by
  simp [denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, optionSems, denoteμs, optionSemOf, specOf, OptionSem.byAttempt,
        altCodec, select, stringCodec, literalCodec, baseCodec, Codec.restrict, inL]

/-- Right: three options admit, so the union refuses globally. -/
theorem assoc_right_e :
    (denote (.union [.string, .literal .string (.of "A" ∅), .literal .string (.of "A" ∅)])).e (.str "A") = none := by
  simp [denote, denote, denoteList_eq, denoteOpt_eq, optionSems_eq, denoteμs_eq_map, denoteTagged_eq, optionSems, denoteμs, optionSemOf, specOf, OptionSem.byAttempt,
        altCodec, select, stringCodec, literalCodec, baseCodec, Codec.restrict, inL]

/-- The two associativity forms are `≡` but not interchangeable: one writes where the
    other refuses. §6's (D)/(K)/(U) hedge is about this, not about `≡`. -/
theorem not_eq_altCodec_assoc :
    ∃ (l r : Term) (v : Value) (a : Attr),
      (denote l).e v = some a ∧ (denote r).e v = none :=
  ⟨.union [.string, .union [.literal .string (.of "A" ∅), .literal .string (.of "A" ∅)]],
   .union [.string, .literal .string (.of "A" ∅), .literal .string (.of "A" ∅)],
   .str "A", .s "A", assoc_left_e, assoc_right_e⟩

/-! ## `≡` is not transitive

Not a row of §6 — a property of §6 itself. `Codec.Equiv.refl` and `Codec.Equiv.symm` are
proved in `Equations.lean`; `trans` is absent, and this is why. §6 is presented as an
equational theory and the conformance standard asks a port to exhibit `Codec.Equiv`, so a
reader is entitled to assume the relation chains. It does not,
and nothing said so.

The mechanism is the tolerance the header above describes: `≡` compares `e` and `p` only
*where both are defined*, so a codec whose `e` is nowhere defined agrees with everything.
Put one in the middle and it relates two codecs that disagree outright.

The witness is at `Codec` level, which is the level §6's relation lives at — `Equations.lean`
states all thirty-six of its rows about combinators, never about `denote`. What keeps it
from being a degenerate artifact is that **all three codecs are `Lawful` and on their
`Carrier`**, and the held set is not empty: the failure survives every hypothesis §2
imposes on a pair. It uses only the licence §2 grants explicitly — a term's `e` does
whatever it likes off `T` — and the fact that `Carrier` bounds `dom(e)` by `T` without
requiring the converse.

What is *not* settled here: whether `≡` chains when both ends are `denote` of derivable
terms. The middle codec below holds `null` and writes nothing, and no derivable term does
that, so this refutation does not decide the restricted question. -/

/-- Writes `null` as an `S`, and nothing else — lawful, and on its carrier. -/
def cA : Codec :=
  { T := fun v => v = .null, μ := none,
    e := fun v => match v with | .null => some (.s "A") | _ => none,
    p := fun a => match a with | .s _ => some .null | _ => none }

/-- The same, writing `S "B"`. It disagrees with `cA` on the one value both write. -/
def cB : Codec :=
  { T := fun v => v = .null, μ := none,
    e := fun v => match v with | .null => some (.s "B") | _ => none,
    p := fun a => match a with | .s _ => some .null | _ => none }

/-- The middle: the same held set, and no `e` or `p` anywhere. Every law of §2 is vacuous
    on it, which is exactly what makes it `≡` to both of the others. -/
def cMid : Codec :=
  { T := fun v => v = .null, μ := none, e := fun _ => none, p := fun _ => none }

theorem lawful_cA : Lawful cA where
  retract := by intro t a he; cases t <;> simp_all [cA]; subst_vars; rfl
  canon := by intro a t hp; cases a <;> simp_all [cA]; subst_vars; rfl
  writes := by intro μ hμ; exact nomatch hμ
  agree := by
    intro a t a' hp he
    cases a
    case s v =>
      obtain rfl : t = .null := by simpa [cA] using hp.symm
      obtain rfl : a' = .s "A" := by simpa [cA] using he.symm
      exact .s _ _
    all_goals simp [cA] at hp

theorem lawful_cB : Lawful cB where
  retract := by intro t a he; cases t <;> simp_all [cB]; subst_vars; rfl
  canon := by intro a t hp; cases a <;> simp_all [cB]; subst_vars; rfl
  writes := by intro μ hμ; exact nomatch hμ
  agree := by
    intro a t a' hp he
    cases a
    case s v =>
      obtain rfl : t = .null := by simpa [cB] using hp.symm
      obtain rfl : a' = .s "B" := by simpa [cB] using he.symm
      exact .s _ _
    all_goals simp [cB] at hp

theorem lawful_cMid : Lawful cMid := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [cMid]

theorem carrier_cA : Carrier cA where
  domE := by intro v a he; cases v <;> simp_all [cA]
  ranP := by intro a v hp; cases a <;> simp_all [cA]

theorem carrier_cB : Carrier cB where
  domE := by intro v a he; cases v <;> simp_all [cB]
  ranP := by intro a v hp; cases a <;> simp_all [cB]

theorem carrier_cMid : Carrier cMid := by
  refine ⟨?_, ?_⟩ <;> intros <;> simp_all [cMid]

/-- The two hops. Both hold because `cMid` never writes and never reads, so the two
    agreement clauses of `≡` have no input to disagree on. -/
theorem equiv_cA_cMid : Codec.Equiv cA cMid := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩ <;> intros <;> simp_all [cMid]

theorem equiv_cMid_cB : Codec.Equiv cMid cB := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩ <;> intros <;> simp_all [cMid]

/-- And the composite fails: both write `null`, to different attributes. -/
theorem not_equiv_cA_cB : ¬ Codec.Equiv cA cB := by
  intro h
  have hab : (Attr.s "A") = Attr.s "B" := h.writes (v := .null) rfl rfl
  simp at hab

/-- **§6's `≡` is not transitive**, and the counterexample is lawful throughout. -/
theorem not_equiv_trans :
    ¬ ∀ c d e, Codec.Equiv c d → Codec.Equiv d e → Codec.Equiv c e :=
  fun h => not_equiv_cA_cB (h _ _ _ equiv_cA_cMid equiv_cMid_cB)

/-! ## `(literal-N)`'s `ℓ ⊆ D`, and what it refuses

`(number)` gates on §1's numeral domain, which is what the rule always claimed. `(literal-N)`
now carries the same bound as a premise — the second and last of the two places the bound was
forced outward, and the one that needed the specification amended rather than the model
corrected.

It is the same set on both rules: **what DynamoDB accepts**, `Numeral.WF` of the text the
value is written as. `literal` writes its values' own digits, so a double outside that domain
would be written to an attribute `𝔸` has no point for, which is the one thing a term may
never do. The premise sits beside `hne` and `hnd` because it is the same kind of fact: data
the term owns, decidable at the declaration.

What follows is what it buys and what it refuses. The refutations are conditional on a double
outside `D` existing: `Double` is axiomatized with the shortest-text round trip and nothing
else, and whether IEEE-754 has a value DynamoDB will not store is a fact about IEEE that the
model deliberately does not assert. It was not a hypothetical — the shipped `literal(NaN)`
wrote `⟨N, "NaN"⟩` and `literal(1e400)` wrote `⟨N, "Infinity"⟩`, both reachable with no cast,
which is what settled the question the conditional leaves open. -/

/-- **`literal-N` is a refinement of `number`, with nothing asked for.** This took
    `hD : ∀ d ∈ ls.1, Numeral.WF d.toDec = true` and its docstring said the premise "is the
    whole of what the prism needed". It still is; it is now `WFDouble`'s, so the containment
    holds of every `ls` there is. -/
theorem literalN_sub_number (ls : NEFinset WFDouble) :
    ∀ v, (literalCodec .number ls).T v → numberCodec.T v := by
  rintro v ⟨d, hd, rfl⟩
  exact ⟨d.1, rfl, d.2⟩

/-! ### §3's `(literal)` at `number`, with `ℓᵢ ∈ T` dropped

§3's premise line is `⊢ g : T ⇝ μ, g ground; ℓ₁ … ℓₙ ∈ T`, and at `g = number` the base's held
set *is* §1's `D` — so the rule already requires `ℓ ⊆ D`. **The two witnesses below show that
premise is load-bearing: drop it and (B) fails.** That needs an ungated prism to be stated
about, not an ungated `Term`, which `GroundKind.number.Carrier = WFDouble` no longer admits.

`literalNRule` is that prism. It is deliberately not a `Term`, no constructor builds it, and it
exists only to carry the two theorems below — which is why it is here and not in
`Combinators.lean` with the codecs the calculus uses. -/

/-- `(literal)`'s prism at base `number`, over an ungated `ℓ` — §3's, not ours. -/
noncomputable def inLNRule (ls : NEFinset Double) : Value → Bool
  | .num d => decide (d ∈ ls.1)
  | _ => false

/-- §3's `(literal)` at `number`, transcribed with the rule's ungated `ℓ`. Not a `Term`. -/
noncomputable def literalNRule (ls : NEFinset Double) : Codec :=
  { numberCodec.restrict (inLNRule ls) with T := fun v => ∃ d ∈ ls.1, v = .num d }

/-- **Drop `ℓᵢ ∈ T` and `(literal)` stops refining `number`.** An alternative outside `D` is
    held by the ungated prism and not by `number`, so the two disagree about a value one of them
    claims to hold. This is what the rule's premise buys, stated where it can be stated. -/
theorem not_literalNRule_sub_number {d : Double} (hw : Numeral.WF d.toDec = false) :
    ¬ ∀ v, (literalNRule (.of d ∅)).T v → numberCodec.T v := by
  intro h
  obtain ⟨d', hd', hwd⟩ := h (.num d) ⟨d, NEFinset.mem_of d ∅, rfl⟩
  cases Value.num.inj hd'
  rw [hw] at hwd
  exact nomatch hwd

/-- **And the consequence is not confined to the held sets.** With `Attr.n` carrying §1's
    `Numerals`, §3's `(literal-N)` cannot *write* a numeral `𝔸` has no point for — `e` refuses,
    there being no such attribute. What it does is **hold** the value, since the rule's `T` is
    its ungated `ℓ`.

    So the failure is *"`T ⊄ dom(e)`"* — **(B)**, and exactly the sentence `(literal-N)` needs
    `ℓ ⊆ D` to stop being able to say. -/
theorem literalNRule_holds_what_it_cannot_write {d : Double}
    (hw : Numeral.WF d.toDec = false) :
    (literalNRule (.of d ∅)).T (.num d) ∧ (literalNRule (.of d ∅)).e (.num d) = none := by
  refine ⟨⟨d, NEFinset.mem_of d ∅, rfl⟩, ?_⟩
  show (if inLNRule (.of d ∅) (.num d) = true then numberCodec.e (.num d) else none) = none
  rw [if_pos (by simp [inLNRule, NEFinset.mem_of]), numberCodec_e_num,
    dif_neg (by rw [hw]; exact Bool.noConfusion)]

/-! Two theorems here quantified over a derivation only to read `hD` back off it. With the gate
in the carrier the derivation argument is unused, `#lint_calculus` reported it, and the honest
response to that report is deletion rather than a sanction entry: one became `fun d _ => d.2`
and the other became `literalN_sub_number` above, which needs no premise. A theorem whose
hypothesis has become decoration is a description that has stopped describing.

A third said no numeric literal outside `D` is derivable. `.of d ∅` needs `d : WFDouble`, so
there is no such term to quantify over — "this cannot be derived" and "this cannot be written"
are one claim, and only the theorem can go stale. -/

/-! ## `decimal` before its held set was narrowed

`survivesStore_decimalCodec` shows that gating on `Numeral.Stored` discharges `η ⊆ ker p`.
This is the other half: the codec that gated on `Numeral.WF` instead — §1's *whole* numeral
grammar, which is what the implementation shipped — does not, and the witness is a form
DynamoDB was measured to normalise.

Without this the narrowing reads as a precaution. With it, it is the only option: `WF` admits
`"1.500"`, the store returns `"1.5"`, `decimal`'s `ker p` is equality (`ker_decimalCodec`),
and (R) through the store fails on a value the codec claimed to hold. -/

/-- `decimal`, gated on §1's grammar rather than on what the store hands back — which is
    now **`wfDecimalCodec`, the base `decimal` actually refines**. Since `Attr.n` carries
    `WF`, there is no wider text-side numeric codec to invent, so this refutation says
    something about the base itself rather than about a codec built for the purpose.

    Note its read is *total*: `WF` is the carrier now, so the gate that used to sit on `p`
    has nothing left to reject. That is the whole asymmetry `decimal` adds — `Stored` is a
    strictly smaller set than `WF`, and only the smaller one survives the store. -/
theorem wfDecimalCodec_e_str (s : String) :
    wfDecimalCodec.e (.str s) = if h : Numeral.WF s then some (.n ⟨s, h⟩) else none := rfl

theorem wfDecimalCodec_p_n (x : WFNumeral) : wfDecimalCodec.p (.n x) = some (.str x.1) := rfl

/-- `"1.500"` is one of the forms `stored_rejects_denormal` records the store rewriting, and
    the un-narrowed codec claims to hold it. -/
theorem can_wfDecimalCodec_denormal : Can wfDecimalCodec (.n (.of "1.500")) :=
  ⟨.str "1.500", by rw [wfDecimalCodec_e_str, dif_pos (by decide : Numeral.WF "1.500" = true)]; rfl⟩

/-- **The un-narrowed `decimal` does not survive the store.** Any `η` that normalises
    `"1.500"` — which is what DynamoDB was measured to do — falls outside its `ker p`. -/
theorem not_survivesStore_wfDecimalCodec {η : Attr → Attr}
    (hη : η (.n (.of "1.500")) = .n (.of "1.5")) : ¬ SurvivesStore wfDecimalCodec η := by
  intro h
  have hk : wfDecimalCodec.p (η (.n (.of "1.500"))) = wfDecimalCodec.p (.n (.of "1.500")) :=
    h _ can_wfDecimalCodec_denormal
  rw [hη, wfDecimalCodec_p_n, wfDecimalCodec_p_n] at hk
  exact absurd (Value.str.inj (Option.some.inj hk)) (by decide)

/-- And (R) through the store fails outright: the value is written, the store rewrites the
    attribute, and the codec reads back something else — the shape of the shipped defect. -/
theorem not_retract_through_store_wfDecimalCodec {η : Attr → Attr}
    (hη : η (.n (.of "1.500")) = .n (.of "1.5")) :
    wfDecimalCodec.e (.str "1.500") = some (.n (.of "1.500")) ∧
      wfDecimalCodec.p (η (.n (.of "1.500"))) ≠ some (.str "1.500") := by
  refine ⟨by rw [wfDecimalCodec_e_str, dif_pos (by decide : Numeral.WF "1.500" = true)]; rfl, ?_⟩
  rw [hη, wfDecimalCodec_p_n]
  intro hk
  exact absurd (Value.str.inj (Option.some.inj hk)) (by decide)

/-! ## `union(opaque, c)` is never separable

Not one of §6's nine rows — a row §5 never wrote, and the reason it did not is that
`opaque` looked like a term with nothing to say. `κ (.opaq _)` is `⊤` and, before `adm`
was made to ask `opaqCodecω`, so were `adm (.opaq _)` and `admA (.opaq _)`. ~~SepV~~
offers exactly two routes — a disjoint kind or a disjoint admissible set — and ~~SepA~~
two more — a distinct named member or a disjoint admissible set. A `⊤` on every one of
the four is not a weak option; it is an **absorbing** one, in the sense `unknown | T` is
absorbing in TypeScript.

The absorption survives the semantic row, and the statements below say so in the form
the row leaves them. They used to read "for every option that admits anything", on the
strength of `adm (.opaq true) = ⊤`; that blanket is gone, because `adm` now asks the
codec and `opaqCodecω` at a lossy policy still refuses `.num d` when
`Numeral.WF (Double.toDec d)` fails — and `Double.toDec` is an axiom with no such
guarantee (`Domain.lean`). What is true, and is all the refutation ever used, is: **an
`opaque` never separates from an option they both admit.** The kind and member disjuncts
are still structurally unavailable, so a single shared value or attribute is enough.

Stated in both argument orders, because `List.Pairwise` asks the question one way round
and the fact does not care; and at both policies, because the policy bit plays no part —
what does the work is that `κ` and `μSyn` are `⊤` at an `opaque` whatever it writes. -/
