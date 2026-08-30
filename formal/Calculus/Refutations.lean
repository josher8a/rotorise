import Calculus.Equations
import Calculus.Soundnessω

/-!
# §6's "Do not hold" table, refuted

Nine rows of §6 assert that a rewrite *fails*. Until now none was machine-checked, which
`docs/codec-formalization.md` §7 called "the most suspicious remaining surface" — given
that mechanizing §5's *positive* discharger claims refuted three of them.

They are stated here against `denoteω`, which is what makes them readable: a claim about
`≡` is a claim about `T`, `μ`, `e` and `p` together, and until the denotation lost its
fuel every such statement carried a budget that had nothing to do with the equation.

A note on what refuting one of these means. `Codec.Equiv` is §6's `≡` — same held set,
same member, `e` and `p` agreeing *where both are defined*. So the cheapest honest
refutation is usually a held-set separation: one side holds a value the other does not.
That is stronger than an `e`/`p` disagreement would be, because `≡` deliberately tolerates
a shrinking domain but never a differing `T`.
-/

namespace Calculus

/-! ## `lazy(γ) ≢ γ(∗)`

§6 singles this row out: "the pair is the same and the μ is not … `≡` compares the index
too, and this is the row where that matters." The model says exactly that — the two
denotations differ in `μ` alone, and `Codec.Equiv` sees it. -/

/-- The pairs really are the same: `lazy` changes only the index. -/
theorem lazy_e_eq (t : Term) : (denoteω (.lazy t)).e = (denoteω t).e := rfl

theorem lazy_p_eq (t : Term) : (denoteω (.lazy t)).p = (denoteω t).p := rfl

/-- And the index really does differ: `lazy` concludes `⊤`, `string` names `S`. -/
theorem lazy_μ_ne : (denoteω (.lazy .string)).μ ≠ (denoteω .string).μ := by
  simp [denoteω, stringCodec]

/-- §6: `lazy(γ) ≢ γ(∗)` — refuted on the member index, with the pair identical. -/
theorem not_equiv_lazy : ¬ Codec.Equiv (denoteω (.lazy .string)) (denoteω .string) :=
  fun h => lazy_μ_ne h.member

/-! ## `union(c₁ … cₙ) ≢ union(c₁ … cₙ, c)`

Not closed under extension. The held set grows, so `≡` fails before (D) or (K) are even
consulted — which is the stronger statement, since §6 justifies the row by well-formedness
and the model shows it fails for a more basic reason. -/

theorem not_equiv_union_extend :
    ¬ Codec.Equiv (denoteω (.union [.string])) (denoteω (.union [.string, .boolean])) := by
  intro h
  have hb := (h.heldSet (.bool true)).mpr
  simp [denoteω, denoteωOpts, denoteωMems, optionSemOf, specOf, OptionSem.byAttempt,
        altCodec, select, stringCodec, booleanCodec] at hb

/-! ## `union(array(c₁), array(c₂)) ≢ array(union(c₁, c₂))`

§6: "Left: a sequence homogeneous in one option. Right: a sequence of either,
elementwise." The witness is the shortest heterogeneous sequence. -/

/-- `["A", "B"]` is an array of either literal, but homogeneous in neither. -/
theorem not_equiv_union_array :
    ¬ Codec.Equiv
        (denoteω (.union [.array (.literalS ["A"]), .array (.literalS ["B"])]))
        (denoteω (.array (.union [.literalS ["A"], .literalS ["B"]]))) := by
  intro h
  have hv := (h.heldSet (.arr [.str "A", .str "B"])).mpr
  simp [denoteω, denoteωOpts, denoteωMems, optionSemOf, specOf, OptionSem.byAttempt,
        altCodec, select, arrayCodec, literalSCodec] at hv

/-! ## `tuple(c₁ … cₙ, rest(c))` is neither a tuple nor an array of unions

§6: "a fixed head with a repeating tail is neither: a tuple has no tail and an array has
no head." Both halves separate on held sets, and each witness is the shortest one that
isolates the missing feature. -/

/-- Against the plain tuple: a second element the tail accepts and the tuple has no
    position for. -/
theorem not_equiv_tupleTail_tuple :
    ¬ Codec.Equiv (denoteω (.tuple [.string] (some .string)))
                  (denoteω (.tuple [.string] none)) := by
  intro h
  have hv := (h.heldSet (.arr [.str "a", .str "b"])).mp
  simp [denoteω, denoteωL, denoteωO, tupleCodec, align, stringCodec] at hv
  obtain ⟨x, x1, hmem, hnT⟩ := hv
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hnT ⟨_, rfl⟩

/-- Against the array: the empty sequence, which an array holds and a fixed head cannot. -/
theorem not_equiv_tupleTail_array :
    ¬ Codec.Equiv (denoteω (.tuple [.string] (some .string)))
                  (denoteω (.array (.union [.string]))) := by
  intro h
  have hv := (h.heldSet (.arr [])).mpr
  simp [denoteω, denoteωL, denoteωO, denoteωOpts, denoteωMems, optionSemOf, specOf,
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
    ¬ Codec.Equiv (denoteω (.refine (.held .string isoF id) predA))
                  (denoteω (.held (.refine .string predA) isoF id)) := by
  intro h
  have hv := (h.heldSet (.str "B")).mpr
  simp [denoteω, Codec.through, Codec.restrict, stringCodec, isoF, predA] at hv

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

theorem legacy_p_n : (denoteω (.legacy .string migrateNtoS)).p (.n "1") = some (.str "x") :=
  rfl

theorem legacy_e_x : (denoteω (.legacy .string migrateNtoS)).e (.str "x") = some (.s "x") :=
  rfl

/-- §6: `legacy(c, r)` breaks (MP). The migration reads `N` and writes `S`. -/
theorem legacy_breaks_MP : ¬ Lawful (denoteω (.legacy .string migrateNtoS)) := by
  intro h
  have hag := h.agree legacy_p_n legacy_e_x
  cases hag

/-- §6: `e ∘ p ≢ id` — equality holds only on `Can(c)`, and this attribute is off it. -/
theorem e_comp_p_ne_id :
    ∃ (c : Codec) (a : Attr) (v : Value), c.p a = some v ∧ c.e v ≠ some a :=
  ⟨denoteω (.legacy .string migrateNtoS), .n "1", .str "x", legacy_p_n, by
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

/-! ## `set(union(c₁, c₂))` — not derivable

§6: "the premise on `set` demands a member, and a union of options writing different
members has none." This is the one row that is a claim about the *judgement* rather than
about `≡`, and the model settles it from the member index alone: `(set)` concludes
`some μS`, `μSyn` of a heterogeneous union is `none`, and `typed_μSyn` says the two must
agree.

Note it is not the union that is underivable — `union(string, boolean)` is perfectly well
typed at `⊤`. It is putting one under `set` that has no derivation, which is the
distinction §3's `⇝` column exists to draw. -/

theorem not_typed_set_union :
    ¬ ∃ T μ, Typed (.set (.union [.string, .boolean])) T μ := by
  rintro ⟨T, μ, h⟩
  cases h with
  | set h' hs =>
    have hμ := typed_μSyn h'
    simp [μSyn, μSynList, unanimous] at hμ

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
    (denoteω (.union [.string, .union [.literalS ["A"], .literalS ["A"]]])).e (.str "A")
      = some (.s "A") := by
  simp [denoteω, denoteωOpts, denoteωMems, optionSemOf, specOf, OptionSem.byAttempt,
        altCodec, select, stringCodec, literalSCodec]

/-- Right: three options admit, so the union refuses globally. -/
theorem assoc_right_e :
    (denoteω (.union [.string, .literalS ["A"], .literalS ["A"]])).e (.str "A") = none := by
  simp [denoteω, denoteωOpts, denoteωMems, optionSemOf, specOf, OptionSem.byAttempt,
        altCodec, select, stringCodec, literalSCodec]

/-- The two associativity forms are `≡` but not interchangeable: one writes where the
    other refuses. §6's (D)/(K)/(U) hedge is about this, not about `≡`. -/
theorem not_eq_altCodec_assoc :
    ∃ (l r : Term) (v : Value) (a : Attr),
      (denoteω l).e v = some a ∧ (denoteω r).e v = none :=
  ⟨.union [.string, .union [.literalS ["A"], .literalS ["A"]]],
   .union [.string, .literalS ["A"], .literalS ["A"]],
   .str "A", .s "A", assoc_left_e, assoc_right_e⟩

/-! ## `≡` is not transitive

Not a row of §6 — a property of §6 itself. `Codec.Equiv.refl` and `Codec.Equiv.symm` are
proved in `Equations.lean`; `trans` is absent, and this is why. §6 is presented as an
equational theory and `docs/codec-formalization.md`'s conformance standard asks a port to
exhibit `Codec.Equiv`, so a reader is entitled to assume the relation chains. It does not,
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

What is *not* settled here: whether `≡` chains when both ends are `denoteω` of derivable
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
now carries the same bound as a premise — the second and last of the two places
`codec-formalization.md` §4 predicted it would be forced outward, and the one that needed the
specification amended rather than the model corrected.

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

/-- **With `ℓ ⊆ D`, `literal-N` is a refinement of `number` again.** The premise is not
    decoration for the proof's sake: it is the whole of what the prism needed. -/
theorem literalN_sub_number (ls : List Double)
    (hD : ∀ d ∈ ls, Numeral.WF d.toDec = true) :
    ∀ v, (literalNCodec ls).T v → numberCodec.T v := by
  rintro v ⟨d, hd, rfl⟩
  exact ⟨d, rfl, hD d hd⟩

/-- **Without it, it is not.** A literal outside `D` is held by `literal-N` and not by
    `number`, so the two rules disagree about a value one of them claims to hold. -/
theorem not_literalN_sub_number {d : Double} (hw : Numeral.WF d.toDec = false) :
    ¬ ∀ v, (literalNCodec [d]).T v → numberCodec.T v := by
  intro h
  obtain ⟨d', hd', hwd⟩ := h (.num d) ⟨d, by simp, rfl⟩
  cases Value.num.inj hd'
  rw [hw] at hwd
  exact nomatch hwd

/-- And the consequence is not confined to the held sets: the term **writes** an attribute
    whose numeral is outside §1's `Numerals`, at a value `number` refuses outright. That is
    the sentence `(literal-N)` would need `ℓ ⊆ D` to stop being able to say. -/
theorem literalN_writes_off_numerals {d : Double} (hw : Numeral.WF d.toDec = false) :
    (literalNCodec [d]).e (.num d) = some (.n d.toDec) ∧
      numberCodec.e (.num d) = none := by
  refine ⟨?_, ?_⟩
  · rw [literalNCodec_e_num, if_pos (by simp : d ∈ [d])]
  · rw [numberCodec_e_num, if_neg (by rw [hw]; exact Bool.noConfusion)]

/-- The premise, read back off any derivation — this is what makes the two theorems above
    about *derivable* terms rather than about `literalNCodec` in isolation. -/
theorem typed_literalN_D {ls : List Double} {T μ} (h : Typed (.literalN ls) T μ) :
    ∀ d ∈ ls, Numeral.WF d.toDec = true := by
  cases h with | literalN _ _ _ hD => exact hD

/-- **Every derivable numeric literal refines `number` again.** The prism
    `lawful_literalNCodec` was once proved through is not restored as a proof route — the two
    codecs still differ, since one gates and the other tests membership — but the containment
    it stood for is a theorem once more, and it is `ℓ ⊆ D` that makes it one. -/
theorem typed_literalN_sub_number {ls : List Double} {T μ} (h : Typed (.literalN ls) T μ) :
    ∀ v, (literalNCodec ls).T v → numberCodec.T v :=
  literalN_sub_number ls (typed_literalN_D h)

/-- And the derivation the premise refuses. Before it, this held for **any** `d` with no
    hypothesis at all, which is what `literal(NaN)` was in the shipped library. -/
theorem not_typed_literalN_nonD {d : Double} (hw : Numeral.WF d.toDec = false) :
    ¬ ∃ T μ, Typed (.literalN [d]) T μ := by
  rintro ⟨T, μ, h⟩
  have hd := typed_literalN_D h d (by simp)
  rw [hw] at hd
  exact nomatch hd

/-! ## `decimal` before its held set was narrowed

`survivesStore_decimalCodec` shows that gating on `Numeral.Stored` discharges `η ⊆ ker p`.
This is the other half: the codec that gated on `Numeral.WF` instead — §1's *whole* numeral
grammar, which is what the implementation shipped — does not, and the witness is a form
DynamoDB was measured to normalise.

Without this the narrowing reads as a precaution. With it, it is the only option: `WF` admits
`"1.500"`, the store returns `"1.5"`, `decimal`'s `ker p` is equality (`ker_decimalCodec`),
and (R) through the store fails on a value the codec claimed to hold. -/

/-- `decimal`, gated on §1's grammar rather than on what the store hands back. -/
def decimalWF : Codec :=
  { T := fun v => ∃ s, v = .str s ∧ Numeral.WF s = true
    μ := some .N
    e := fun v => match v with
      | .str s => if Numeral.WF s then some (.n s) else none
      | _ => none
    p := fun a => match a with
      | .n x => if Numeral.WF x then some (.str x) else none
      | _ => none }

theorem decimalWF_e_str (s : String) :
    decimalWF.e (.str s) = if Numeral.WF s then some (.n s) else none := rfl

theorem decimalWF_p_n (x : Numeral) :
    decimalWF.p (.n x) = if Numeral.WF x then some (.str x) else none := rfl

/-- `"1.500"` is one of the forms `stored_rejects_denormal` records the store rewriting, and
    the un-narrowed codec claims to hold it. -/
theorem can_decimalWF_denormal : Can decimalWF (.n "1.500") :=
  ⟨.str "1.500", by rw [decimalWF_e_str, if_pos (by decide : Numeral.WF "1.500" = true)]⟩

/-- **The un-narrowed `decimal` does not survive the store.** Any `η` that normalises
    `"1.500"` — which is what DynamoDB was measured to do — falls outside its `ker p`. -/
theorem not_survivesStore_decimalWF {η : Attr → Attr}
    (hη : η (.n "1.500") = .n "1.5") : ¬ SurvivesStore decimalWF η := by
  intro h
  have hk : decimalWF.p (η (.n "1.500")) = decimalWF.p (.n "1.500") :=
    h _ can_decimalWF_denormal
  rw [hη, decimalWF_p_n, decimalWF_p_n,
    if_pos (by decide : Numeral.WF "1.5" = true),
    if_pos (by decide : Numeral.WF "1.500" = true)] at hk
  exact absurd (Value.str.inj (Option.some.inj hk)) (by decide)

/-- And (R) through the store fails outright: the value is written, the store rewrites the
    attribute, and the codec reads back something else — the shape of the shipped defect. -/
theorem not_retract_through_store_decimalWF {η : Attr → Attr}
    (hη : η (.n "1.500") = .n "1.5") :
    decimalWF.e (.str "1.500") = some (.n "1.500") ∧
      decimalWF.p (η (.n "1.500")) ≠ some (.str "1.500") := by
  refine ⟨by rw [decimalWF_e_str, if_pos (by decide : Numeral.WF "1.500" = true)], ?_⟩
  rw [hη, decimalWF_p_n, if_pos (by decide : Numeral.WF "1.5" = true)]
  intro hk
  exact absurd (Value.str.inj (Option.some.inj hk)) (by decide)

end Calculus
