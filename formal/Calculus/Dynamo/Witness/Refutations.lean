import Calculus.Dynamo.Lang.Equations
import Calculus.Dynamo.Lang.Soundness
import Calculus.Dynamo.Witness.Discharge

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

/-! ## §2's three laws are independent

§2's laws are (R), canonical reads, and (W). Independence *is* a family of counter-models: for
each law, a codec satisfying the other two and failing that one.

They are stated at `Codec`, not at `Term`, which is what makes this independence rather than
a remark about the terms that happen to exist: a law the language cannot violate is still a
law the definition does not imply. Each is as small as `𝔸` allows — a pair of partial
functions on strings, `T` everything, and a member named only where the law needs one.

`cM` is the codec between `LawfulCore` and `Lawful`: every read value is writable, and the
write lands on another attribute. That is the same residue `alternate reader` leaves (§5). -/

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
/-- …but every read value writes the attribute it was read from. -/
theorem cR_canon : ∀ {a t}, cR.p a = some t → cR.e t = some a := by
  intro a t h; cases a <;> simp [cR] at h; split at h <;> simp_all [cR]; subst_vars; rfl
/-- …and the declared member is the only one written. -/
theorem cR_W : ∀ {μ}, cR.μ = some μ → ∀ {t a}, cR.e t = some a → a.member = μ := by
  intro μ hμ t a h; cases t <;> simp [cR] at h hμ; subst h; subst hμ; rfl

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
  intro μ hμ t a h; cases t <;> simp [cC] at h hμ; split at h <;> simp_all []; subst_vars; rfl
/-- …but `"b"` is readable and not writable, which breaks canonical reads and nothing else. -/
theorem cC_notCanon : ¬ (∀ {a t}, cC.p a = some t → cC.e t = some a) := by
  intro h; have := @h (.s "b") (.str "b") rfl; simp [cC] at this

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
/-- …and every read value writes the attribute it was read from. -/
theorem cW_canon : ∀ {a t}, cW.p a = some t → cW.e t = some a := by
  intro a t h
  cases a <;> simp only [cW] at h
  case s s =>
    split at h
    · exact absurd h (by simp)
    · next hz => cases h; simp only [cW]; rw [if_neg hz]
  case bool b =>
    cases b
    · exact absurd h (by simp)
    · cases h; simp [cW]
  all_goals exact absurd h (by simp)

/-- **Definedness without canonical reads.** Declares no member, and reads `⟨BOOL, true⟩` back
    as a string it writes to `S` — so a stored `BOOL` becomes an `S` on the way through. -/
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
/-- So the three that hold are exactly `LawfulCore` — the same residue `alternate reader` leaves. -/
theorem cM_core : LawfulCore cM := ⟨cM_R, cM_C, cM_W⟩
/-- …and canonical reads are what is left to break: `⟨BOOL, true⟩` reads as `"z"` and re-writes
    to `⟨S, "z"⟩`. -/
theorem cM_notCanon : ¬ (∀ {a t}, cM.p a = some t → cM.e t = some a) := by
  intro h; have := @h (.bool true) (.str "z") rfl; simp [cM] at this

/-! ## `union(c₁ … cₙ) ≢ union(c₁ … cₙ, c)`

Not closed under extension. The held set grows, so `≡` fails before any obligation is consulted.
§6 justifies the row by well-formedness, and the model shows it fails for a more basic reason. -/

theorem not_equiv_union_extend :
    ¬ Codec.Equiv (denote (.union [.string])) (denote (.union [.string, .boolean])) := by
  intro h
  have hb := (h.heldSet (.bool true)).mpr
  simp [denote_rows,
        altCodec, stringCodec, booleanCodec] at hb

/-! ## `union(array(c₁), array(c₂)) ≢ array(union(c₁, c₂))`

§6: "Left: a sequence homogeneous in one option. Right: a sequence of either,
elementwise." The witness is the shortest heterogeneous sequence. -/

/-- `["A", "B"]` is an array of either literal, but homogeneous in neither. -/
theorem not_equiv_union_array :
    ¬ Codec.Equiv
        (denote (.union [.array (.literal .string "A"), .array (.literal .string "B")]))
        (denote (.array (.union [.literal .string "A", .literal .string "B"]))) := by
  intro h
  have hv := (h.heldSet (.arr [.str "A", .str "B"])).mpr
  simp [Term.array, ← arrayCodec_eq_listCodec, denote_rows,
        altCodec, arrayCodec, literalCodec,
        baseCodec, Alg.Codec.restrict, inL, stringCodec, HLit] at hv

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
  simp only [Term.tuple, ← tupleCodec_eq_listCodec, denote_rows,
    tupleCodec, align, Option.map_some,
    Option.some.injEq, exists_eq_left', List.mem_cons, List.not_mem_nil, or_false] at hv
  exact absurd (hv (by rintro p (rfl | rfl) <;> exact ⟨_, rfl⟩))
    (by rintro ⟨ps, hps, -⟩; simp at hps)

/-- Against the array: the empty sequence, which an array holds and a fixed head cannot. -/
theorem not_equiv_tupleTail_array :
    ¬ Codec.Equiv (denote (.tuple [.string] (some .string)))
                  (denote (.array (.union [.string]))) := by
  intro h
  have hv := (h.heldSet (.arr [])).mpr
  simp [Term.tuple, Term.array, ← tupleCodec_eq_listCodec, ← arrayCodec_eq_listCodec,
        denote_rows,
        altCodec, tupleCodec, align, arrayCodec,
        stringCodec] at hv

/-! ## `refine(held(c, P, f, g), q) ≢ held(refine(c, q), P, f, g)`

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
    ¬ Codec.Equiv (denote (.refine (.held .string .string isoF id) (.closure predA)))
                  (denote (.held (.refine .string (.closure predA)) .string isoF id)) := by
  intro h
  have hv := (h.heldSet (.str "B")).mpr
  simp [denote_rows, Alg.Codec.through, Alg.Codec.restrict, Pred.eval, stringCodec, isoF, predA] at hv

/-! ## `legacy(c, r)` breaks canonical reads, and `e ∘ p ≢ id`

Two rows, one witness. A migration reads an attribute that the codec does not write, so the
value it reads writes another attribute. That is why §6 says an `alternate reader` attribute
cannot be an index key. -/

/-- Reads an `N` into a string value — so the re-encoding lands on `S`. -/
def migrateNtoS : Attr → Option Value
  | .n _ => some (.str "x")
  | _ => none

/-- `string` with `migrateNtoS` as its alternate reader. -/
noncomputable def migration : Codec := (denote .string).extendRead migrateNtoS

theorem legacy_p_n : migration.p (.n (.of "1")) = some (.str "x") := rfl

theorem legacy_e_x : migration.e (.str "x") = some (.s "x") := rfl

/-- §6: an alternate reader breaks canonical reads. The migration reads `N` and writes `S`. -/
theorem legacy_breaks_MP : ¬ Lawful migration := by
  intro h
  have hc := h.canon legacy_p_n
  rw [legacy_e_x] at hc
  cases hc

/-- §6: `e ∘ p ≢ id` — equality holds only on `Can(c)`, and this attribute is off it. -/
theorem e_comp_p_ne_id :
    ∃ (c : Codec) (a : Attr) (v : Value), c.p a = some v ∧ c.e v ≠ some a :=
  ⟨migration, .n (.of "1"), .str "x", legacy_p_n, by
    rw [legacy_e_x]; intro hc; exact nomatch hc⟩

/-! ## `optional(optional(c))` — not derivable, by construction

This row needs no theorem, and could not have one: it is enforced by the syntax. `ObjectSlot`
(Term.lean) has two constructors — `req` and `optional` — and every one takes a
`Term`. None takes an `ObjectSlot`, so `optional(optional(c))` cannot be written down.
An alternate reader (`Codec.extendRead`) is outside a slot. An `ObjectSlot` always carries a
current `Term`.

That is the stratification §4 of the specification asks for, and the model gets it from
the type rather than from a side condition — which is the stronger place to get it. It is
also `C3`'s sharpest test for a port (§5): a library that lets `optional(c)` appear where a
codec is expected has no corresponding `Term`, and the mapping fails there rather than
quietly succeeding.
-/

/-! ## `set(union(c₁, c₂))`: derivable, and refused by the store

§6: "the premise on `set` demands a member, and a union of options writing different
members has none." `μSyn` of a heterogeneous union is `none`, and `typed_μSyn` puts the same
`none` in the judgement.

`Term.set` takes any element term, so `set(union(string, boolean))` is a term, and the judgement
types it at the member `none` (`setMember` of the union's `none`). The DynamoDB set obligation
`SetElem` refuses it (`setElem_union_refused`). The lift of a lawful union is lawful.
-/

/-- **A heterogeneous union fails the DynamoDB set obligation**, because the union names no single
    member. -/
theorem setElem_union_refused : ¬ SetElem (denote (.union [.string, .boolean])) := by
  intro h
  rw [SetElem, denote_μ] at h
  exact absurd h (by decide)

/-- The union on its own is typed, and so is the `set` above it: the store refuses the set. -/
theorem typed_union_string_boolean :
    Typed (.union [.string, .boolean])
      (HUnion [fun v => ∃ s, v = .str s, fun v => ∃ b, v = .bool b]) none :=
  .union (.cons (Typed.base _) (.cons (Typed.base _) .nil))

/-- **An empty option is the unit of the sum.** The bottom holds nothing, so it changes no
    union's `HUnion`. The meet builds such a union whenever a surviving option's predicate
    holds of nothing. -/
example : ∃ T μ, Typed (.union [.string, .never]) T μ :=
  ⟨_, _, .union (.cons (Typed.base _) (.cons .never .nil))⟩

/-! ## `≡` is not transitive

Not a row of §6 — a property of §6 itself. `Codec.Equiv.refl` and `Codec.Equiv.symm` are
proved over any carriers; `trans` is absent, and this is why. §6 is presented as an
equational theory and the conformance standard asks a port to exhibit `Codec.Equiv`, so a
reader is entitled to assume the relation chains. It does not,
and nothing said so.

The mechanism is the tolerance the header above describes: `≡` compares `e` and `p` only
*where both are defined*, so a codec whose `e` is nowhere defined agrees with everything.
Put one in the middle and it relates two codecs that disagree outright.

The witness is at `Codec` level, which is the level §6's relation lives at: the rows of §6 are
stated over any carriers, about combinators and not about `denote`. What keeps it
from being a degenerate artifact is that **all three codecs are `Lawful` and on their
`Carrier`**, and the held set is not empty: the failure survives every hypothesis §2
imposes on a pair. It uses only the licence §2 grants explicitly — a term's `e` does
whatever it likes off `T` — and the fact that `Carrier` bounds `dom(e)` by `T` without
requiring the converse.

What is *not* settled here: whether `≡` chains when both ends are `denote` of derivable
terms. The middle codec below holds `null` and writes nothing, and no derivable term does
that, so this refutation does not decide the restricted question. -/

/-- Writes `null` as `S "A"`, and reads only that attribute — lawful, and on its carrier. -/
def cA : Codec :=
  { T := fun v => v = .null, μ := none,
    e := fun v => match v with | .null => some (.s "A") | _ => none,
    p := fun a => match a with | .s x => if x = "A" then some .null else none | _ => none }

/-- The same, at `S "B"`. It disagrees with `cA` on the one value both write. -/
def cB : Codec :=
  { T := fun v => v = .null, μ := none,
    e := fun v => match v with | .null => some (.s "B") | _ => none,
    p := fun a => match a with | .s x => if x = "B" then some .null else none | _ => none }

/-- The middle: the same held set, and no `e` or `p` anywhere. Every law of §2 is vacuous
    on it, which is exactly what makes it `≡` to both of the others. -/
def cMid : Codec :=
  { T := fun v => v = .null, μ := none, e := fun _ => none, p := fun _ => none }

theorem lawful_cA : Lawful cA where
  retract := by intro t a he; cases t <;> simp_all [cA]; subst_vars; simp
  canon := by
    intro a t hp
    cases a with
    | s x =>
      simp only [cA] at hp
      split at hp
      · next hx => cases hp; subst hx; rfl
      · exact nomatch hp
    | _ => simp [cA] at hp
  writes := by intro μ hμ; exact nomatch hμ

theorem lawful_cB : Lawful cB where
  retract := by intro t a he; cases t <;> simp_all [cB]; subst_vars; simp
  canon := by
    intro a t hp
    cases a with
    | s x =>
      simp only [cB] at hp
      split at hp
      · next hx => cases hp; subst hx; rfl
      · exact nomatch hp
    | _ => simp [cB] at hp
  writes := by intro μ hμ; exact nomatch hμ

theorem lawful_cMid : Lawful cMid := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [cMid]

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
    ¬ ∀ c d e : Codec, Codec.Equiv c d → Codec.Equiv d e → Codec.Equiv c e :=
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

What follows is what it buys and what it refuses. The refutations were conditional on a host
number outside `D` existing, while the numeric host was axiomatized with the shortest-text round
trip and nothing else: whether IEEE-754 has a value DynamoDB will not store is a fact about IEEE
that the model deliberately does not assert. It was not a hypothetical — the shipped `literal(NaN)`
wrote `⟨N, "NaN"⟩` and `literal(1e400)` wrote `⟨N, "Infinity"⟩`, both reachable with no cast,
which is what settled the question the conditional leaves open. -/

/-- **`literal-N` is a refinement of `number`, with nothing asked for.** This took
    `hD : ∀ d ∈ ls.1, Numeral.WF d.toDec = true` and its docstring said the premise "is the
    whole of what the prism needed". It still is; it is the VALUE carrier's now, so the
    containment holds of every literal there is and of every value there is. -/
theorem literalN_sub_number (y : WFNumeral) :
    ∀ v, (literalCodec .number y).T v → numberCodec.T v := by
  rintro v rfl
  exact ⟨y, rfl⟩

/-! ### §3's `(literal)` at `number`, and why the witnesses are all gone now

§3's premise line is `⊢ g : T ⇝ μ, g ground; ℓ₁ … ℓₙ ∈ T`, and at `g = number` the base's held
set *is* §1's `D`, so the rule already requires `ℓ ⊆ D`. Two witnesses here used to show that
premise load-bearing, stated about ~~literalNRule~~, an ungated prism that was deliberately not
a `Term` and existed only to carry them.

**They are unstatable now, and by the argument the section below already made about a third.**
Both needed a value outside `D` to point at: `{d : Double} (hw : Numeral.WF d.toDec = false)`.
`Value.num` carries `WFNumeral`, so there is no such value to quantify over. The gate did not
weaken; it moved one level further out, from the alternative's carrier to the VALUE's, and
`ℓ ⊆ D` is now true of everything that can be written down.

~~inLNRule~~, ~~literalNRule~~, ~~not_literalNRule_sub_number~~ and
~~literalNRule_holds_what_it_cannot_write~~ go together. What the section keeps is the reason:
"this cannot be derived" and "this cannot be written" became one claim, and a refutation needs
a representable counterexample. -/

/-! Two theorems here quantified over a derivation only to read `hD` back off it. With the gate
in the carrier the derivation argument is unused, `#lint_calculus` reported it, and the honest
response to that report is deletion rather than a sanction entry: one became `fun d _ => d.2`
and the other became `literalN_sub_number` above, which needs no premise. A theorem whose
hypothesis has become decoration is a description that has stopped describing.

A third said no numeric literal outside `D` is derivable. It quantified over a carrier that had
no closed term, because the carrier was a host axiom, so there was nothing to quantify over:
"this cannot be derived" and "this cannot be written" were one claim, and only the theorem could
go stale. `N` is carried exactly now and closed numeric literals exist, so the premise that made
the two claims one is gone with the axiom. -/

/-! ## `union(opaque, c)` is never separable

Not one of §6's nine rows — a row §5 never wrote, and the reason it did not is that
`opaque` looked like a term with nothing to say. `κ .opaq` is `⊤` and, before `adm`
was made to ask `opaque`'s codec, so were `adm .opaq` and `admA .opaq`. ~~SepV~~
offers exactly two routes — a disjoint kind or a disjoint admissible set — and ~~SepA~~
two more — a distinct named member or a disjoint admissible set. A `⊤` on every one of
the four is not a weak option; it is an **absorbing** one, in the sense `unknown | T` is
absorbing in TypeScript.

The absorption survives the semantic row. `opaque` writes every value (`opaq_total`), so
**an `opaque` never separates from an option that admits anything.** The kind and member
disjuncts are structurally unavailable, so a single shared value or attribute is enough.
The fact holds in both argument orders, because `κ` and `μSyn` are `⊤` at an `opaque`. -/
