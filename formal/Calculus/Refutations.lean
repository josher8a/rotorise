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
        altCodec, stringCodec, booleanCodec] at hb

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
        altCodec, arrayCodec, literalSCodec] at hv

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
        OptionSem.byAttempt, altCodec, tupleCodec, align, arrayCodec, stringCodec] at hv

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
  .union (.cons .string (.cons .boolean .nil))

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
        altCodec, stringCodec, literalSCodec]

/-- Right: three options admit, so the union refuses globally. -/
theorem assoc_right_e :
    (denoteω (.union [.string, .literalS ["A"], .literalS ["A"]])).e (.str "A") = none := by
  simp [denoteω, denoteωOpts, denoteωMems, optionSemOf, specOf, OptionSem.byAttempt,
        altCodec, stringCodec, literalSCodec]

/-- The two associativity forms are `≡` but not interchangeable: one writes where the
    other refuses. §6's (D)/(K)/(U) hedge is about this, not about `≡`. -/
theorem not_eq_altCodec_assoc :
    ∃ (l r : Term) (v : Value) (a : Attr),
      (denoteω l).e v = some a ∧ (denoteω r).e v = none :=
  ⟨.union [.string, .union [.literalS ["A"], .literalS ["A"]]],
   .union [.string, .literalS ["A"], .literalS ["A"]],
   .str "A", .s "A", assoc_left_e, assoc_right_e⟩

end Calculus
