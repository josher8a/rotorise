import Calculus.Dynamo.Alg.Lists
import Calculus.Dynamo.Alg.Codec

/-!
# Constructors as prisms, and the ground codecs

The DynamoDB instances of the certified combinator algebra. `Ctor`, the wrappers `through`,
`restrict` and `extendRead`, and their laws take the carriers as parameters. This file states
the instances that read the constructors of `Value` and `Attr`:

* the prisms, one per constructor, on the value side and the attribute side;
* ground codecs, one per §3 ground term.
-/

namespace Calculus

noncomputable section

/-! ## Constructors as prisms

The shape this file is built out of. A constructor viewed as a partial iso onto its image
is the prism §7 of the specification already names when it calls `held` and `refine` "the
same shape at different strengths". Two families turn out to be instances, and each was
written out once per constructor before it was named:

* the **point ground codecs** (`pointCodec`) — `string`, `boolean`, `binary` and
  `null` are a payload carried between a value constructor and an attribute constructor,
  differing in nothing but which pair;
* the **scalar payload prisms** (`sC`/`nC`/`bC`) — the attribute half of three of those
  pairs, factored out because `setAt` needs the same three prisms to decide which wire set
  a homogeneous element set writes to.

Naming the shape once is what lets retract, canon and writes be discharged once for each family
rather than once per constructor. -/

/-! ### The prisms of the carrier -/

/-- `S`'s payload. -/ def sC : Ctor String Attr where
  into := Attr.s
  out := fun a => match a with | .s v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `N`'s payload. -/ def nC : Ctor WFNumeral Attr where
  into := Attr.n
  out := fun a => match a with | .n v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `B`'s payload. -/ def bC : Ctor Bytes Attr where
  into := Attr.b
  out := fun a => match a with | .b v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `BOOL`'s payload. -/ def boolA : Ctor Bool Attr where
  into := Attr.bool
  out := fun a => match a with | .bool v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `NULL`'s point: a prism with a trivial payload, which is what makes `null` an instance of
    the same shape as the three that carry data. -/ def nullA : Ctor Unit Attr where
  into := fun _ => .null
  out := fun a => match a with | .null => some () | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-! ### The container prisms

The same shape one level up: a constructor whose payload is a *list* of entries. `L` and
`M` are the two §1 provides. Naming them is what lets `array` and `record` be one construction
(`entrywise`, under Products) rather than two. -/

/-- `L`'s payload. -/ def lA : Ctor (List Attr) Attr where
  into := Attr.l
  out := fun a => match a with | .l xs => some xs | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `M`'s payload. -/ def mA : Ctor (MapOf Attr) Attr where
  into := fun p => Attr.m p.1 p.2
  out := fun a => match a with | .m keys f => some ⟨keys, f⟩ | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-! ## Ground codecs (§3) -/

/-- **The prism of a ground kind**: the stored constructor of the kind. -/
def GroundKind.prism : (k : GroundKind) → Ctor k.Carrier Attr
  | .string  => sC
  | .number  => nC
  | .boolean => boolA
  | .binary  => bC
  | .null    => nullA

/-- The pair a literal refines: its base's, chosen by the index.

    §3's `(literal)` premise is `⊢ g : T ⇝ μ, g ground`, and this is `g`. It exists because
    the rule quantifies over the base — the three constructors this replaces had it hard-coded
    three times over, which is why `literal-S` and `literal-N` were two rules and `boolean`,
    `binary` and `null` were none. A base is one point codec at the prism of its kind: it
    accepts a datum of the kind, changes nothing, and stamps the member of the kind. -/
@[simp] def baseCodec (k : GroundKind) : Codec := pointCodec k.prism k.prism k.member

/-- `number` writes a numeral as `N`. -/
theorem baseCodec_e_num (x : WFNumeral) : (baseCodec .number).e (.num x) = some (.n x) := rfl

/-- …and reads `N` back as the numeral. -/
theorem baseCodec_p_n (x : WFNumeral) : (baseCodec .number).p (.n x) = some (.num x) := rfl

/-- `literal(ℓ)`'s predicate: the value is the alternative.

    One definition where there were two (~~inLS~~, ~~inLN~~) and three bases with none. Dispatching
    on the index first is what makes the carrier concrete, and so the equality decidable. -/
noncomputable def inL : (k : GroundKind) → k.Carrier → Value → Bool
  | .string,  x, .str s  => decide (s = x)
  -- `number`'s carrier IS the value's, so this row joins the ungated four: the payload is
  -- the alternative and there is no gate left to go through.
  | .number,  x, .num d  => decide (d = x)
  | .boolean, x, .bool b => decide (b = x)
  | .binary,  x, .bin b  => decide (b = x)
  | .null,    _, .null   => true
  | _, _, _ => false

/-! `inL`'s rows at the five bases, as `@[simp]` equations.

Without these a `simp` that needs `inL` at one base unfolds `inL.match_1` — the matcher Lean
derives for the whole ten-row table — and pays for all ten rows at every rewrite. That is what
~~fanOf~~ found behind `AdmA_exact`'s duplication. Each of the five bases gets an equation. -/

/-- `.str` at `string`: the payload *is* the carrier, so this is `rfl`. -/
@[simp] theorem inL_str (x s : String) :
    inL .string x (.str s) = decide (s = x) := rfl

/-- `.num` at `number`: the carrier is the payload now, so this is `rfl` like the three
    ungated bases beside it. It used to need a `dite` on the host's spelling. -/
@[simp] theorem inL_num (x d : WFNumeral) :
    inL .number x (.num d) = decide (d = x) := rfl

/-- `.bool` at `boolean`, on the same terms. -/
@[simp] theorem inL_bool (x b : Bool) :
    inL .boolean x (.bool b) = decide (b = x) := rfl

/-- `.bin` at `binary`, on the same terms. -/
@[simp] theorem inL_bin (x b : Bytes) :
    inL .binary x (.bin b) = decide (b = x) := rfl

/-- `.null` at `null`: `Unit` has one inhabitant, so the row is `true` and not a comparison. -/
@[simp] theorem inL_null (x : Unit) :
    inL .null x .null = true := rfl

/-- §3's `{ℓ}` — the held set, uniform in the base because `toValue` is. Spelled
    `Value → Prop` rather than `Held`, which is `Typing`'s abbreviation and one module down. -/
def HLit (k : GroundKind) (x : k.Carrier) : Value → Prop :=
  fun v => v = k.toValue x


/-! ## Wrappers -/

/-! ### §1's number gates are that combinator too

    `(number)` and `(decimal)` each carry a predicate checked on **both** halves —
    `Numeral.WF` on the double a text reads back to, `Numeral.Stored` on the numeral a
    string is written as. §3 argues at length that gating only the write breaks (C), which
    is exactly the shape `restrict` has and an ad-hoc `if` does not.

    So the gates are not bespoke: each of the two codecs is `refine` over a base. The
    `decimal` gate is a fact of the store, so the DynamoDB port states it on the pair
    (`decimalCodec_e_restrict`, `Dynamo/Lang/Store.lean`). The bases used to be *ungated*, every
    numeral and every string, and cannot be, now that both sides carry §1's `Numerals`. There is one base at `N`
    instead of the two a host carrier forced, and it is §1's own set: `baseCodec .number`. The ungated
    bases were standing in for sets the carrier should have been. -/

/-- §1's `D`, as a predicate on values. **It asks only that the value is an `N`**: `D` is the
    well-formed numerals and the carrier is exactly those, so the grammar check that used to
    sit here is carried rather than tested. -/
def inD : Value → Bool :=
  fun v => match v with | .num _ => true | _ => false


/-! ### The base at `N` is §1's own set, and there is exactly ONE of them

**`baseCodec .number` IS the base at `N`.** `Attr.n` carries `Numeral.WF` and so does the value
side now, so `Carries(N)` is §1's `Numerals` on both halves and no wider codec exists to
refine. ~~wfDecimalCodec~~ was the text-side base beside it, gated at `WF` where `baseCodec .number`
went through a host spelling; the two are one definition now and the second is deleted. The
DynamoDB port refines it at `Stored` (`Dynamo/Lang/Store.lean`), and `Stored` is a real gate rather
than a carried one. -/

/-- §3 `(literal)`. **The pair is a refinement of its base by construction** — the `refine`
    §7 calls "an iso and a prism", with the prism named by `ℓ` and the iso supplied by the
    index.

    **`T` is deliberately *not* the refinement's**: it stays §3's `ℓ`. That used to mean a
    numeric literal outside `D` was *held* and unwritable, which is (B) failing, and it no
    longer can be: `GroundKind.number`'s carrier is the well-formed numerals, so `HLit` holds
    only values `baseCodec .number` writes. The transcription that used to exhibit (B) failing here
    is retired, because the value carrier is `D` and there is no outside to point at. -/
noncomputable def literalCodec (k : GroundKind) (x : k.Carrier) : Codec :=
  Alg.Codec.ofEP (T := HLit k x) (μ := ((baseCodec k).restrict (inL k x)).μ)
    (e := ((baseCodec k).restrict (inL k x)).e) (p := ((baseCodec k).restrict (inL k x)).p)

theorem literalNCodec_p_n (y : WFNumeral) (x : WFNumeral) :
    (literalCodec .number y).p (.n x) =
      ((baseCodec .number).p (.n x)).bind (fun v => if inL .number y v then some v else none) := rfl

/-! ### The gated ground codecs are refinements

`literal` is not a new construction: it is `string` and `number` with a prism laid over
them, which is exactly what §7 means by "an iso and a prism". Naming the predicates makes
that visible, and lets all four of its laws come from `Lawful.restrict` and
`carrier_restrict` instead of four bespoke inductions.

`decimal` is deliberately *not* here. It moves the member (`str` values to an `N`
attribute), so it is not a refinement of `string` and keeps its own proofs. -/

/-- **§3's gate is `refine` over the base, at every base** — and the numeric one is `number`
    itself rather than a separate ungated numeric term, because §1's `Numerals` is the whole of
    `Carries(N)` and there is no wider numeric pair. That is what makes numeric literals
    separable.

    Both halves are `rfl` now, where the string pair needed a `funext` and a case split: the
    codec *is* the restriction, rather than a hand-written pair that agreed with one. -/
theorem literalCodec_e_restrict (k : GroundKind) (x : k.Carrier) :
    (literalCodec k x).e = ((baseCodec k).restrict (inL k x)).e := rfl

theorem literalCodec_p_restrict (k : GroundKind) (x : k.Carrier) :
    (literalCodec k x).p = ((baseCodec k).restrict (inL k x)).p := rfl

/-- **A literal codec writes only its own alternative.** `restrict`'s `e` is a guard in front
    of the base's, so a defined write is the value `ℓ` names — which is what an object option's
    content admission reads off a field whose term is a literal. -/
theorem inL_of_literalCodec_e {k : GroundKind} {x : k.Carrier} {v a}
    (he : (literalCodec k x).e v = some a) : inL k x v = true := by
  rw [literalCodec_e_restrict] at he
  exact (Alg.refine2_f.mp he).1

/-- The value `ℓ` names places the value in the held set — the direction `Carrier` needs.

    The four ungated bases are the payload equality outright. `number` and `decimal` reach here
    with a `dite` on their gate, so the branch splits on the gate and names the alternative as a
    subtype, and `toValue` projects it straight back. `cases hs :` rather than `by_cases`, which
    is classical. `.null` is `rfl`: it used to need the alternative set's nonemptiness proof, and
    a carrier with one inhabitant needs nothing. -/
theorem hLit_of_inL (k : GroundKind) (x : k.Carrier) (v : Value) :
    inL k x v = true → HLit k x v := by
  cases k <;> cases v <;> intro h <;>
    first
      | exact Bool.noConfusion h
      | rfl
      | (simp only [inL, decide_eq_true_eq] at h
         subst h
         rfl)
      | (simp only [inL] at h
         split at h
         · simp only [decide_eq_true_eq] at h
           subst h
           rfl
         · exact Bool.noConfusion h)
      | (rename_i d
         cases hs : Numeral.WF d.toDec with
         | true =>
           simp only [inL, hs, dif_pos, decide_eq_true_eq] at h
           exact congrArg Value.num (congrArg Subtype.val h)
         | false => simp [inL, hs] at h)

end

end Calculus
