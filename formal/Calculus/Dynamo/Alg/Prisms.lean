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

section

/-! ## Constructors as prisms

The shape this file is built out of. A constructor viewed as a partial iso onto its image
is the prism §7 of the specification already names when it calls `held` and `refine` "the
same shape at different strengths". Two families turn out to be instances, and each was
written out once per constructor before it was named:

* the **ground summands** (`GroundKind.summand`) — the prism of each base with the member it
  stamps, which gives a set element its member law;
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

/-- The summand of `L`. -/
def lS : Alg.Summand (List Attr) Attr Member Attr.member := ⟨lA, .L, fun _ => rfl⟩

/-- The summand of `M`. -/
def mS : Alg.Summand (MapOf Attr) Attr Member Attr.member := ⟨mA, .M, fun _ => rfl⟩

attribute [prism_rows] lS mS

/-! ## Ground codecs (§3) -/

/-- **The prism of a ground kind**: the stored constructor of the kind. -/
def GroundKind.prism : (k : GroundKind) → Ctor k.Carrier Attr
  | .string  => sC
  | .number  => nC
  | .boolean => boolA
  | .binary  => bC
  | .null    => nullA

/-- Equality at each base's carrier is decidable. -/
instance GroundKind.decEqCarrier : (k : GroundKind) → DecidableEq k.Carrier
  | .string  => inferInstanceAs (DecidableEq String)
  | .number  => inferInstanceAs (DecidableEq WFNumeral)
  | .boolean => inferInstanceAs (DecidableEq Bool)
  | .binary  => inferInstanceAs (DecidableEq Bytes)
  | .null    => inferInstanceAs (DecidableEq Unit)

/-! ### The element kinds of a wire set -/

/-- The three element kinds of §1's wire sets: the ground kinds that a set holds. -/
inductive SetKind where
  | string | number | binary
deriving DecidableEq

/-- The ground kind of a set's elements. -/
@[reducible] def SetKind.ground : SetKind → GroundKind
  | .string => .string
  | .number => .number
  | .binary => .binary

/-- What a set of each kind holds: the carrier of its ground kind. -/
abbrev SetKind.Carrier (k : SetKind) : Type := k.ground.Carrier

/-- The element prism of a kind: the prism of its ground kind. -/
abbrev SetKind.elem (k : SetKind) : Ctor k.Carrier Attr := k.ground.prism

/-- The wire set of a kind. -/
def SetKind.wire : (k : SetKind) → NEFinset k.Carrier → Attr
  | .string => Attr.ss
  | .number => Attr.ns
  | .binary => Attr.bs

/-- Two element prisms of different kinds share no datum. -/
theorem SetKind.elem_out_ne {k k' : SetKind} (h : k ≠ k') (x : k.Carrier) :
    k'.elem.out (k.elem.into x) = none := by
  cases k <;> cases k' <;> first | exact absurd rfl h | rfl

attribute [orient_rows] Alg.Codec.e Alg.Codec.p
attribute [prism_rows] GroundKind.prism sC nC bC boolA nullA

/-- The summand of a ground kind: the prism of the kind, which stamps the member of the kind. -/
def GroundKind.summand (k : GroundKind) : Alg.Summand k.Carrier Attr Member Attr.member :=
  ⟨k.prism, k.member, by cases k <;> exact fun _ => rfl⟩

/-- The pair a literal refines: its base's, chosen by the index.

    §3's `(literal)` premise is `⊢ g : T ⇝ μ, g ground`, and this is `g`. It exists because
    the rule quantifies over the base — the three constructors this replaces had it hard-coded
    three times over, which is why `literal-S` and `literal-N` were two rules and `boolean`,
    `binary` and `null` were none. A base is the identity on the fiber of its kind: it
    accepts a datum of the kind, changes nothing, and stamps the member of the kind. -/
@[simp] def baseCodec (k : GroundKind) : Codec := Alg.fiberCodec Attr.member k.member

attribute [prism_rows] baseCodec GroundKind.summand Alg.fiberCodec Attr.member

/-- `number` writes a numeral as `N`. -/
theorem baseCodec_e_num (x : WFNumeral) : (baseCodec .number).e (.num x) = some (.n x) := rfl

/-- …and reads `N` back as the numeral. -/
theorem baseCodec_p_n (x : WFNumeral) : (baseCodec .number).p (.n x) = some (.num x) := rfl

/-- `literal(ℓ)`'s predicate: the base's prism matches the value, and the match is the
    alternative.

    One definition where there were two (~~inLS~~, ~~inLN~~) and three bases with none. The
    prism of the index makes the carrier concrete, and so the equality decidable. -/
def inL (k : GroundKind) (x : k.Carrier) (v : Value) : Bool :=
  match k.prism.out v with
  | some y => decide (y = x)
  | none   => false

/-! `inL`'s rows at the five bases, as `@[simp]` equations.

Without these a `simp` that needs `inL` at one base unfolds the prism's matcher at every
rewrite. That is what ~~fanOf~~ found behind `AdmA_exact`'s duplication. Each of the five bases
gets an equation. -/

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

/-- **`inL` holds exactly at the alternative's datum**, at every base. -/
theorem inL_iff {k : GroundKind} {x : k.Carrier} {v : Value} :
    inL k x v = true ↔ v = k.prism.into x := by
  rw [← Alg.Ctor.out_eq_some, inL]
  split <;> simp_all

/-- §3's `{ℓ}` — the held set: the datum that the base's prism builds from the alternative.
    Spelled `Value → Prop` rather than `Held`, which is `Typing`'s abbreviation and one module
    down. -/
def HLit (k : GroundKind) (x : k.Carrier) : Value → Prop :=
  fun v => v = k.prism.into x


/-! ## Wrappers -/

/-! ### §1's number gates are that combinator too

    `(number)` and `(decimal)` each carry a predicate checked on **both** halves —
    `Numeral.WF` on the double a text reads back to, `Numeral.Stored` on the numeral a
    string is written as. §3 argues at length that gating only the write breaks (C), which
    is exactly the shape `restrict` has and an ad-hoc `if` does not.

    So the gates are not bespoke: each of the two codecs is `refine` over a base. The
    `decimal` gate is a fact of the store, so the DynamoDB port states it on the pair
    (`decimalCodec` is that restriction, `Dynamo/Lang/Store.lean`). The bases used to be *ungated*, every
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

    `T` is spelled as §3's `ℓ` (`HLit`), so the judgement reads against §3. The set is the
    refinement's held set (`HLit_iff_restrict`); only the spelling differs. -/
def literalCodec (k : GroundKind) (x : k.Carrier) : Codec :=
  { (baseCodec k).restrict (inL k x) with T := HLit k x }

/-! ### The gated ground codecs are refinements

`literal` is not a new construction: it is its base with a prism laid over it, which is what
§7 means by "an iso and a prism". So its laws come from `Lawful.restrict` and `carrier_restrict`,
and its held set is the restriction's (`HLit_iff_restrict`). `decimal` is the same shape at the
`number` base, restricted to the stored numerals (`Store.lean`). -/

/-- **A literal's held set is the refinement's held set**: §3's `ℓ` is the base's carrier
    restricted to the alternative. -/
theorem HLit_iff_restrict (k : GroundKind) (x : k.Carrier) (v : Value) :
    HLit k x v ↔ ((baseCodec k).restrict (inL k x)).T v := by
  show v = k.prism.into x ↔ Attr.member v = k.member ∧ inL k x v = true
  rw [inL_iff]
  exact ⟨fun h => ⟨h ▸ k.summand.hμ x, h⟩, And.right⟩

end

end Calculus
