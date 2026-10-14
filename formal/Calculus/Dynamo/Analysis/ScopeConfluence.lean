import Calculus.Dynamo.Analysis.ScopeUniversal
import Calculus.Dynamo.Analysis.ScopeDisjoint

/-!
# Confluence: the payoffs of a held-free closed codec

`Dynamo/Lang/ScopeHeldFree.lean` proves that a held-free closed codec is a restriction of `opaque`
on both halves (`Closed.confluence_W`, `Closed.confluence_R`). This file holds what follows from it.

The payoffs follow from one fact: `opaque` is the identity. So two held-free closed codecs that
both write a value write one attribute (`Closed.write_agree`), and two that both read an attribute
read one value (`Closed.read_agree`).

`held` is the one operation outside the result. An adapter changes the carrier, so it is not a
restriction of `opaque`. `Closed.held_violates_W` and `Closed.held_violates_R` are the control:
`oneHeldClosed` writes `"1"` as the number `1`, which `opaque` does not.
-/

namespace Calculus

/-! ## Payoffs -/

/-- Two held-free closed codecs that both write a value write one attribute. -/
theorem Closed.write_agree {α : Table} {s t : Closed} (hs : s.HF) (ht : t.HF) {v a b}
    (ha : (s.meaning α).e v = some a) (hb : (t.meaning α).e v = some b) : a = b :=
  Option.some.inj ((Closed.confluence_W hs ha).symm.trans (Closed.confluence_W ht hb))

/-- Two held-free closed codecs that both read an attribute read one value. -/
theorem Closed.read_agree {α : Table} {s t : Closed} (hs : s.HF) (ht : t.HF) {a v w}
    (hv : (s.meaning α).p a = some v) (hw : (t.meaning α).p a = some w) : v = w :=
  Option.some.inj ((Closed.confluence_R hs hv).symm.trans (Closed.confluence_R ht hw))

/-! ## The false control: a `held` adapter is not a restriction of `opaque` -/

/-- The table that gives each generator the constant adapter of `oneHeldClosed`. -/
def oneTable : Table := fun _ => (fun _ => Value.num (WFNumeral.of "1"), fun _ => Value.str "1")

/-- The numeric base under a constant adapter, with the caller side restricted to text, as a
    closed codec of one entry. The adapter writes each text as the number `1`, and reads each
    number as the text `"1"`. -/
def oneHeldClosed : Closed :=
  Closed.one (Scoped.Term.held false Scoped.Term.number Scoped.Term.string (.caller 0, false) [])

/-- `oneHeldClosed` writes the string `"1"` as the number `1`. -/
theorem Closed.oneHeld_writes :
    (oneHeldClosed.meaning oneTable).e (.str "1") = some (.n (WFNumeral.of "1")) := by
  rfl

/-- **The false control, write side.** `oneHeldClosed` writes an attribute that `opaque` does not
    write at the same value, so `Closed.confluence_W` needs `Closed.HF`. -/
theorem Closed.held_violates_W :
    ¬ ∀ v a, (oneHeldClosed.meaning oneTable).e v = some a →
      ((Closed.one .opaq).meaning oneTable).e v = some a := fun h =>
  absurd (Option.some.inj ((Closed.opaq_f oneTable .host _).symm.trans
    (h _ _ Closed.oneHeld_writes))) (fun h => nomatch h)

/-- `oneHeldClosed` reads the number `1` as the string `"1"`. -/
theorem Closed.oneHeld_reads :
    (oneHeldClosed.meaning oneTable).p (.n (WFNumeral.of "1")) = some (.str "1") := by
  rfl

/-- **The false control, read side.** `oneHeldClosed` reads a value that `opaque` does not read at
    the same attribute, so `Closed.confluence_R` needs `Closed.HF`. -/
theorem Closed.held_violates_R :
    ¬ ∀ a v, (oneHeldClosed.meaning oneTable).p a = some v →
      ((Closed.one .opaq).meaning oneTable).p a = some v := fun h =>
  absurd (Option.some.inj ((Closed.opaq_f oneTable .dual _).symm.trans
    (h _ _ Closed.oneHeld_reads))) (fun h => nomatch h)

/-- The control of the control: `oneHeldClosed` is not held-free, so `Closed.confluence_W` does
    not apply to it. -/
theorem Closed.not_HF_oneHeld : ¬ oneHeldClosed.HF := fun h => nomatch h ⟨0, Nat.one_pos⟩

/-- **The views do not certify the constant adapter beside `string`.** Its caller side is
    `string`, so the caller-side views overlap. -/
theorem Closed.viewsDisjoint_oneHeld_string :
    oneHeldClosed.viewsDisjoint (Closed.one .string) = false := by
  decide

end Calculus
