import Calculus.Dynamo.Analysis.Universal

variable {α : Calculus.Table}

/-!
# Confluence: the payoffs of a held-free term

`HeldFree.lean` proves that a held-free term is a restriction of `opaque` on both halves
(`sub_denote`, `confluence_W`, `confluence_R`). This file holds what follows from it.

The payoffs follow from one fact: `opaque`'s pair is a bijection between `Value` and `Attr`.
`Ω_onto` and `Ω_canon` prove the bijection. So two held-free terms that both write a value
write one attribute (`write_agree`), and two that both read an attribute read one value
(`read_agree`).

`held` is the one constructor outside the result. An adapter changes the carrier, so it is
not a restriction of `opaque`. `held_violates_W` and `held_violates_R` are the control:
`oneHeld` writes `"1"` as the number `1`, which `opaque` does not.
-/

namespace Calculus

/-! ## Payoffs -/

/-- Two held-free terms that both write a value write one attribute. -/
theorem write_agree {s t : Term} (hs : HF s) (ht : HF t) {v a b}
    (ha : (denote α s).e v = some a) (hb : (denote α t).e v = some b) : a = b :=
  Option.some.inj ((confluence_W hs ha).symm.trans (confluence_W ht hb))

/-- Two held-free terms that both read an attribute read one value. -/
theorem read_agree {s t : Term} (hs : HF s) (ht : HF t) {a v w}
    (hv : (denote α s).p a = some v) (hw : (denote α t).p a = some w) : v = w :=
  Option.some.inj ((confluence_R hs hv).symm.trans (confluence_R ht hw))

/-- `Ω` writes every attribute: its write side is onto. -/
theorem Ω_onto (a : Attr) : ∃ v, Ω.e v = some a := ⟨a, rfl⟩

/-- `Ω` reads only canonical attributes: `e ∘ p = id` on `dom(p)`. -/
theorem Ω_canon {a : Attr} {t : Value} (h : Ω.p a = some t) : Ω.e t = some a := by
  cases h; rfl

/-- Each member of a held-free list is held-free. -/
theorem HFL_mem : ∀ {ts : List Term}, HFL ts → ∀ t ∈ ts, HF t
  | [], _, _, h => nomatch h
  | _ :: _, h, t, hm => by
      simp only [HFL, Alg.hasHeldL, Bool.or_eq_false_iff] at h
      rcases List.mem_cons.mp hm with rfl | hm
      · exact h.1
      · exact HFL_mem h.2 t hm


/-! ## The false control: a `held` adapter is not a restriction of `opaque` -/

/-- The numeric base under a constant adapter, with the caller side restricted to text. The
    adapter writes each text as the number `1`, and reads each number as the text `"1"`. -/
def oneHeld : Term := Term.held false Term.number Term.string (.caller 0, false) []

/-- The table that gives each generator the constant adapter of `oneHeld`. -/
def oneTable : Table := fun _ => (fun _ => Value.num (WFNumeral.of "1"), fun _ => Value.str "1")

/-- `oneHeld` writes the string `"1"` as the number `1`. -/
theorem oneHeld_writes : (denote oneTable oneHeld).e (.str "1") = some (.n (WFNumeral.of "1")) := by
  rfl

/-- **The false control, write side.** `oneHeld` writes an attribute that `opaque` does not
    write at the same value, so `confluence_W` needs `HF`. -/
theorem held_violates_W :
    ¬ ∀ v a, (denote oneTable oneHeld).e v = some a → (denote oneTable .opaq).e v = some a := by
  intro h
  exact absurd (Option.some.inj (h _ _ oneHeld_writes)) (fun h => nomatch h)

/-- `oneHeld` reads the number `1` as the string `"1"`. -/
theorem oneHeld_reads : (denote oneTable oneHeld).p (.n (WFNumeral.of "1")) = some (.str "1") := by
  rfl

/-- **The false control, read side.** `oneHeld` reads a value that `opaque` does not read at
    the same attribute, so `confluence_R` needs `HF`. -/
theorem held_violates_R :
    ¬ ∀ a v, (denote oneTable oneHeld).p a = some v → (denote oneTable .opaq).p a = some v := by
  intro h
  exact absurd (Option.some.inj (h _ _ oneHeld_reads)) (fun h => nomatch h)


/-- The control of the control: `oneHeld` is not held-free, so `confluence_W` does not
    apply to it. -/
theorem not_HF_oneHeld : ¬ HF oneHeld := nofun

/-- **The views do not certify the constant adapter beside `string`.** Its caller side is
    `string`, so the caller-side views overlap. -/
theorem certPair_oneHeld_string : certPair oneHeld .string = false := by
  decide

end Calculus
