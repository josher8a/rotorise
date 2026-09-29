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

/-- The image of a nonempty set under a function that answers `none` everywhere is `none`. -/
theorem neSetImage_none_all {α β : Type} [DecidableEq β] {f : α → Option β} (S : NEFinset α)
    (h : ∀ x, f x = none) : neSetImage f S = none := by
  obtain ⟨x, hx⟩ := S.2
  exact neSetImage_none (setImage_none_of hx (h x))

mutual
/-- The value that `Ω` writes to an attribute, by structure. The witness of `Ω_onto` is this
    function and not a choice, so the map case names its preimage without `Classical.choose`. -/
def valueOfAttr : Attr → Value
  | .s x => .str x
  | .n x => .num x
  | .b x => .bin x
  | .bool x => .bool x
  | .null => .null
  | .ss S => .strSet S
  | .ns S => .numSet S
  | .bs S => .binSet S
  | .l as => .arr (valueOfAttrL as)
  | .m keys g => .map keys (fun k => valueOfAttr (g k))
/-- …and on a list of attributes. -/
def valueOfAttrL : List Attr → List Value
  | [] => []
  | a :: as => valueOfAttr a :: valueOfAttrL as
end

mutual
/-- `Ω` writes each attribute from `valueOfAttr`. -/
theorem Ω_e_valueOfAttr : ∀ a : Attr, Ω.e (valueOfAttr a) = some a
  | .s _ => rfl
  | .n _ => rfl
  | .b _ => rfl
  | .bool _ => rfl
  | .null => rfl
  | .ss S => by
      show Ω.e (.strSet S) = _
      rw [Ωe_strSet]; unfold encSet
      rw [show (fun x : String => (Ω.e (Value.str x)).bind sC.out) = fun x => some x from rfl,
        neSetImage_id]
  | .ns S => by
      show Ω.e (.numSet S) = _
      rw [Ωe_numSet]; unfold encSet
      rw [neSetImage_none_all (f := fun x : WFNumeral => (Ω.e (Value.num x)).bind sC.out) S
          (fun _ => rfl),
        show (fun x : WFNumeral => (Ω.e (Value.num x)).bind nC.out) = fun x => some x from rfl,
        neSetImage_id]
  | .bs S => by
      show Ω.e (.binSet S) = _
      rw [Ωe_binSet]; unfold encSet
      rw [neSetImage_none_all (f := fun x : Bytes => (Ω.e (Value.bin x)).bind sC.out) S
          (fun _ => rfl),
        neSetImage_none_all (f := fun x : Bytes => (Ω.e (Value.bin x)).bind nC.out) S
          (fun _ => rfl),
        show (fun x : Bytes => (Ω.e (Value.bin x)).bind bC.out) = fun x => some x from rfl,
        neSetImage_id]; rfl
  | .l as => by
      show Ω.e (.arr (valueOfAttrL as)) = _
      rw [Ωe_arr, Ω_e_valueOfAttrL as]; rfl
  | .m keys g => by
      show Ω.e (.map keys (fun k => valueOfAttr (g k))) = _
      rw [Ωe_map, funImage_eq (f := g) (fun k => Ω_e_valueOfAttr (g k))]; rfl
/-- …and each list of attributes from `valueOfAttrL`. -/
theorem Ω_e_valueOfAttrL : ∀ as : List Attr, traverse Ω.e (valueOfAttrL as) = some as
  | [] => rfl
  | a :: as => by simp only [valueOfAttrL, traverse, Ω_e_valueOfAttr a, Ω_e_valueOfAttrL as]
end

/-- `Ω` writes every attribute: its write side is onto. -/
theorem Ω_onto (a : Attr) : ∃ v, Ω.e v = some a := ⟨_, Ω_e_valueOfAttr a⟩

/-- `Ω` reads only canonical attributes: `e ∘ p = id` on `dom(p)`. -/
theorem Ω_canon {a : Attr} {t : Value} (h : Ω.p a = some t) : Ω.e t = some a :=
  lawful_opaq.can_roundTrip (Ω_onto a) h

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
  have := h _ _ oneHeld_writes
  rw [denote_opaq, show (muCodec opaqStep).e (.str "1") = some (.s "1") from rfl] at this
  exact nomatch this

/-- `oneHeld` reads the number `1` as the string `"1"`. -/
theorem oneHeld_reads : (denote oneTable oneHeld).p (.n (WFNumeral.of "1")) = some (.str "1") := by
  rfl

/-- **The false control, read side.** `oneHeld` reads a value that `opaque` does not read at
    the same attribute, so `confluence_R` needs `HF`. -/
theorem held_violates_R :
    ¬ ∀ a v, (denote oneTable oneHeld).p a = some v → (denote oneTable .opaq).p a = some v := by
  intro h
  have := h _ _ oneHeld_reads
  rw [denote_opaq, show (muCodec opaqStep).p (.n (WFNumeral.of "1"))
    = some (.num (WFNumeral.of "1")) from rfl] at this
  exact nomatch this


/-- The control of the control: `oneHeld` is not held-free, so `confluence_W` does not
    apply to it. -/
theorem not_HF_oneHeld : ¬ HF oneHeld := nofun

/-- **The views do not certify the constant adapter beside `string`.** Its caller side is
    `string`, so the caller-side views overlap. -/
theorem certPair_oneHeld_string : certPair oneHeld .string = false := by
  decide

end Calculus
