import Calculus.Dynamo.Alg.Frontier

/-!
# Non-malleability: a lawful codec has one attribute per value

A lawful codec is a canonical partial bijection, so each fibre of `p` holds at most one
attribute (`Lawful.fmt_subsingleton`): two attributes that read to one value are equal. This is
non-malleability in its equality form, the form the verified-formats community states for CBOR.

* **`Fmt` is derived, not assumed.** It is the fibre of `p`, so it is `Codec.Ker` seen from the
  other side, and `fmt_forced` shows that the two relational decode directions pin it.
* **`η` is stated against fibres.** `survivesStore_iff` is `η ⊆ ker p` against fibres. Under
  a canonical codec a fibre is one attribute, so the store must fix each attribute the codec
  writes. That is why `decimal`'s held set is the numerals the store returns unchanged.
* **A reader that drops names is not lawful** (`not_lawful_dropAll`). A reader that discards
  every name reads every `M` attribute to the empty map, so its `M` fragment is one fibre. So the
  model has no such rest policy: a rest policy refuses an undeclared name, or reads it with a
  codec in the open block.
-/

namespace Calculus

/-! ## The fibre of `p`, and why it is not a choice -/

/-- **`Codec.Ker`, seen from the other side.** `Ker` says two attributes share a fibre;
    `Fmt c v` is that fibre. A relational format `fmt : Value → Set Attr` is not a rival
    presentation of a codec — it is this function, and `fmt_forced` says so. -/
def Fmt (c : Codec) (v : Value) : Set Attr := {a | c.p a = some v}

/-- Membership in a fibre is the reading equation. Stated once so nothing below has to
    unfold `Set`. -/
theorem mem_Fmt {c : Codec} {v : Value} {a : Attr} : a ∈ Fmt c v ↔ c.p a = some v :=
  Iff.rfl

/-- Two attributes share a fibre exactly when `Ker` relates them and the fibre is inhabited
    by a value — the sentence "`Fmt` and `Ker` are one definition" in the only form that can
    be checked. -/
theorem ker_of_mem_Fmt {c : Codec} {v : Value} {a a' : Attr}
    (h : a ∈ Fmt c v) (h' : a' ∈ Fmt c v) : c.Ker a a' := by
  show c.p a = c.p a'
  rw [mem_Fmt.mp h, mem_Fmt.mp h']

/-- **The forcing lemma: `fmt` is not a design choice.** Any relation satisfying both decode
    directions — sound (`a ∈ fmt v` reads back to `v`) and complete (everything reading to `v`
    is in `fmt v`) — *is* the fibre of `p`, on the nose.

    A relational presentation of a codec is therefore the same model, addressed by fibre. -/
theorem fmt_forced {c : Codec} {fmt : Value → Set Attr}
    (sound : ∀ v a, a ∈ fmt v → c.p a = some v)
    (complete : ∀ v a, c.p a = some v → a ∈ fmt v) :
    fmt = Fmt c := by
  funext v
  apply Set.ext
  intro a
  exact ⟨sound v a, complete v a⟩

/-! ## The store premise, restated against fibres

`SurvivesStore` concedes that the store is not the identity
on attributes, and all a codec needs is that it moves within a fibre. Under a relational
format that sentence is unchanged — which is the point. -/

/-- **`η ⊆ ker p`, in the format's vocabulary.** Read left to right: whatever `e` writes for
    `v`, the store's rewrite of it still lies in `v`'s fibre.

    (R) is needed in both directions and that is not an artefact: `SurvivesStore` compares
    `η a` against `a`, while the right-hand side compares `η a` against the *value* `a` came
    from, and only retraction identifies the two. So a relational presentation does not
    remove `η`; it renames the same quantified statement, and still owes (R) to state it. -/
theorem survivesStore_iff {c : Codec} (h : Lawful c) (η : Attr → Attr) :
    SurvivesStore c η ↔ ∀ v a, c.e v = some a → η a ∈ Fmt c v := by
  constructor
  · intro hη v a he
    show c.p (η a) = some v
    rw [hη a ⟨v, he⟩, h.retract he]
  · intro hη a ⟨v, he⟩
    show c.p (η a) = c.p a
    rw [hη v a he, h.retract he]

/-! ## The fibre is one attribute -/

/-- **Non-malleability.** Two attributes that a lawful codec reads to one value are equal. -/
theorem Lawful.fmt_subsingleton {c : Codec} (h : Lawful c) {v a a'}
    (ha : a ∈ Fmt c v) (ha' : a' ∈ Fmt c v) : a = a' := by
  have e1 := h.canon (mem_Fmt.mp ha)
  rw [h.canon (mem_Fmt.mp ha')] at e1
  exact (Option.some.inj e1).symm

/-! ### Where it breaks: a reader that drops names

A reader that keeps no name discards everything it is given, so its `M` fragment is a single
fibre. The model gives this reader no term. The witness below is built by hand. -/

/-- The empty binding, at any payload type: `∅` names no key, so the payload function is
    total by vacuity. -/
def noEntries {α : Type} : MapOf α := ⟨∅, fun k => (Finset.notMem_empty _ k.2).elim⟩

/-- **The reader that drops every name**: it reads each `M` attribute to the empty map, and it
    writes nothing. -/
def dropAll : Codec :=
  Alg.Codec.ofEP (T := fun _ => True) (μ := none) (e := fun _ => none)
    (p := fun a => match a with
      | .m _ _ => some (mA.into noEntries)
      | _ => none)

/-- **Every `M` attribute reads to the empty map.** This one equation is the fibre. -/
theorem dropAll_p (keys : Finset Name) (f : {k // k ∈ keys} → Attr) :
    dropAll.p (.m keys f) = some (mA.into noEntries) := rfl

/-- **A reader that drops names is not lawful**: two maps read to the empty map, and the empty
    map writes one of them. -/
theorem not_lawful_dropAll : ¬ Lawful dropAll := by
  intro h
  have h1 := h.canon (dropAll_p {"x"} (fun _ => .null))
  have h2 := h.canon (dropAll_p ∅ (fun k => (Finset.notMem_empty _ k.2).elim))
  rw [h1] at h2
  have hk := congrArg (fun o => match o with | some (Attr.m k _) => k.card | _ => 0) h2
  exact absurd hk (by decide)

end Calculus
