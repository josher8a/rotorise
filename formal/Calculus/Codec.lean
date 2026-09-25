import Calculus.Domain
import Calculus.Alg

/-!
# §2 — What a codec is, and its laws

The pair is data; the laws are a `Prop`-valued structure over it: a lawful codec is a canonical
partial bijection. The record and its laws take the carriers as parameters. This file instantiates
them at `Value`, `Attr` and `Member`, and states the side conditions over the instance.
-/

namespace Calculus

/-- §2: `c = (T, μ, e, p)`, at the DynamoDB carriers. -/
abbrev Codec := Alg.Codec Value Attr Member

/-- §2 Laws at the DynamoDB carriers: (W) reads the member of an attribute. -/
abbrev Lawful := Alg.Lawful (V := Value) Attr.member

/-- §2 core laws at the DynamoDB carriers. -/
abbrev LawfulCore := Alg.LawfulCore (V := Value) Attr.member

/- An `export` alias whose first explicit parameter is the generic record captures field
   notation, and Lean then refuses the argument of the abbreviation. So only the names that no
   caller reaches by field notation get an alias. Field notation reaches the others through the
   abbreviation. -/
export Alg (Can)

namespace Codec
export Alg.Codec (ext ext_iff empty Ker.refl Ker.symm Ker.trans)
end Codec

namespace Lawful
export Alg.Lawful (empty)
end Lawful

/-! ## §3's side conditions, named

Three rules carry premises about the pair rather than about the index, and §3 names each
of them in prose. Naming them here too is what keeps `Obligations` readable and stops
every use site restating the proposition: a case that consumes one of these says which
condition it is consuming. -/

/-- §3 `(held)`: the iso cancels **on the carriers** — `T ≃ I`, in the domain-restricted
    form the laws actually need. `g ∘ f = id` where `f` lands writable, `f ∘ g = id` on
    the writable values themselves. -/
def IsoCancels (c : Codec) (f g : Value → Value) : Prop :=
  (∀ v, (c.e (f v)).isSome → g (f v) = v) ∧
  (∀ v, (c.e v).isSome → f (g v) = v)

/-- §3 `(alternate reader)`: `ran(r) ⊆ dom(e)` — a migration lands on writable values — and
    coherence, the legacy reading agreeing with the current one on their overlap. -/
def ReadsCoherently (c : Codec) (r : Attr → Option Value) : Prop :=
  (∀ a v, r a = some v → (c.e v).isSome) ∧
  (∀ a v, r a = some v → ∀ v', c.p a = some v' → v = v')

/-- §3 types the pair *on the held set*: `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T`. `Lawful` never
    mentions `T`, because retract, canon and writes relate `e` and `p` to each other and not to
    the index. So this is the separate claim that the index is honest, and it is what makes `T` a
    checked part of the judgement rather than a decoration. -/
structure Carrier (c : Codec) : Prop where
  /-- `e : T ⇀ 𝔸` — nothing outside the held set is written. -/
  domE : ∀ {v a}, c.e v = some a → c.T v
  /-- `p : 𝔸 ⇀ T` — nothing outside the held set is read. -/
  ranP : ∀ {a v}, c.p a = some v → c.T v

/-- The empty codec is on its (empty) carrier, vacuously. -/
theorem Carrier.empty : Carrier Codec.empty := by
  refine ⟨?_, ?_⟩ <;> intro _ _ h <;> exact nomatch h

/-- `Can(c)` is §2's `e[T]` — and it takes `Carrier` to say so: without `domE` a codec could
    write from a value it does not hold, making `Can` larger than the image. -/
theorem can_iff_image {c : Codec} (h : Carrier c) {a : Attr} :
    Can c a ↔ ∃ v, c.T v ∧ c.e v = some a := by
  constructor
  · rintro ⟨v, hv⟩; exact ⟨v, h.domE hv, hv⟩
  · rintro ⟨v, -, hv⟩; exact ⟨v, hv⟩

/-! ## §1's store, as a premise

§2 composes `e` and `p` directly. In use there is a store between them and it is not the
identity on attributes. The DynamoDB port (`DynamoDB.lean`) answers it with
`Numeral.Stored`. This is the premise itself, for every store. -/

/-- **`η ⊆ ker p`** — §1's concession, as a proposition. Quantified over `Can(c)` because
    `η` only ever sees what `e` wrote. Buys `retract_through_store`: (R) through the store. -/
def SurvivesStore (c : Codec) (η : Attr → Attr) : Prop :=
  ∀ a, Can c a → c.Ker (η a) a

/-- **(R), through the store.** `η ⊆ ker p` is exactly what makes a codec survive a round
    trip that passes through DynamoDB rather than through `Option` — and it is all it takes,
    which is why §1 could answer the whole problem by narrowing one held set. -/
theorem Lawful.retract_through_store {c : Codec} (h : Lawful c) {η : Attr → Attr}
    (hη : SurvivesStore c η) {t a} (he : c.e t = some a) : c.p (η a) = some t := by
  have hk : c.p (η a) = c.p a := hη a ⟨t, he⟩
  rw [hk, h.retract he]

end Calculus
