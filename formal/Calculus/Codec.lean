import Calculus.Domain

/-!
# §2 — What a codec is, and its laws

The pair is data; the laws are a `Prop`-valued structure over it: a lawful codec is a canonical
partial bijection. The two §2 corollaries — (Q) and read-side (W) — are proved here.
-/

namespace Calculus

/-- §2: `c = (T, μ, e, p)`. -/
@[ext]
structure Codec where
  T : Value → Prop
  μ : Option Member
  e : Value → Option Attr
  p : Attr → Option Value

/-- The degenerate codec: empty domains everywhere. Laws hold vacuously — this is what
    `lazy` denotes at fuel 0 ("partiality is doing the termination argument's work"). -/
def Codec.empty : Codec :=
  { T := fun _ => False, μ := none, e := fun _ => none, p := fun _ => none }

/-! ## §2's two derived sets

`≈c` and `Can(c)` are §2's own vocabulary and both were unavailable to it: the kernel had no
name at all, and `Can` lived in `Equations.lean`, where §2 and §5 could not cite it. They are
here for the same reason `Lawful` is — a §2 device belongs in §2's file. -/

/-- §2's `≈c`: the kernel of the reading, `a ≈c a′ ⟺ p(a) = p(a′)`. The equivalence `e ∘ p`
    canonizes modulo — forced by `p`, not chosen.

    Not `Codec.Equiv`, which relates two *codecs* and is not transitive (`not_equiv_trans`).
    A kernel is; see `ker_equivalence`. -/
def Codec.Ker (c : Codec) (a a' : Attr) : Prop := c.p a = c.p a'

theorem Codec.Ker.refl (c : Codec) (a : Attr) : c.Ker a a := rfl

theorem Codec.Ker.symm {c : Codec} {a a' : Attr} (h : c.Ker a a') : c.Ker a' a :=
  Eq.symm h

theorem Codec.Ker.trans {c : Codec} {a a' a'' : Attr}
    (h : c.Ker a a') (h' : c.Ker a' a'') : c.Ker a a'' :=
  Eq.trans h h'

/-- `≈c` is an equivalence — because it is the kernel of a function, and for no other
    reason. The contrast with `Codec.Equiv` is the whole content of the remark on `Ker`. -/
theorem Codec.ker_equivalence (c : Codec) : Equivalence c.Ker :=
  ⟨Codec.Ker.refl c, Codec.Ker.symm, Codec.Ker.trans⟩

/-- §2's `Can(c) = e[T]`: the attributes some value actually writes. `e ∘ p` is total here
    and merely partial on `𝔸`; §6's `≈` rows are stated on it. -/
def Can (c : Codec) (a : Attr) : Prop := ∃ v, c.e v = some a

/-- §2 Laws: the codec is a canonical partial bijection. `(R)` retraction, `(C)` in the canonical
    form (a read at `a` of `t` writes `t` at `a`), and `(W)` member-naming. The `alternate reader`
    exemption is handled at the theorem (§5), not here: `Lawful` is the exemption-free bundle. -/
structure Lawful (c : Codec) : Prop where
  retract : ∀ {t a}, c.e t = some a → c.p a = some t
  canon   : ∀ {a t}, c.p a = some t → c.e t = some a
  writes  : ∀ {μ}, c.μ = some μ → ∀ {t a}, c.e t = some a → a.member = μ

/-- `(R)`, `(C)` as definedness, and `(W)` — what survives in a derivation containing
    `alternate reader` (§5 theorem, first residue). -/
structure LawfulCore (c : Codec) : Prop where
  retract : ∀ {t a}, c.e t = some a → c.p a = some t
  canon   : ∀ {a t}, c.p a = some t → (c.e t).isSome
  writes  : ∀ {μ}, c.μ = some μ → ∀ {t a}, c.e t = some a → a.member = μ

/-- A read value is writable. -/
theorem Lawful.defined {c : Codec} (h : Lawful c) {a t} (hp : c.p a = some t) :
    (c.e t).isSome := by
  rw [h.canon hp]; rfl

theorem Lawful.core {c : Codec} (h : Lawful c) : LawfulCore c :=
  ⟨h.retract, h.defined, h.writes⟩

/-- §2 Corollary (Q — stability): `∀ a ∈ dom(p). e(p(a)) ≈c a`. Retraction asked at values a
    *table* returned rather than a generator produced; what it adds to (R) is (C). -/
theorem Lawful.stable {c : Codec} (h : Lawful c) {a t a'}
    (hp : c.p a = some t) (he : c.e t = some a') : c.Ker a' a := by
  show c.p a' = c.p a
  rw [h.retract he, hp]

/-- §2 Corollary (read-side W): a member-naming codec accepts only its member. -/
theorem Lawful.reads {c : Codec} (h : Lawful c) {μ a t}
    (hμ : c.μ = some μ) (hp : c.p a = some t) : a.member = μ :=
  h.writes hμ (h.canon hp)

/-- §2 Corollary: **a member a codec cannot write is one it cannot read.** Canonical reads hold
    the pair's halves together, so a member absent from `ran(e)` is absent from `dom(p)`.

    Definedness alone does not see this: in the failing case `e (p a)` is defined and the value
    survives — just at a different member — and a `⊤`-membered term has no (W) to appeal to. -/
theorem Lawful.no_read_without_write {c : Codec} (h : Lawful c) {m : Member}
    (hw : ∀ {v a}, c.e v = some a → a.member ≠ m) {a v} (hm : a.member = m) :
    c.p a ≠ some v := by
  intro hp
  exact hw (h.canon hp) hm

/-- The contrapositive, in the form a port checks: if a member is readable, it is writable.
    `C1`'s audit list asks which terms touch a refined member; this asks the prior question
    of *any* member, and a `⊤`-membered term is where it has teeth. -/
theorem Lawful.write_of_read {c : Codec} (h : Lawful c) {a v} (hp : c.p a = some v) :
    ∃ a', c.e v = some a' ∧ a'.member = a.member :=
  ⟨a, h.canon hp, rfl⟩

/-- `(R)` makes `e` injective on its domain — the Lemma of §5's proof, consumed by the
    `set` case. -/
theorem Lawful.e_injective {c : Codec} (h : Lawful c) {t t' a}
    (he : c.e t = some a) (he' : c.e t' = some a) : t = t' := by
  have h2 := h.retract he'
  rw [h.retract he] at h2
  exact Option.some.inj h2

/-- The empty codec is lawful, vacuously. -/
theorem Lawful.empty : Lawful Codec.empty := by
  constructor <;> intros <;> simp_all [Codec.empty]

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
    mentions `T` — the four laws relate `e` and `p` to each other, not to the index — so
    this is the separate claim that the index is honest, and it is what makes `T` a
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

/-- **The ideal a codec is a deviation from**, stated so the deviation can be located.
    `(R)` gives `p ∘ e = id` on `dom(e)`; this gives `e ∘ p = id` on `Can(c)`. Together
    with `e_injective` they say that between the values a codec writes and the attributes
    it does write, `e` and `p` are **mutually inverse** — a bijection, on the nose, with
    no quotient and no partiality anywhere in sight.

    So §2's `e ∘ p ≠ id` is not a failure of the pair; it is a statement about the two
    places the bijection is *extended*. Off `Can(c)` but inside `dom(p)`, `e ∘ p` is the
    canonizer and the equivalence is `Ker` — the quotient half. Off `dom(e)` inside `T`,
    there is simply nothing to write — the partial half. Every law in §2 beyond `(R)` is
    about one of those two extensions, and nothing is about the bijection, because there
    is nothing to say about it. -/
theorem Lawful.can_roundTrip {c : Codec} (h : Lawful c) {a : Attr} {t : Value}
    (ha : Can c a) (hp : c.p a = some t) : c.e t = some a := by
  obtain ⟨t', ht'⟩ := ha
  rw [h.retract ht'] at hp
  cases hp
  exact ht'

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
