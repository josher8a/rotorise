/-!
# §2 — The codec record and its laws, over any carriers

The laws of a codec relate `e` and `p` to each other. No law reads the structure of a value or
of an attribute. So the record and its laws take the carriers as parameters: `V` the caller's
values, `A` the stored attributes, and `M` the members. The one fact that (W) needs from the
store is the member of an attribute, and `Lawful` takes that function as a parameter.
-/

namespace Calculus.Alg

/-- §2: `c = (T, μ, e, p)`, over the carriers `V`, `A` and `M`. -/
@[ext]
structure Codec (V A M : Type) where
  T : V → Prop
  μ : Option M
  e : V → Option A
  p : A → Option V

variable {V A M : Type}

/-- The degenerate codec: empty domains everywhere. Laws hold vacuously. It is the first stage of
    a recursive term, and a variable that no binder gives. -/
def Codec.empty : Codec V A M :=
  { T := fun _ => False, μ := none, e := fun _ => none, p := fun _ => none }

/-! ## §2's two derived sets -/

/-- §2's `≈c`: the kernel of the reading, `a ≈c a′ ⟺ p(a) = p(a′)`. The equivalence `e ∘ p`
    canonizes modulo — forced by `p`, not chosen.

    Not `Codec.Equiv`, which relates two *codecs* and is not transitive (`not_equiv_trans`).
    A kernel is; see `ker_equivalence`. -/
def Codec.Ker (c : Codec V A M) (a a' : A) : Prop := c.p a = c.p a'

theorem Codec.Ker.refl (c : Codec V A M) (a : A) : c.Ker a a := rfl

theorem Codec.Ker.symm {c : Codec V A M} {a a' : A} (h : c.Ker a a') : c.Ker a' a :=
  Eq.symm h

theorem Codec.Ker.trans {c : Codec V A M} {a a' a'' : A}
    (h : c.Ker a a') (h' : c.Ker a' a'') : c.Ker a a'' :=
  Eq.trans h h'

/-- `≈c` is an equivalence — because it is the kernel of a function, and for no other
    reason. The contrast with `Codec.Equiv` is the whole content of the remark on `Ker`. -/
theorem Codec.ker_equivalence (c : Codec V A M) : Equivalence c.Ker :=
  ⟨Codec.Ker.refl c, Codec.Ker.symm, Codec.Ker.trans⟩

/-- §2's `Can(c) = e[T]`: the attributes some value actually writes. `e ∘ p` is total here
    and merely partial on `A`; §6's `≈` rows are stated on it. -/
def Can (c : Codec V A M) (a : A) : Prop := ∃ v, c.e v = some a

/-- §2 Laws: the codec is a canonical partial bijection. `(R)` retraction, `(C)` in the canonical
    form (a read at `a` of `t` writes `t` at `a`), and `(W)` member-naming, where `member` gives
    the member of an attribute. The `alternate reader` exemption is handled at the theorem (§5),
    not here: `Lawful` is the exemption-free bundle. -/
structure Lawful (member : A → M) (c : Codec V A M) : Prop where
  retract : ∀ {t a}, c.e t = some a → c.p a = some t
  canon   : ∀ {a t}, c.p a = some t → c.e t = some a
  writes  : ∀ {μ}, c.μ = some μ → ∀ {t a}, c.e t = some a → member a = μ

/-- `(R)`, `(C)` as definedness, and `(W)` — what survives in a derivation containing
    `alternate reader` (§5 theorem, first residue). -/
structure LawfulCore (member : A → M) (c : Codec V A M) : Prop where
  retract : ∀ {t a}, c.e t = some a → c.p a = some t
  canon   : ∀ {a t}, c.p a = some t → (c.e t).isSome
  writes  : ∀ {μ}, c.μ = some μ → ∀ {t a}, c.e t = some a → member a = μ

variable {member : A → M}

/-- A read value is writable. -/
theorem Lawful.defined {c : Codec V A M} (h : Lawful member c) {a t} (hp : c.p a = some t) :
    (c.e t).isSome := by
  rw [h.canon hp]; rfl

theorem Lawful.core {c : Codec V A M} (h : Lawful member c) : LawfulCore member c :=
  ⟨h.retract, h.defined, h.writes⟩

/-- §2 Corollary (Q — stability): `∀ a ∈ dom(p). e(p(a)) ≈c a`. Retraction asked at values a
    *table* returned rather than a generator produced; what it adds to (R) is (C). -/
theorem Lawful.stable {c : Codec V A M} (h : Lawful member c) {a t a'}
    (hp : c.p a = some t) (he : c.e t = some a') : c.Ker a' a := by
  show c.p a' = c.p a
  rw [h.retract he, hp]

/-- §2 Corollary (read-side W): a member-naming codec accepts only its member. -/
theorem Lawful.reads {c : Codec V A M} (h : Lawful member c) {μ a t}
    (hμ : c.μ = some μ) (hp : c.p a = some t) : member a = μ :=
  h.writes hμ (h.canon hp)

/-- §2 Corollary: **a member a codec cannot write is one it cannot read.** Canonical reads hold
    the pair's halves together, so a member absent from `ran(e)` is absent from `dom(p)`.

    Definedness alone does not see this: in the failing case `e (p a)` is defined and the value
    survives — just at a different member — and a `⊤`-membered term has no (W) to appeal to. -/
theorem Lawful.no_read_without_write {c : Codec V A M} (h : Lawful member c) {m : M}
    (hw : ∀ {v a}, c.e v = some a → member a ≠ m) {a v} (hm : member a = m) :
    c.p a ≠ some v := by
  intro hp
  exact hw (h.canon hp) hm

/-- The contrapositive, in the form a port checks: if a member is readable, it is writable.
    `C1`'s audit list asks which terms touch a refined member; this asks the prior question
    of *any* member, and a `⊤`-membered term is where it has teeth. -/
theorem Lawful.write_of_read {c : Codec V A M} (h : Lawful member c) {a v}
    (hp : c.p a = some v) : ∃ a', c.e v = some a' ∧ member a' = member a :=
  ⟨a, h.canon hp, rfl⟩

/-- `(R)` makes `e` injective on its domain — the Lemma of §5's proof, consumed by the
    `set` case. -/
theorem Lawful.e_injective {c : Codec V A M} (h : Lawful member c) {t t' a}
    (he : c.e t = some a) (he' : c.e t' = some a) : t = t' := by
  have h2 := h.retract he'
  rw [h.retract he] at h2
  exact Option.some.inj h2

/-- The empty codec is lawful, vacuously. -/
theorem Lawful.empty : Lawful member (Codec.empty : Codec V A M) where
  retract h := nomatch h
  canon h := nomatch h
  writes _ _ _ h := nomatch h

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
theorem Lawful.can_roundTrip {c : Codec V A M} (h : Lawful member c) {a : A} {t : V}
    (ha : Can c a) (hp : c.p a = some t) : c.e t = some a := by
  obtain ⟨t', ht'⟩ := ha
  rw [h.retract ht'] at hp
  cases hp
  exact ht'

end Calculus.Alg
