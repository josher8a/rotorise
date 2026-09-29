/-!
# §2 — The codec record and its laws, over any carriers

The laws of a codec relate `e` and `p` to each other. No law reads the structure of a value or
of an attribute. So the record and its laws take the carriers as parameters: `V` the caller's
values, `A` the stored attributes, and `M` the members. The one fact that (W) needs from the
store is the member of an attribute, and `Lawful` takes that function as a parameter.

The record holds one partial map for each orientation, from the caller side to the stored side
of the orientation. `e` is the map at the host, and `p` is the map at the dual.
-/

namespace Calculus.Alg

/-! ## The orientation -/

/-- **An orientation**: the absolute side of the caller and the absolute side of the stored
    carrier. The two sides differ, so an orientation is one of two values. -/
abbrev Orient : Type := {p : Bool × Bool // p.1 ≠ p.2}

/-- The dual orientation: the caller side and the stored side swap. -/
abbrev Orient.op (o : Orient) : Orient := ⟨(o.1.2, o.1.1), fun h => o.2 h.symm⟩

/-- The host orientation: the caller side is `false`, and the stored side is `true`. -/
abbrev Orient.host : Orient := ⟨(false, true), Bool.false_ne_true⟩

/-- The dual of the host. -/
abbrev Orient.dual : Orient := Orient.host.op

/-- **The dual of the dual is the orientation, on the nose.** -/
theorem Orient.op_op (o : Orient) : o.op.op = o := rfl

/-- **A property of every orientation** from the property at the host and at the dual. The two
    are the only orientations. -/
theorem Orient.both {P : Orient → Prop} (host : P Orient.host) (dual : P Orient.dual) :
    ∀ o, P o
  | ⟨(false, true), _⟩ => host
  | ⟨(true, false), _⟩ => dual
  | ⟨(false, false), h⟩ => absurd rfl h
  | ⟨(true, true), h⟩ => absurd rfl h

/-- The caller side of an orientation. -/
abbrev Orient.c (o : Orient) : Bool := o.1.1

/-- The stored side of an orientation. -/
abbrev Orient.s (o : Orient) : Bool := o.1.2

/-- The carrier at an absolute side: the values `V` at `false`, and the attributes `A` at
    `true`. -/
abbrev Side (V A : Type) : Bool → Type
  | false => V
  | true => A

/-- **A function at each absolute side**: `fV` at the values, and `fA` at the attributes. A
    predicate of each side and a depth of each side are such functions. -/
def Side.elim {V A X : Type} (fV : V → X) (fA : A → X) : (s : Bool) → Side V A s → X
  | false => fV
  | true => fA

/-- §2: `c = (T, μ, f)`, over the carriers `V`, `A` and `M`. `f o` is the partial map from the
    caller side of `o` to the stored side of `o`. -/
structure Codec (V A M : Type) where
  T : V → Prop
  μ : Option M
  f : (o : Orient) → Side V A o.c → Option (Side V A o.s)

variable {V A M : Type}

/-- The write: the map at the host. -/
abbrev Codec.e (c : Codec V A M) : V → Option A := c.f Orient.host

/-- The read: the map at the dual. -/
abbrev Codec.p (c : Codec V A M) : A → Option V := c.f Orient.dual

/-- The codec of a write and a read. -/
def Codec.ofEP (T : V → Prop) (μ : Option M) (e : V → Option A) (p : A → Option V) :
    Codec V A M where
  T := T
  μ := μ
  f
    | ⟨(false, true), _⟩ => e
    | ⟨(true, false), _⟩ => p
    | ⟨(false, false), h⟩ => absurd rfl h
    | ⟨(true, true), h⟩ => absurd rfl h

section OfEP
variable (T : V → Prop) (μ : Option M) (e : V → Option A) (p : A → Option V)

/-- The held set of `Codec.ofEP T μ e p` is `T`. -/
@[simp] theorem Codec.ofEP_T : (Codec.ofEP T μ e p).T = T := rfl

/-- The member of `Codec.ofEP T μ e p` is `μ`. -/
@[simp] theorem Codec.ofEP_μ : (Codec.ofEP T μ e p).μ = μ := rfl

/-- The write of `Codec.ofEP T μ e p` is `e`. `e` is no projection, so `simp only` needs this
    lemma by name. -/
@[simp] theorem Codec.ofEP_e : (Codec.ofEP T μ e p).e = e := rfl

/-- The read of `Codec.ofEP T μ e p` is `p`. `p` is no projection, so `simp only` needs this
    lemma by name. -/
@[simp] theorem Codec.ofEP_p : (Codec.ofEP T μ e p).p = p := rfl

end OfEP

/-- Two codecs with the same held set, member, write and read are equal. -/
@[ext]
theorem Codec.ext {c d : Codec V A M} (hT : c.T = d.T) (hμ : c.μ = d.μ) (he : c.e = d.e)
    (hp : c.p = d.p) : c = d := by
  cases c
  cases d
  congr
  funext o
  exact Orient.both (P := fun o => _ = _) he hp o

/-- The degenerate codec: empty domains everywhere. Laws hold vacuously. It is the first stage of
    a recursive term, and a variable that no binder gives. -/
def Codec.empty : Codec V A M :=
  { T := fun _ => False, μ := none, f := fun _ _ => none }

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

/-- §2 Laws: the codec is a canonical partial bijection. `inv` is one law over the orientation:
    the map at the dual inverts the map at each orientation. At the host `inv` is `(R)`
    retraction, and at the dual `inv` is `(C)` in the canonical form (a read at `a` of `t`
    writes `t` at `a`). `(W)` member-naming is one-sided, where `member` gives the member of an
    attribute. The `alternate reader` exemption is handled at the theorem (§5), not here:
    `Lawful` is the exemption-free bundle. -/
structure Lawful (member : A → M) (c : Codec V A M) : Prop where
  inv : ∀ {o : Orient} {x : Side V A o.c} {y : Side V A o.s}, c.f o x = some y → c.f o.op y = some x
  writes  : ∀ {μ}, c.μ = some μ → ∀ {t a}, c.e t = some a → member a = μ

variable {member : A → M}

/-- `(R)`: the one law at the host. -/
theorem Lawful.retract {c : Codec V A M} (h : Lawful member c) {t a} (he : c.e t = some a) :
    c.p a = some t := h.inv he

/-- `(C)`: the one law at the dual. -/
theorem Lawful.canon {c : Codec V A M} (h : Lawful member c) {a t} (hp : c.p a = some t) :
    c.e t = some a := h.inv hp

/-- The law from its two orientations. A proof that reads the asymmetric write and read of a
    combinator gives the two orientations apart. -/
theorem Lawful.ofRC {c : Codec V A M} (retract : ∀ {t a}, c.e t = some a → c.p a = some t)
    (canon : ∀ {a t}, c.p a = some t → c.e t = some a)
    (writes : ∀ {μ}, c.μ = some μ → ∀ {t a}, c.e t = some a → member a = μ) :
    Lawful member c where
  inv {o} := Orient.both (P := fun o => ∀ {x : Side V A o.c} {y : Side V A o.s},
    c.f o x = some y → c.f o.op y = some x) retract canon o
  writes := writes

/-- `(R)`, `(C)` as definedness, and `(W)` — what survives in a derivation containing
    `alternate reader` (§5 theorem, first residue). -/
structure LawfulCore (member : A → M) (c : Codec V A M) : Prop where
  retract : ∀ {t a}, c.e t = some a → c.p a = some t
  canon   : ∀ {a t}, c.p a = some t → (c.e t).isSome
  writes  : ∀ {μ}, c.μ = some μ → ∀ {t a}, c.e t = some a → member a = μ

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
  inv h := nomatch h
  writes _ _ _ h := nomatch h

/-- **The ideal a codec is a deviation from**, stated so the deviation can be located.
    `(R)` gives `p ∘ e = id` on `dom(e)`; this gives `e ∘ p = id` on `Can(c)`. Together
    with `e_injective` they say that between the values a codec writes and the attributes
    it does write, `e` and `p` are **mutually inverse** — a bijection, on the nose, with
    no quotient and no partiality anywhere in sight.

    A lawful codec has no canonizer. `canon` sends every read attribute to itself, so
    `dom(p) ⊆ Can(c)` and `Ker` is trivial on `dom(p)`. The quotient half, where `e ∘ p` is
    a canonizer and the equivalence is `Ker`, belongs to `LawfulCore`, whose `canon` asks only
    that a read value be writable: that is an alternate reader. Off `dom(e)` inside `T`, there
    is nothing to write: that is the partial half. -/
theorem Lawful.can_roundTrip {c : Codec V A M} (h : Lawful member c) {a : A} {t : V}
    (ha : Can c a) (hp : c.p a = some t) : c.e t = some a := by
  obtain ⟨t', ht'⟩ := ha
  rw [h.retract ht'] at hp
  cases hp
  exact ht'

end Calculus.Alg
