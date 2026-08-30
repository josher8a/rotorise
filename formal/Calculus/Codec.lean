import Calculus.Domain

/-!
# §2 — What a codec is, and its laws

The pair is data; the laws are a `Prop`-valued structure over it. `(MP)` is carried in the
strong form `Agree` (the doc's `≼`), from which the top-level member law is a corollary.
The two §2 corollaries — (Q) and read-side (W) — are proved here, exactly as in the doc.
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

/-- §5's `≼`: recursive member agreement. `L` compares pointwise on shared positions,
    `M` pointwise on shared names, sets no deeper than the member (payloads carry no
    member to disagree on). -/
inductive Agree : Attr → Attr → Prop where
  | s    (x y : String)  : Agree (.s x) (.s y)
  | n    (x y : Numeral) : Agree (.n x) (.n y)
  | b    (x y : Bytes)   : Agree (.b x) (.b y)
  | bool (x y : Bool)    : Agree (.bool x) (.bool y)
  | null                 : Agree .null .null
  | ss   (x y : List String)  : Agree (.ss x) (.ss y)
  | ns   (x y : List Numeral) : Agree (.ns x) (.ns y)
  | bs   (x y : List Bytes)   : Agree (.bs x) (.bs y)
  | l    (xs ys : List Attr)
         (h : ∀ q ∈ List.zip xs ys, Agree q.1 q.2) : Agree (.l xs) (.l ys)
  | m    (xs ys : List (Name × Attr))
         (h : ∀ k a a', xs.lookup k = some a → ys.lookup k = some a' → Agree a a') :
         Agree (.m xs) (.m ys)

/-- `≼` implies plain member equality — (MP) as §2 states it. -/
theorem Agree.member_eq {a a' : Attr} (h : Agree a a') : a.member = a'.member := by
  cases h <;> rfl

/-- §2 Laws. `(R)` retraction, `(C)` canonizability, `(W)` member-naming, and `(MP)` in
    §5's strong form. The `legacy` exemption is handled at the theorem (§5), not here:
    `Lawful` is the exemption-free bundle. -/
structure Lawful (c : Codec) : Prop where
  retract : ∀ {t a}, c.e t = some a → c.p a = some t
  canon   : ∀ {a t}, c.p a = some t → (c.e t).isSome
  writes  : ∀ {μ}, c.μ = some μ → ∀ {t a}, c.e t = some a → a.member = μ
  agree   : ∀ {a t a'}, c.p a = some t → c.e t = some a' → Agree a' a

/-- `(R)`, `(C)`, `(W)` without `(MP)` — what survives in a derivation containing
    `legacy` (§5 theorem, first residue). -/
structure LawfulCore (c : Codec) : Prop where
  retract : ∀ {t a}, c.e t = some a → c.p a = some t
  canon   : ∀ {a t}, c.p a = some t → (c.e t).isSome
  writes  : ∀ {μ}, c.μ = some μ → ∀ {t a}, c.e t = some a → a.member = μ

theorem Lawful.core {c : Codec} (h : Lawful c) : LawfulCore c :=
  ⟨h.retract, h.canon, h.writes⟩

/-- §2 Corollary (Q — stability): `∀ a ∈ dom(p). e(p(a)) ≈c a`. Retraction asked at values a
    *table* returned rather than a generator produced; what it adds to (R) is (C). -/
theorem Lawful.stable {c : Codec} (h : Lawful c) {a t a'}
    (hp : c.p a = some t) (he : c.e t = some a') : c.Ker a' a := by
  show c.p a' = c.p a
  rw [h.retract he, hp]

/-- §2 Corollary (read-side W): a member-naming codec accepts only its member. -/
theorem Lawful.reads {c : Codec} (h : Lawful c) {μ a t}
    (hμ : c.μ = some μ) (hp : c.p a = some t) : a.member = μ := by
  obtain ⟨a', he⟩ := Option.isSome_iff_exists.mp (h.canon hp)
  have hm := (h.agree hp he).member_eq
  rw [← hm, h.writes hμ he]

/-- §2 Corollary: **a member a codec cannot write is one it cannot read.** (MP) holds the
    pair's halves together, so a member absent from `ran(e)` is absent from `dom(p)`.

    Only (MP) sees this: in the failing case `e (p a)` is defined and the value survives —
    just at a different member — and a `⊤`-membered term has no (W) to appeal to. -/
theorem Lawful.no_read_without_write {c : Codec} (h : Lawful c) {m : Member}
    (hw : ∀ {v a}, c.e v = some a → a.member ≠ m) {a v} (hm : a.member = m) :
    c.p a ≠ some v := by
  intro hp
  obtain ⟨a', he⟩ := Option.isSome_iff_exists.mp (h.canon hp)
  exact hw he (((h.agree hp he).member_eq).trans hm)

/-- The contrapositive, in the form a port checks: if a member is readable, it is writable.
    `C1`'s audit list asks which terms touch a refined member; this asks the prior question
    of *any* member, and a `⊤`-membered term is where it has teeth. -/
theorem Lawful.write_of_read {c : Codec} (h : Lawful c) {a v} (hp : c.p a = some v) :
    ∃ a', c.e v = some a' ∧ a'.member = a.member := by
  obtain ⟨a', he⟩ := Option.isSome_iff_exists.mp (h.canon hp)
  exact ⟨a', he, (h.agree hp he).member_eq⟩

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

/-- §3 `(legacy)`: `ran(r) ⊆ dom(e)` — a migration lands on writable values — and
    coherence, the legacy reading agreeing with the current one on their overlap. -/
def ReadsCoherently (c : Codec) (r : Attr → Option Value) : Prop :=
  (∀ a v, r a = some v → (c.e v).isSome) ∧
  (∀ a v, r a = some v → ∀ v', c.p a = some v' → v = v')

/-- §3 `(nullable)`: `c` speaks of `NULL` only for `null`, in both directions —
    write-honesty then read-honesty. §5 records that these are (U) for the two-option
    sum `union(c, ⟨NULL⟩-point)`, specialised. -/
def NullHonest (c : Codec) : Prop :=
  (∀ v a, c.e v = some a → a = .null → v = .null) ∧
  (∀ a v, c.p a = some v → v = .null → a = .null)

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

/-! ## §1's store, as a premise

§2 composes `e` and `p` directly. In use there is a store between them and it is not the
identity on attributes, which `Domain.lean` states in prose and answers with
`Numeral.Stored`. This is the premise itself. -/

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
