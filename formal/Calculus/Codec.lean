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

/-- §2 Corollary (Q — stability): `e (p a) ≈c a`, i.e. the re-encoding reads back to the
    same value — `ker p` relates the canonical attribute to the one read. -/
theorem Lawful.stable {c : Codec} (h : Lawful c) {a t a'}
    (hp : c.p a = some t) (he : c.e t = some a') : c.p a' = c.p a := by
  rw [h.retract he, hp]

/-- §2 Corollary (read-side W): a member-naming codec accepts only its member. -/
theorem Lawful.reads {c : Codec} (h : Lawful c) {μ a t}
    (hμ : c.μ = some μ) (hp : c.p a = some t) : a.member = μ := by
  obtain ⟨a', he⟩ := Option.isSome_iff_exists.mp (h.canon hp)
  have hm := (h.agree hp he).member_eq
  rw [← hm, h.writes hμ he]

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

end Calculus
