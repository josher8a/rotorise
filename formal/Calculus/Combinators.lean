import Calculus.Lists
import Calculus.Codec

/-!
# Certified combinators

The semantic constructions the denotation factors through, each carrying its own
lawfulness lemma — so soundness becomes plumbing rather than eighteen bespoke cases.
The inventory mirrors the doc's own analysis (§7: products and coproducts are the
irreducible structure; everything else wraps one subterm):

* ground codecs — one per §3 ground term — **proved**;
* `through` / `restrict` — the iso/prism pair (`held`, `refine`/`numeric`), the
  invertible-syntax-descriptions combinator the doc cites — **proved**;
* `extendRead` — the agreeing extension of the reading (`legacy`) — core laws
  **proved**; (MP) is the sanctioned breach and has no lemma, by design;
* `orNull` — `nullable`, whose honesty premises are (U) for a two-option sum,
  specialised — **proved**;
* the **traversal toolkit** (`traverse` and the round-trip / definedness /
  pointwise-relation lemmas — **proved**): the one proof shape shared by every
  product. `drop` is a *filter*, not a traversal mode, and `tuple` is `align` +
  `traverse` — so nothing needs a second toolkit;
* products — `carriedCodec`, a payload pair carried between two prisms, is the shape
  underneath all of them; `entrywise` is it at a traversal (hence `arrayCodec` and
  `recordCodec`), `tupleCodec` it at `align` + a traversal, where the one fact worth
  proving is that alignment depends on a row's *length* alone (`slots`, `align_eq_some`).
  `setCodec` and `objectCodec` are argued on their own;
* sums — `altCodec` over `OptionSem`s that carry their *admission as data*, with
  `UniqueAdmission` ((U) as a premise). `dunionCodec` is `altCodec` over
  tag-admission options — "the one union whose (U) is a theorem" (doc §5) is
  literally `uniqueAdmission_byTag`. `opaqCodec` is `altCodec`'s fueled fixpoint
  over everything self-identifying — its (U) is `uniqueAdmission_of_kinds`, and
  the `refuse` policy is the absence of the number option.
-/

namespace Calculus

noncomputable section

/-! ## Constructors as prisms

The shape this file is built out of. A constructor viewed as a partial iso onto its image
is the prism §7 of the specification already names when it calls `held` and `refine` "the
same shape at different strengths". Two families turn out to be instances, and each was
written out once per constructor before it was named:

* the **point ground codecs** (`pointCodec` below) — `string`, `boolean`, `binary` and
  `null` are a payload carried between a value constructor and an attribute constructor,
  differing in nothing but which pair;
* the **wire-set payload projections** (`sC`/`nC`/`bC`, under Products) — the same
  traversal three times.

Naming the shape once is what lets §2's four laws be discharged once for each family
rather than once per constructor. -/

/-- A constructor, as a partial iso onto its image. -/
structure Ctor (α β : Type) where
  /-- Build. -/
  into : α → β
  /-- Match, partially. -/
  out : β → Option α
  /-- Matching what was built returns it. -/
  out_into : ∀ x, out (into x) = some x
  /-- Anything that matches was built. -/
  into_out : ∀ {b x}, out b = some x → b = into x

/-! ### The prisms, value side and attribute side -/

/-- `str` values. -/ def strV : Ctor String Value where
  into := Value.str
  out := fun v => match v with | .str s => some s | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `bool` values. -/ def boolV : Ctor Bool Value where
  into := Value.bool
  out := fun v => match v with | .bool b => some b | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `bin` values. -/ def binV : Ctor Bytes Value where
  into := Value.bin
  out := fun v => match v with | .bin b => some b | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- The `null` *point*: a prism with a trivial payload, which is what makes `null` an
    instance of the same shape as the three that carry data. -/
def nullV : Ctor Unit Value where
  into := fun _ => .null
  out := fun v => match v with | .null => some () | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `S`'s payload. -/ def sC : Ctor String Attr where
  into := Attr.s
  out := fun a => match a with | .s v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `N`'s payload. -/ def nC : Ctor Numeral Attr where
  into := Attr.n
  out := fun a => match a with | .n v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `B`'s payload. -/ def bC : Ctor Bytes Attr where
  into := Attr.b
  out := fun a => match a with | .b v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `BOOL`'s payload. -/ def boolA : Ctor Bool Attr where
  into := Attr.bool
  out := fun a => match a with | .bool v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `NULL`'s point. -/ def nullA : Ctor Unit Attr where
  into := fun _ => .null
  out := fun a => match a with | .null => some () | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-! ### The container prisms

The same shape one level up: a constructor whose payload is a *list* of entries. `L` and
`M` are the two §1 provides on the attribute side, `arr` and `map` the two §3 writes into
them. Naming them is what lets `array` and `record` be one construction (`entrywise`,
under Products) rather than two. -/

/-- `arr` values. -/ def arrV : Ctor (List Value) Value where
  into := Value.arr
  out := fun v => match v with | .arr xs => some xs | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `map` values. -/ def mapV : Ctor (List (Name × Value)) Value where
  into := Value.map
  out := fun v => match v with | .map xs => some xs | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `L`'s payload. -/ def lA : Ctor (List Attr) Attr where
  into := Attr.l
  out := fun a => match a with | .l xs => some xs | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `M`'s payload. -/ def mA : Ctor (List (Name × Attr)) Attr where
  into := Attr.m
  out := fun a => match a with | .m xs => some xs | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- **The point ground codecs of §3**, as one construction: a payload carried between a
    value constructor and an attribute constructor, both prisms.

    The prism laws are exactly §2's laws in disguise — `out_into` is the round trip **(R)**
    and `into_out` is canonizability **(C)** — which is why `lawful_pointCodec` needs no
    hypothesis about either side beyond the member it stamps. -/
def pointCodec {α : Type} (V : Ctor α Value) (A : Ctor α Attr) (μ₀ : Member) : Codec :=
  { T := fun v => ∃ x, v = V.into x
    μ := some μ₀
    e := fun v => (V.out v).map A.into
    p := fun a => (A.out a).map V.into }

/-! ## Ground codecs (§3) -/

def stringCodec : Codec :=
  { T := fun v => ∃ s, v = .str s
    μ := some .S
    e := fun v => match v with | .str s => some (.s s) | _ => none
    p := fun a => match a with | .s s => some (.str s) | _ => none }

def numberCodec : Codec :=
  { T := fun v => ∃ d, v = .num d
    μ := some .N
    e := fun v => match v with | .num d => some (.n d.toDec) | _ => none
    p := fun a => match a with | .n x => (Double.ofDec x).map Value.num | _ => none }

/-- §3 `(decimal)`. The held set is §1's `Numerals`, not every string: the grammar, the
    38 significant digits and the magnitude range are checked on both halves. The read
    side has to check as well — an ill-formed numeral admitted by `p` would name a value
    `e` then refuses, and that is **(C)** failing. -/
def decimalCodec : Codec :=
  { T := fun v => ∃ s, v = .str s ∧ Numeral.WF s = true
    μ := some .N
    e := fun v => match v with
      | .str s => if Numeral.WF s then some (.n s) else none
      | _ => none
    p := fun a => match a with
      | .n x => if Numeral.WF x then some (.str x) else none
      | _ => none }

def numericCodec (q : Double → Bool) : Codec :=
  { T := fun v => ∃ d, q d ∧ v = .num d
    μ := some .N
    e := fun v => match v with
      | .num d => if q d then some (.n d.toDec) else none
      | _ => none
    p := fun a => match a with
      | .n x => (Double.ofDec x).bind fun d => if q d then some (.num d) else none
      | _ => none }

def booleanCodec : Codec :=
  { T := fun v => ∃ b, v = .bool b
    μ := some .BOOL
    e := fun v => match v with | .bool b => some (.bool b) | _ => none
    p := fun a => match a with | .bool b => some (.bool b) | _ => none }

def binaryCodec : Codec :=
  { T := fun v => ∃ b, v = .bin b
    μ := some .B
    e := fun v => match v with | .bin b => some (.b b) | _ => none
    p := fun a => match a with | .b b => some (.bin b) | _ => none }

/-- The `NULL` point: one value, one attribute. A building block of `opaqCodec`. -/
def nullCodec : Codec :=
  { T := fun v => v = .null
    μ := some .NULL
    e := fun v => match v with | .null => some .null | _ => none
    p := fun a => match a with | .null => some .null | _ => none }

def literalSCodec (ls : List String) : Codec :=
  { T := fun v => ∃ s, s ∈ ls ∧ v = .str s
    μ := some .S
    e := fun v => match v with
      | .str s => if s ∈ ls then some (.s s) else none
      | _ => none
    p := fun a => match a with
      | .s s => if s ∈ ls then some (.str s) else none
      | _ => none }

def literalNCodec (ls : List Double) : Codec :=
  { T := fun v => ∃ d, d ∈ ls ∧ v = .num d
    μ := some .N
    e := fun v => match v with
      | .num d => if d ∈ ls then some (.n d.toDec) else none
      | _ => none
    p := fun a => match a with
      | .n x => (Double.ofDec x).bind fun d => if d ∈ ls then some (.num d) else none
      | _ => none }

/-! ### The gated ground codecs are refinements

`literal` and `numeric` are not new constructions: they are `string` and `number` with a
prism laid over them, which is exactly what §7 means by "an iso and a prism". Naming the
predicates makes that visible, and lets all six of their laws come from `Lawful.restrict`
and `carrier_restrict` instead of six bespoke inductions.

`decimal` is deliberately *not* here. It moves the member (`str` values to an `N`
attribute), so it is not a refinement of `string` and keeps its own proofs. -/

/-- `literal(ℓ)`'s predicate on the string side. -/
def inLS (ls : List String) : Value → Bool
  | .str s => decide (s ∈ ls)
  | _ => false

/-- `literal(ℓ)`'s predicate on the numeric side. -/
def inLN (ls : List Double) : Value → Bool
  | .num d => decide (d ∈ ls)
  | _ => false

/-- `numeric(q)`'s predicate, lifted from doubles to values. -/
def onNum (q : Double → Bool) : Value → Bool
  | .num d => q d
  | _ => false


/-! ## Wrappers -/

/-- `held`: an iso on the value side; the stored side is untouched. -/
def Codec.through (c : Codec) (f g : Value → Value) : Codec :=
  { T := fun v => c.T (f v)
    μ := c.μ
    e := fun v => c.e (f v)
    p := fun a => (c.p a).map g }

/-- `refine`: the prism. -/
def Codec.restrict (c : Codec) (q : Value → Bool) : Codec :=
  { T := fun v => c.T v ∧ q v
    μ := c.μ
    e := fun v => if q v then c.e v else none
    p := fun a => (c.p a).bind fun v => if q v then some v else none }

/-- `legacy`: extend the reading. With §3's coherence premise this presentation equals
    the order-free `p ∪ r`. -/
def Codec.extendRead (c : Codec) (r : Attr → Option Value) : Codec :=
  { T := c.T
    μ := c.μ
    e := c.e
    p := fun a => match c.p a with | some v => some v | none => r a }

/-- `nullable`. -/
def Codec.orNull (c : Codec) : Codec :=
  { T := fun v => c.T v ∨ v = .null
    μ := none
    e := fun v => match v with | .null => some .null | _ => c.e v
    p := fun a => match a with | .null => some .null | _ => c.p a }

/-! ### What the wrappers write and read

Each wrapper is one line of definition and touches exactly one half of the pair; stating
that as an `iff` is what keeps the proofs below — and §6's wrapper rows — from unfolding
the definitions again. `held` and `legacy` are transparent on the side they do not
touch, which is why two of the eight are `Iff.rfl`. -/

section WrapperInversion
variable {c : Codec}

/-- `held` writes what its base writes, at the transported value. -/
theorem through_e {f g : Value → Value} {v a} :
    (c.through f g).e v = some a ↔ c.e (f v) = some a := Iff.rfl

/-- …and reads what its base reads, transported back. -/
theorem through_p {f g : Value → Value} {a v} :
    (c.through f g).p a = some v ↔ ∃ w, c.p a = some w ∧ v = g w := by
  simp [Codec.through, Option.map_eq_some', eq_comm (a := v)]

/-- `refine` writes only what passes the prism… -/
theorem restrict_e {q : Value → Bool} {v a} :
    (c.restrict q).e v = some a ↔ q v = true ∧ c.e v = some a := by
  simp only [Codec.restrict]; split <;> simp_all

/-- …and reads only into it. -/
theorem restrict_p {q : Value → Bool} {a v} :
    (c.restrict q).p a = some v ↔ c.p a = some v ∧ q v = true := by
  simp only [Codec.restrict, Option.bind_eq_some]
  constructor
  · rintro ⟨w, hw, h⟩; split at h <;> simp_all
  · rintro ⟨h, hq⟩; exact ⟨v, h, by simp [hq]⟩

/-- `legacy` does not touch the writing at all — §5's whole point. -/
theorem extendRead_e {r : Attr → Option Value} {v a} :
    (c.extendRead r).e v = some a ↔ c.e v = some a := Iff.rfl

/-- It reads through the base where the base reads, and through the migration exactly
    where the base does not. That "exactly" is where (MP) goes. -/
theorem extendRead_p {r : Attr → Option Value} {a v} :
    (c.extendRead r).p a = some v ↔ c.p a = some v ∨ (c.p a = none ∧ r a = some v) := by
  show (match c.p a with | some w => some w | none => r a) = some v ↔ _
  cases hp : c.p a <;> simp

/-- `nullable` adds the `null` point and passes everything else through. -/
theorem orNull_e {v a} :
    c.orNull.e v = some a ↔ (v = .null ∧ a = .null) ∨ (v ≠ .null ∧ c.e v = some a) := by
  cases v <;> simp [Codec.orNull, eq_comm (a := a)]

theorem orNull_p {a v} :
    c.orNull.p a = some v ↔ (a = .null ∧ v = .null) ∨ (a ≠ .null ∧ c.p a = some v) := by
  cases a <;> simp [Codec.orNull, eq_comm (a := v)]

end WrapperInversion

/-! ## The traversal toolkit

One proof shape, proved once: a list traversed by an entrywise partial function, with
the laws lifting pointwise. `drop`'s skipping is not a traversal mode: it filters by
name first, then traverses — so every product consumes these same lemmas.

The whole toolkit rests on one observation, `traverse_eq_some`: **a successful traversal
*is* the pointwise relation**, `List.Forall₂ (f · = some ·)`. Every law below is then that
relation being pushed around — reversed for (R), forgotten for (C), composed for (MP) —
and mathlib's `Forall₂` API does the pushing. What used to be four twenty-line case
analyses on `Option` are four appeals to the pivot. -/


section Traverse
variable {α β γ : Type} {f : α → Option β} {g : β → Option α}


end Traverse


/-- A dead pair — nothing readable, nothing writable — is lawful whatever its `μ`. -/
theorem lawful_dead {m? : Option Member} :
    Lawful { T := fun _ => False, μ := m?, e := fun _ => none, p := fun _ => none } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ h; exact nomatch h
  · intro _ _ h; exact nomatch h
  · intro _ _ _ _ h; exact nomatch h
  · intro _ _ _ h _; exact nomatch h


/-- Lawfulness sees only the pair and the member, so it transfers to any codec agreeing on
    those three. This is how a ground codec inherits from the wrapper it turns out to be,
    without disturbing its definition — which matters, since the definitions are unfolded
    all over the development. -/
theorem Lawful.congr {c d : Codec} (he : c.e = d.e) (hp : c.p = d.p) (hμ : c.μ = d.μ)
    (h : Lawful d) : Lawful c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a hx; rw [he] at hx; rw [hp]; exact h.retract hx
  · intro a t hx; rw [hp] at hx; rw [he]; exact h.canon hx
  · intro μ hm t a hx; rw [hμ] at hm; rw [he] at hx; exact h.writes hm hx
  · intro a t a' h1 h2; rw [hp] at h1; rw [he] at h2; exact h.agree h1 h2

/-- The carrier transfers too, given the held set is no smaller. -/
theorem Carrier.congr {c d : Codec} (he : c.e = d.e) (hp : c.p = d.p)
    (hT : ∀ v, d.T v → c.T v) (h : Carrier d) : Carrier c := by
  refine ⟨?_, ?_⟩
  · intro v a hx; rw [he] at hx; exact hT v (h.domE hx)
  · intro a v hx; rw [hp] at hx; exact hT v (h.ranP hx)

/-- Forgetting the member index preserves the laws — `(lazy)` concludes `⊤`. -/
theorem Lawful.μNone {c : Codec} (h : Lawful c) : Lawful { c with μ := none } := by
  refine ⟨h.retract, h.canon, ?_, h.agree⟩
  intro _ h'
  exact nomatch h'

theorem LawfulCore.μNone {c : Codec} (h : LawfulCore c) :
    LawfulCore { c with μ := none } := by
  refine ⟨h.retract, h.canon, ?_⟩
  intro _ h'
  exact nomatch h'

/-! ## Filter facts (the sum proofs consume these) -/


/-! ## Products -/

/-! ### The wire-set payload projections

Each is `traverse` of one of the attribute prisms' inverses, and each of its two lemmas is
an instance of one general fact. -/

/-- A traversal through a prism recovers its input exactly. -/
theorem traverse_ctor_eq {α : Type} (c : Ctor α Attr) :
    ∀ {as : List Attr} {xs}, traverse c.out as = some xs → as = xs.map c.into
  | [], xs, h => by
      replace h : some [] = some xs := h
      cases h; rfl
  | a :: as, xs, h => by
      simp only [traverse] at h
      cases hu : c.out a with
      | none => rw [hu] at h; exact nomatch h
      | some x =>
        rw [hu] at h
        cases ht : traverse c.out as with
        | none => rw [ht] at h; exact nomatch h
        | some xs' =>
          rw [ht] at h
          replace h : some (x :: xs') = some xs := h
          cases h
          simp only [List.map]
          rw [← c.into_out hu, ← traverse_ctor_eq c ht]

/-- And it succeeds exactly when every element matches. -/
theorem traverse_ctor_isSome {α : Type} (c : Ctor α Attr) :
    ∀ {as : List Attr}, (∀ a ∈ as, (c.out a).isSome) → ∃ xs, traverse c.out as = some xs
  | [], _ => ⟨[], rfl⟩
  | a :: as, h => by
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h a (List.mem_cons_self a as))
      obtain ⟨xs, hxs⟩ := traverse_ctor_isSome c fun y hy => h y (List.mem_cons_of_mem _ hy)
      exact ⟨x :: xs, by simp only [traverse, hx, hxs]⟩

def strPayloads (as : List Attr) : Option (List String) := traverse sC.out as

def numPayloads (as : List Attr) : Option (List Numeral) := traverse nC.out as

def binPayloads (as : List Attr) : Option (List Bytes) := traverse bC.out as

/-- Encode a list of element attributes as the wire set their member selects. -/
def asWireSet (as : List Attr) : Option Attr :=
  if as.isEmpty then none
  else match strPayloads as with
    | some ss => some (Attr.ss ss)
    | none => match numPayloads as with
      | some ns => some (Attr.ns ns)
      | none => (binPayloads as).map Attr.bs

/-- The member a set stores, computed from its element's (§3 `(set)`). -/
def setMember : Member → Option Member
  | .S => some .SS
  | .N => some .NS
  | .B => some .BS
  | _ => none

def setCodec (c : Codec) : Codec :=
  { T := fun v => match v with | .set vs => vs ≠ [] ∧ ∀ x ∈ vs, c.T x | _ => False
    μ := c.μ.bind setMember
    e := fun v => match v with
      | .set vs => (traverse c.e vs).bind asWireSet
      | _ => none
    p := fun a => match a with
      | .ss vs =>
        if vs.isEmpty then none
        else (traverse (fun s => c.p (.s s)) vs).map Value.set
      | .ns vs =>
        if vs.isEmpty then none
        else (traverse (fun x => c.p (.n x)) vs).map Value.set
      | .bs vs =>
        if vs.isEmpty then none
        else (traverse (fun b => c.p (.b b)) vs).map Value.set
      | _ => none }

/-! ### A codec carried between two prisms

The shape underneath every product in §3–§4. A pair works on *payloads* — lists of
entries, mostly — and two prisms say which value and which attribute constructor hold
them. §2's four laws split cleanly along that seam: the prism halves are discharged once,
here, and each construction is left with only its payload pair's own round trip,
definedness and agreement.

`pointCodec` above is the degenerate case, where the payload passes through untouched.
The three below are the products: `entrywise` (a traversal, hence `array` and `record`),
`tuple` (`align`, then a traversal) and `object` (a guard, a filter, then a traversal).

`set` is the one product that is *not* an instance, and for a reason worth stating: its
attribute side is a choice among three wire sets, not one constructor. It is argued on
its own below. -/

/-- **A codec between two prisms.** `P` is the held set's condition on the payload;
    `E`/`D` are the payload pair. -/
def carriedCodec {γ δ : Type} (V : Ctor γ Value) (A : Ctor δ Attr) (μ₀ : Member)
    (P : γ → Prop) (E : γ → Option δ) (D : δ → Option γ) : Codec :=
  { T := fun v => ∃ x, v = V.into x ∧ P x
    μ := some μ₀
    e := fun v => ((V.out v).bind E).map A.into
    p := fun a => ((A.out a).bind D).map V.into }

section Carried
variable {γ δ : Type} {V : Ctor γ Value} {A : Ctor δ Attr} {μ₀ : Member}
  {P : γ → Prop} {E : γ → Option δ} {D : δ → Option γ}

/-- What it writes: only a value the prism matches, and only what `E` accepts. -/
theorem carried_e {v a} :
    (carriedCodec V A μ₀ P E D).e v = some a ↔
      ∃ x y, V.out v = some x ∧ E x = some y ∧ a = A.into y := by
  simp [carriedCodec, Option.bind_eq_some, Option.map_eq_some', eq_comm (a := a)]

/-- What it reads: the mirror. -/
theorem carried_p {a v} :
    (carriedCodec V A μ₀ P E D).p a = some v ↔
      ∃ y x, A.out a = some y ∧ D y = some x ∧ v = V.into x := by
  simp [carriedCodec, Option.bind_eq_some, Option.map_eq_some', eq_comm (a := v)]

/-- (R), (C) and (W) are the payload pair's own, plus the member the attribute
    constructor stamps. The prisms contribute nothing but their two laws. -/
theorem lawfulCore_carried (hμ : ∀ y, (A.into y).member = μ₀)
    (hr : ∀ x y, E x = some y → D y = some x)
    (hc : ∀ y x, D y = some x → (E x).isSome) :
    LawfulCore (carriedCodec V A μ₀ P E D) where
  retract he := by
    obtain ⟨x, y, hv, hx, rfl⟩ := carried_e.mp he
    exact carried_p.mpr ⟨y, x, A.out_into y, hr x y hx, V.into_out hv⟩
  canon hp := by
    obtain ⟨y, x, _, hy, rfl⟩ := carried_p.mp hp
    obtain ⟨y', h'⟩ := Option.isSome_iff_exists.mp (hc y x hy)
    exact Option.isSome_iff_exists.mpr ⟨_, carried_e.mpr ⟨x, y', V.out_into x, h', rfl⟩⟩
  writes := by
    intro μ hμ' t a he
    obtain ⟨_, y, _, _, rfl⟩ := carried_e.mp he
    exact (hμ y).trans (Option.some.inj hμ')

/-- (MP) is the payload pair's own too, stated where it has to be — at the attribute
    constructor, since that is where `≼` is defined. -/
theorem lawful_carried (hμ : ∀ y, (A.into y).member = μ₀)
    (hr : ∀ x y, E x = some y → D y = some x)
    (hc : ∀ y x, D y = some x → (E x).isSome)
    (hag : ∀ y x y', D y = some x → E x = some y' → Agree (A.into y') (A.into y)) :
    Lawful (carriedCodec V A μ₀ P E D) :=
  { lawfulCore_carried hμ hr hc with
    agree := by
      intro a t a' hp he
      obtain ⟨y, x, ha, hy, rfl⟩ := carried_p.mp hp
      obtain ⟨x', y', hv, hx, rfl⟩ := carried_e.mp he
      obtain rfl : x' = x := Option.some.inj ((V.out_into x).symm.trans hv).symm
      exact A.into_out ha ▸ hag _ _ _ hy hx }

/-- `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T`: the held set's condition has to hold of whatever
    payload either half of the pair accepts. -/
theorem carrier_carried
    (hdom : ∀ {x y}, E x = some y → P x)
    (hran : ∀ {y x}, D y = some x → P x) :
    Carrier (carriedCodec V A μ₀ P E D) where
  domE he := by
    obtain ⟨x, y, hv, hx, _⟩ := carried_e.mp he
    exact ⟨x, V.into_out hv, hdom hx⟩
  ranP hp := by
    obtain ⟨y, x, _, hy, rfl⟩ := carried_p.mp hp
    exact ⟨x, rfl, hran hy⟩

end Carried

/-! ### The entrywise product, named once

`array` and `record` are `carriedCodec` where the payload pair is one entry function
traversed: a value constructor holding a list of entries, an attribute constructor
holding a list of wire entries. Named once, §2's laws are discharged once — and each
instance is left with only the part that is genuinely its own, the shape of `≼` at its
attribute constructor (`Agree.l` compares by position, `Agree.m` by name). -/

/-- **The entrywise product**: `carriedCodec` at a traversal. -/
def entrywise {α β : Type} (V : Ctor (List α) Value) (A : Ctor (List β) Attr)
    (μ₀ : Member) (P : List α → Prop) (f : α → Option β) (g : β → Option α) : Codec :=
  carriedCodec V A μ₀ P (traverse f) (traverse g)

section Entrywise
variable {α β : Type} {V : Ctor (List α) Value} {A : Ctor (List β) Attr}
  {μ₀ : Member} {P : List α → Prop} {f : α → Option β} {g : β → Option α}

theorem entrywise_e {v a} :
    (entrywise V A μ₀ P f g).e v = some a ↔
      ∃ xs ys, V.out v = some xs ∧ traverse f xs = some ys ∧ a = A.into ys := carried_e

theorem entrywise_p {a v} :
    (entrywise V A μ₀ P f g).p a = some v ↔
      ∃ ys xs, A.out a = some ys ∧ traverse g ys = some xs ∧ v = V.into xs := carried_p

/-- The traversal toolkit is exactly what the payload pair's three clauses ask for:
    the round trip reversed, definedness forgotten. -/
theorem lawfulCore_entrywise (hμ : ∀ ys, (A.into ys).member = μ₀)
    (hr : ∀ x y, f x = some y → g y = some x)
    (hc : ∀ y x, g y = some x → (f x).isSome) :
    LawfulCore (entrywise V A μ₀ P f g) :=
  lawfulCore_carried hμ (traverse_roundTrip hr) (traverse_isSome hc)

/-- (MP) is the one clause `array` and `record` do not share: `R` is the entry-level
    agreement the pair delivers, and `hA` is how the attribute constructor turns a
    pointwise `R` into `≼`. -/
theorem lawful_entrywise {R : β → β → Prop} (hμ : ∀ ys, (A.into ys).member = μ₀)
    (hr : ∀ x y, f x = some y → g y = some x)
    (hc : ∀ y x, g y = some x → (f x).isSome)
    (hag : ∀ y x y', g y = some x → f x = some y' → R y' y)
    (hA : ∀ {ys ys' : List β}, ys'.length = ys.length →
            (∀ q ∈ ys'.zip ys, R q.1 q.2) → Agree (A.into ys') (A.into ys)) :
    Lawful (entrywise V A μ₀ P f g) :=
  lawful_carried hμ (traverse_roundTrip hr) (traverse_isSome hc)
    fun _ _ _ hy hx => hA ((traverse_length _ _ hy).trans (traverse_length _ _ hx)).symm
      (traverse_rel hag _ _ _ hy hx)

theorem carrier_entrywise
    (hdom : ∀ {xs ys}, traverse f xs = some ys → P xs)
    (hran : ∀ {ys xs}, traverse g ys = some xs → P xs) :
    Carrier (entrywise V A μ₀ P f g) :=
  carrier_carried hdom hran

end Entrywise

/-! ### `array` (§3) — entrywise between `arr` and `L` -/

/-! ### What `set` writes and reads

    The attribute side of `set` is a choice among three wire constructors rather than
    one prism, which is why it is not an `entrywise` product and why its read-side
    inversion names all three families. -/

/-- What `set` writes: a `set` value whose elements all write, gathered by `asWireSet`. -/
theorem setCodec_e_eq {c : Codec} {v : Value} {a : Attr} :
    (setCodec c).e v = some a ↔
      ∃ vs as, v = .set vs ∧ traverse c.e vs = some as ∧ asWireSet as = some a := by
  cases v <;> simp [setCodec, Option.bind_eq_some]

/-- What `set` reads: a nonempty wire set of one of the three families, its payloads
    each read through the matching element prism. The read-side mirror of
    `setCodec_e_eq`, and the reason the three families have to be spelled out — the
    attribute side of `set` is a choice among three constructors, not one prism. -/
theorem setCodec_p_eq {c : Codec} {a : Attr} {v : Value} :
    (setCodec c).p a = some v ↔
      ∃ vs : List Value, v = .set vs ∧
        ((∃ ss : List String, a = .ss ss ∧ ss ≠ [] ∧
            traverse (fun s => c.p (.s s)) ss = some vs)
         ∨ (∃ ns : List Numeral, a = .ns ns ∧ ns ≠ [] ∧
            traverse (fun x => c.p (.n x)) ns = some vs)
         ∨ (∃ bs : List Bytes, a = .bs bs ∧ bs ≠ [] ∧
            traverse (fun b => c.p (.b b)) bs = some vs)) := by
  cases a <;>
    simp [setCodec, Option.map_eq_some', eq_comm (a := v), List.isEmpty_iff] <;>
    tauto

def arrayCodec (c : Codec) : Codec :=
  { T := fun v => match v with | .arr vs => ∀ x ∈ vs, c.T x | _ => False
    μ := some .L
    e := fun v => match v with
      | .arr vs => (traverse c.e vs).map Attr.l
      | _ => none
    p := fun a => match a with
      | .l as => (traverse c.p as).map Value.arr
      | _ => none }

/-- `array` *is* the entrywise product at `arr`/`L`, on the nose. The definition above is
    left in its unfolded form because the `opaque` fixpoint reduces through it; this
    equation is what carries the three lemmas across. -/
theorem arrayCodec_eq {c : Codec} :
    arrayCodec c = entrywise arrV lA .L (fun vs => ∀ x ∈ vs, c.T x) c.e c.p := by
  ext v <;> cases v <;> simp_all [arrayCodec, entrywise, carriedCodec, arrV, lA, Ctor.into, Ctor.out]

/-- (R), (C), (W) — `L` is the member every `arr` writes. -/
theorem lawfulCore_arrayCodec {c : Codec} (h : LawfulCore c) :
    LawfulCore (arrayCodec c) :=
  arrayCodec_eq ▸ lawfulCore_entrywise (fun _ => rfl) (fun _ _ => h.retract)
    (fun _ _ => h.canon)

/-- `≼` at `L` is positional: `Agree.l` reads the zip the traversal already provides. -/
theorem lawful_arrayCodec {c : Codec} (h : Lawful c) : Lawful (arrayCodec c) :=
  arrayCodec_eq ▸ lawful_entrywise (R := Agree) (fun _ => rfl) (fun _ _ => h.retract)
    (fun _ _ => h.canon) (fun _ _ _ => h.agree) (fun _ hz => .l _ _ hz)

theorem carrier_arrayCodec {c : Codec} (hc : Carrier c) : Carrier (arrayCodec c) :=
  arrayCodec_eq ▸ carrier_entrywise
    (fun h => traverse_mem_input (fun _ _ => hc.domE) h)
    (fun h => traverse_mem (fun _ _ => hc.ranP) h)

/-! ### `record` (§3) — entrywise between `map` and `M` -/

/-- The keyed entry steps: `record` is their uniform instance, `object` their
    name-dispatched one. -/
def encPair (c : Codec) : Name × Value → Option (Name × Attr) :=
  fun kv => (c.e kv.2).map ((kv.1, ·))

def decPair (c : Codec) : Name × Attr → Option (Name × Value) :=
  fun kv => (c.p kv.2).map ((kv.1, ·))

/-- The entry steps invert each other, keep the name, and agree — §2's four laws one
    level down, which is all `entrywise` asks of them. -/
theorem encPair_decPair {c : Codec} (h : LawfulCore c) :
    ∀ kv ka, encPair c kv = some ka → decPair c ka = some kv := by
  rintro ⟨k, v⟩ ka hkv
  obtain ⟨a, he, rfl⟩ := Option.map_eq_some'.mp hkv
  exact Option.map_eq_some'.mpr ⟨v, h.retract he, rfl⟩

theorem decPair_encPair {c : Codec} (h : LawfulCore c) :
    ∀ ka kv, decPair c ka = some kv → (encPair c kv).isSome := by
  rintro ⟨k, a⟩ kv hka
  obtain ⟨v, hp, rfl⟩ := Option.map_eq_some'.mp hka
  simpa [encPair] using h.canon hp

theorem encPair_agree {c : Codec} (h : Lawful c) :
    ∀ ka kv ka', decPair c ka = some kv → encPair c kv = some ka' →
      ka'.1 = ka.1 ∧ Agree ka'.2 ka.2 := by
  rintro ⟨k, a⟩ kv ka' hka hkv
  obtain ⟨v, hp, rfl⟩ := Option.map_eq_some'.mp hka
  obtain ⟨a', he, rfl⟩ := Option.map_eq_some'.mp hkv
  exact ⟨rfl, h.agree hp he⟩

theorem encPair_dom {c : Codec} (hc : Carrier c) :
    ∀ kv ka, encPair c kv = some ka → c.T kv.2 := by
  rintro ⟨k, v⟩ ka hkv
  obtain ⟨a, he, _⟩ := Option.map_eq_some'.mp hkv
  exact hc.domE he

theorem decPair_ran {c : Codec} (hc : Carrier c) :
    ∀ ka kv, decPair c ka = some kv → c.T kv.2 := by
  rintro ⟨k, a⟩ kv hka
  obtain ⟨v, hp, rfl⟩ := Option.map_eq_some'.mp hka
  exact hc.ranP hp

def recordCodec (c : Codec) : Codec :=
  { T := fun v => match v with | .map kvs => ∀ kv ∈ kvs, c.T kv.2 | _ => False
    μ := some .M
    e := fun v => match v with
      | .map kvs => (traverse (encPair c) kvs).map Attr.m
      | _ => none
    p := fun a => match a with
      | .m kvs => (traverse (decPair c) kvs).map Value.map
      | _ => none }

/-- `record` is the same product at `map`/`M`, with the entry pair carrying the name. -/
theorem recordCodec_eq {c : Codec} :
    recordCodec c = entrywise mapV mA .M (fun kvs => ∀ kv ∈ kvs, c.T kv.2)
      (encPair c) (decPair c) := by
  ext v <;> cases v <;> simp_all [recordCodec, entrywise, carriedCodec, mapV, mA, Ctor.into, Ctor.out]

/-- (R), (C), (W) — `M` is the member every `map` writes. -/
theorem lawfulCore_recordCodec {c : Codec} (h : LawfulCore c) :
    LawfulCore (recordCodec c) :=
  recordCodec_eq ▸ lawfulCore_entrywise (fun _ => rfl) (encPair_decPair h)
    (decPair_encPair h)

/-- `≼` at `M` is by name, not by position — the entries agree pointwise *and* keep their
    names, and `lookup_rel` turns that into `Agree.m`. -/
theorem lawful_recordCodec {c : Codec} (h : Lawful c) : Lawful (recordCodec c) :=
  recordCodec_eq ▸ lawful_entrywise (fun _ => rfl) (encPair_decPair h.core)
    (decPair_encPair h.core) (encPair_agree h)
    (fun hlen hz => .m _ _ (lookup_rel _ _ hlen hz))

theorem carrier_recordCodec {c : Codec} (hc : Carrier c) : Carrier (recordCodec c) :=
  recordCodec_eq ▸ carrier_entrywise
    (fun h => traverse_mem_input (encPair_dom hc) h)
    (fun h => traverse_mem (decPair_ran hc) h)

/-! ### `tuple` (§3) — the positional product

`tuple` is `carriedCodec` between the same two prisms as `array`, with a payload pair
that pairs each position with its own codec before traversing. Everything specific to it
is therefore a fact about that pairing, and there is only one worth stating: **which
codec a position gets depends on the position alone, never on what stands there.** Name
the codec row a shape assigns to a row of `n` positions (`slots`) and the pairing is a
`zip` with it (`align_eq_some`) — after which a row and its image under the pair, having
the same length, provably align against the *same* codecs. That is the whole of the
tuple's asymmetry between reading and writing, and the four clauses of §2 then run
position by position over the codec row, exactly as they do for `array`. -/

/-- Pair each position with its codec: the fixed head positionally, the tail
    uniformly; length mismatches refuse. `tuple` is then `align` + `traverse`. -/
def align {α : Type} : List Codec → Option Codec → List α → Option (List (Codec × α))
  | [], _, [] => some []
  | [], tail, x :: xs =>
    match tail with
    | some c => (align [] tail xs).map ((c, x) :: ·)
    | none => none
  | _ :: _, _, [] => none
  | c :: cs, tail, x :: xs => (align cs tail xs).map ((c, x) :: ·)

def tupleCodec (cs : List Codec) (tail : Option Codec) : Codec :=
  { T := fun v => match v with
      | .arr vs => ∃ ps, align cs tail vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2
      | _ => False
    μ := some .L
    e := fun v => match v with
      | .arr vs => ((align cs tail vs).bind
          (traverse fun cv => cv.1.e cv.2)).map Attr.l
      | _ => none
    p := fun a => match a with
      | .l as => ((align cs tail as).bind
          (traverse fun ca => ca.1.p ca.2)).map Value.arr
      | _ => none }

/-! #### The codec row a shape assigns -/

/-- The codec row for a row of `n` positions: the fixed head, then the tail codec as
    often as needed. `none` is the length mismatch `align` refuses on. -/
def slots : List Codec → Option Codec → Nat → Option (List Codec)
  | [], _, 0 => some []
  | [], none, _ + 1 => none
  | [], some c, n + 1 => (slots [] (some c) n).map (c :: ·)
  | _ :: _, _, 0 => none
  | c :: cs, tail, n + 1 => (slots cs tail n).map (c :: ·)

theorem align_eq_zip {α : Type} : ∀ (cs : List Codec) (tail : Option Codec) (xs : List α),
    align cs tail xs = (slots cs tail xs.length).map (·.zip xs)
  | [], tail, [] => by cases tail <;> rfl
  | [], none, _ :: _ => rfl
  | [], some c, x :: xs => by
      show (align [] (some c) xs).map ((c, x) :: ·) = _
      rw [align_eq_zip [] (some c) xs]
      cases hs : slots [] (some c) xs.length <;> simp [slots, hs, List.zip]
  | _ :: _, tail, [] => by cases tail <;> rfl
  | c :: cs, tail, x :: xs => by
      show (align cs tail xs).map ((c, x) :: ·) = _
      rw [align_eq_zip cs tail xs]
      cases hs : slots cs tail xs.length <;> simp [slots, hs, List.zip]

theorem slots_length : ∀ (cs : List Codec) (tail : Option Codec) (n : Nat) (ds),
    slots cs tail n = some ds → ds.length = n
  | [], tail, 0, _, h => by cases tail <;> (simp [slots] at h; simp [← h])
  | [], some c, n + 1, ds, h => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some'.mp h
      simp [slots_length [] (some c) n ds' h']
  | c :: cs, tail, n + 1, ds, h => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some'.mp h
      simp [slots_length cs tail n ds' h']

/-- Every codec in the row is one the shape declared. -/
theorem slots_mem : ∀ (cs : List Codec) (tail : Option Codec) (n : Nat) (ds),
    slots cs tail n = some ds → ∀ c ∈ ds, c ∈ cs ∨ tail = some c
  | [], tail, 0, _, h, _, hm => by
      cases tail <;> (simp [slots] at h; subst h; exact nomatch hm)
  | [], some c, n + 1, ds, h, d, hm => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some'.mp h
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact .inr rfl
      · exact slots_mem [] (some c) n ds' h' d hm'
  | c :: cs, tail, n + 1, ds, h, d, hm => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some'.mp h
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact .inl (List.mem_cons_self _ _)
      · exact (slots_mem cs tail n ds' h' d hm').imp (List.mem_cons_of_mem _) id

/-- A property of the shape's codecs is a property of every codec in every row. -/
theorem slots_all {Q : Codec → Prop} {cs : List Codec} {tail : Option Codec}
    (hcs : ∀ c ∈ cs, Q c) (htl : ∀ c ∈ tail, Q c) {n ds}
    (hs : slots cs tail n = some ds) : ∀ c ∈ ds, Q c := fun c hc =>
  (slots_mem cs tail n ds hs c hc).elim (hcs c) (htl c)

/-- **The pivot for `align`.** An alignment is the codec row zipped with the row: which
    codec a position gets depends on the position alone, never on what stands there. -/
theorem align_eq_some {α : Type} {cs : List Codec} {tail : Option Codec}
    {xs : List α} {ps} :
    align cs tail xs = some ps ↔
      ∃ ds, slots cs tail xs.length = some ds ∧ ds.length = xs.length ∧ ps = ds.zip xs := by
  rw [align_eq_zip]
  constructor
  · intro h
    obtain ⟨ds, h', rfl⟩ := Option.map_eq_some'.mp h
    exact ⟨ds, h', slots_length _ _ _ _ h', rfl⟩
  · rintro ⟨ds, h', _, rfl⟩
    rw [h']; rfl

/-- …so any row of the same length aligns against the same codecs. -/
theorem align_of_slots {α : Type} {cs : List Codec} {tail : Option Codec} {n ds}
    (h : slots cs tail n = some ds) {xs : List α} (hn : xs.length = n) :
    align cs tail xs = some (ds.zip xs) := by
  rw [align_eq_zip, hn, h]; rfl

/-! #### §2's clauses, position by position over the codec row -/

theorem zip_roundTrip : ∀ (ds : List Codec) (vs : List Value) (as : List Attr),
    (∀ c ∈ ds, LawfulCore c) → ds.length = vs.length →
    traverse (fun cv : Codec × Value => cv.1.e cv.2) (ds.zip vs) = some as →
    traverse (fun ca : Codec × Attr => ca.1.p ca.2) (ds.zip as) = some vs
  | [], vs, as, _, hlen, h => by simp_all [List.eq_nil_of_length_eq_zero hlen.symm]
  | _ :: _, [], as, _, hlen, h => by simp_all
  | d :: ds, v :: vs, as, hd, hlen, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨a, ha, has⟩ := Option.bind_eq_some.mp h
      obtain ⟨as', has', rfl⟩ := Option.map_eq_some'.mp has
      rw [List.zip_cons_cons, traverse_cons, (hd d (by simp)).retract ha,
        zip_roundTrip ds vs as' (fun c hc => hd c (by simp [hc])) (by simpa using hlen) has']
      rfl

theorem zip_canon : ∀ (ds : List Codec) (as : List Attr) (vs : List Value),
    (∀ c ∈ ds, LawfulCore c) →
    traverse (fun ca : Codec × Attr => ca.1.p ca.2) (ds.zip as) = some vs →
    (traverse (fun cv : Codec × Value => cv.1.e cv.2) (ds.zip vs)).isSome
  | [], as, vs, _, h => by simp_all
  | _ :: _, [], vs, _, h => by simp_all
  | d :: ds, a :: as, vs, hd, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨v, hv, hvs⟩ := Option.bind_eq_some.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some'.mp hvs
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ((hd d (by simp)).canon hv)
      obtain ⟨as', has'⟩ := Option.isSome_iff_exists.mp
        (zip_canon ds as vs' (fun c hc => hd c (by simp [hc])) hvs')
      simp [List.zip_cons_cons, traverse_cons, ha', has']

theorem zip_agree : ∀ (ds : List Codec) (as : List Attr) (vs : List Value) (as' : List Attr),
    (∀ c ∈ ds, Lawful c) →
    traverse (fun ca : Codec × Attr => ca.1.p ca.2) (ds.zip as) = some vs →
    traverse (fun cv : Codec × Value => cv.1.e cv.2) (ds.zip vs) = some as' →
    ∀ q ∈ as'.zip as, Agree q.1 q.2
  | [], as, vs, as', _, h, h' => by simp_all
  | _ :: _, [], vs, as', _, h, h' => by simp_all
  | d :: ds, a :: as, vs, as', hd, h, h' => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨v, hv, hvs⟩ := Option.bind_eq_some.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some'.mp hvs
      rw [List.zip_cons_cons, traverse_cons] at h'
      obtain ⟨a₁, ha₁, has⟩ := Option.bind_eq_some.mp h'
      obtain ⟨as₁, has₁, rfl⟩ := Option.map_eq_some'.mp has
      intro q hq
      rcases List.mem_cons.mp (by simpa using hq) with rfl | hq'
      · exact (hd d (by simp)).agree hv ha₁
      · exact zip_agree ds as vs' as₁ (fun c hc => hd c (by simp [hc])) hvs' has₁ q hq'

/-- Writing a row puts every position on its own carrier… -/
theorem zip_domE : ∀ (ds : List Codec) (vs : List Value) (as : List Attr),
    (∀ c ∈ ds, Carrier c) →
    traverse (fun cv : Codec × Value => cv.1.e cv.2) (ds.zip vs) = some as →
    ∀ q ∈ ds.zip vs, q.1.T q.2
  | [], vs, as, _, h => by simp_all
  | _ :: _, [], as, _, h => by simp_all
  | d :: ds, v :: vs, as, hd, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨a, ha, has⟩ := Option.bind_eq_some.mp h
      obtain ⟨as', has', rfl⟩ := Option.map_eq_some'.mp has
      intro q hq
      rcases List.mem_cons.mp (by simpa using hq) with rfl | hq'
      · exact (hd d (by simp)).domE ha
      · exact zip_domE ds vs as' (fun c hc => hd c (by simp [hc])) has' q hq'

/-- …and so does reading one. -/
theorem zip_ranP : ∀ (ds : List Codec) (as : List Attr) (vs : List Value),
    (∀ c ∈ ds, Carrier c) →
    traverse (fun ca : Codec × Attr => ca.1.p ca.2) (ds.zip as) = some vs →
    ∀ q ∈ ds.zip vs, q.1.T q.2
  | [], as, vs, _, h => by simp_all
  | _ :: _, [], vs, _, h => by simp_all
  | d :: ds, a :: as, vs, hd, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨v, hv, hvs⟩ := Option.bind_eq_some.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some'.mp hvs
      intro q hq
      rcases List.mem_cons.mp (by simpa using hq) with rfl | hq'
      · exact (hd d (by simp)).ranP hv
      · exact zip_ranP ds as vs' (fun c hc => hd c (by simp [hc])) hvs' q hq'

/-! #### `tuple` is `carriedCodec` at that pair -/

section Tuple
variable {cs : List Codec} {tail : Option Codec}

theorem tupleCodec_eq :
    tupleCodec cs tail = carriedCodec arrV lA .L
      (fun vs => ∃ ps, align cs tail vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2)
      (fun vs => (align cs tail vs).bind (traverse fun cv => cv.1.e cv.2))
      (fun as => (align cs tail as).bind (traverse fun ca => ca.1.p ca.2)) := by
  refine Codec.ext ?_ rfl ?_ ?_ <;> funext v <;> cases v <;>
    simp [tupleCodec, carriedCodec, arrV, lA, Ctor.into, Ctor.out]

/-- (R) for the payload pair: realign the written row against the same codecs, then
    read back position by position. -/
theorem tuple_retract (hd : ∀ c ∈ cs, LawfulCore c) (htl : ∀ c ∈ tail, LawfulCore c) :
    ∀ vs as, (align cs tail vs).bind (traverse fun cv => cv.1.e cv.2) = some as →
      (align cs tail as).bind (traverse fun ca => ca.1.p ca.2) = some vs := by
  intro vs as hE
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some.mp hE
  obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
  have hn : as.length = vs.length := by
    rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
  exact Option.bind_eq_some.mpr ⟨_, align_of_slots hs hn,
    zip_roundTrip ds vs as (slots_all hd htl hs) hlen htr⟩

/-- (C) for the payload pair, the same way round. -/
theorem tuple_canon (hd : ∀ c ∈ cs, LawfulCore c) (htl : ∀ c ∈ tail, LawfulCore c) :
    ∀ as vs, (align cs tail as).bind (traverse fun ca => ca.1.p ca.2) = some vs →
      ((align cs tail vs).bind (traverse fun cv => cv.1.e cv.2)).isSome := by
  intro as vs hD
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some.mp hD
  obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
  have hn : vs.length = as.length := by
    rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
  rw [align_of_slots hs hn]
  exact zip_canon ds as vs (slots_all hd htl hs) htr

theorem lawfulCore_tupleCodec (hcs : ∀ c ∈ cs, LawfulCore c)
    (htl : ∀ c ∈ tail, LawfulCore c) : LawfulCore (tupleCodec cs tail) :=
  tupleCodec_eq ▸ lawfulCore_carried (fun _ => rfl) (tuple_retract hcs htl)
    (tuple_canon hcs htl)

/-- `≼` at `L` is positional, and so is the alignment — which is why the re-encoded row
    lands on the same codecs and agrees with the stored one entry for entry. -/
theorem lawful_tupleCodec (hcs : ∀ c ∈ cs, Lawful c) (htl : ∀ c ∈ tail, Lawful c) :
    Lawful (tupleCodec cs tail) := by
  refine tupleCodec_eq ▸ lawful_carried (fun _ => rfl)
    (tuple_retract (fun c h => (hcs c h).core) (fun c h => (htl c h).core))
    (tuple_canon (fun c h => (hcs c h).core) (fun c h => (htl c h).core)) ?_
  intro as vs as' hD hE
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some.mp hD
  obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
  have hn : vs.length = as.length := by
    rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
  obtain ⟨ps', hal', htr'⟩ := Option.bind_eq_some.mp hE
  rw [align_of_slots hs hn] at hal'
  cases hal'
  exact .l as' as (zip_agree ds as vs as' (slots_all hcs htl hs) htr htr')

theorem carrier_tupleCodec (hcs : ∀ c ∈ cs, Carrier c) (htl : ∀ c ∈ tail, Carrier c) :
    Carrier (tupleCodec cs tail) := by
  refine tupleCodec_eq ▸ carrier_carried ?_ ?_
  · intro vs as hE
    obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some.mp hE
    obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
    exact ⟨_, hal, zip_domE ds vs as (slots_all hcs htl hs) htr⟩
  · intro as vs hD
    obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some.mp hD
    obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
    have hn : vs.length = as.length := by
      rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
    exact ⟨_, align_of_slots hs hn, zip_ranP ds as vs (slots_all hcs htl hs) htr⟩

end Tuple

/-! ## Objects (§4) -/

/-- A field, denoted: presence marker plus the attribute pair. -/
inductive FieldSem where
  | req (c : Codec)
  | opt (c : Codec)
  | fb  (c : Codec) (v : Value)

def FieldSem.codec : FieldSem → Codec
  | .req c => c
  | .opt c => c
  | .fb c _ => c

/-- A rest policy, denoted. -/
inductive RestSem where
  | drop | refuse
  | codec (c : Codec)

/-- One value entry, dispatched by name: declared through its field, undeclared through
    the rest codec — or refused, since the doc's `e` is domained on the closed record
    type `T` for `drop` and `refuse` alike (they differ in `dom(p)`, §4). -/
def encEntry (spec : Name → Option FieldSem) (restE : Option (Value → Option Attr)) :
    Name × Value → Option (Name × Attr) := fun kv =>
  match spec kv.1 with
  | some fs => (fs.codec.e kv.2).map ((kv.1, ·))
  | none =>
    match restE with
    | some f => (f kv.2).map ((kv.1, ·))
    | none => none

/-- One stored entry, dispatched by name. Undeclared names reach this only under
    `refuse` (fail) or a rest codec — `drop` filtered them out already. -/
def decEntry (spec : Name → Option FieldSem) (restP : Option (Attr → Option Value)) :
    Name × Attr → Option (Name × Value) := fun kv =>
  match spec kv.1 with
  | some fs => (fs.codec.p kv.2).map ((kv.1, ·))
  | none =>
    match restP with
    | some f => (f kv.2).map ((kv.1, ·))
    | none => none

/-- `fb`'s absent case, `p♭(ε) = v(∗)`: the stand-ins for the fallback names a row
    omits. Empty on canonical items, where every `fb` name is present. -/
def fbDefaults (names : List Name) : List (Name × FieldSem) → List (Name × Value)
  | [] => []
  | (k, .fb _ v) :: sems =>
    if names.contains k then fbDefaults names sems
    else (k, v) :: fbDefaults names sems
  | _ :: sems => fbDefaults names sems

/-- Every non-`opt` binding present — the value-side guard (§4: `fallback` concludes
    `req`). -/
def valPresentB (sems : List (Name × FieldSem)) (names : List Name) : Bool :=
  sems.all fun kf =>
    match kf.2 with
    | .opt _ => true
    | _ => names.contains kf.1

/-- Every `req` name present — the stored-side guard; `fb` reads to its stand-in. -/
def reqPresentB (sems : List (Name × FieldSem)) (names : List Name) : Bool :=
  sems.all fun kf =>
    match kf.2 with
    | .req _ => names.contains kf.1
    | _ => true

/-- The rest policy's codec, where it has one. -/
def rcOf : RestSem → Option Codec
  | .codec c => some c
  | _ => none

/-- The name filter: `drop` keeps declared names only; the others keep everything.
    A filter, never a traversal mode (§4). -/
def keepB (rest : RestSem) (sems : List (Name × FieldSem)) : Name → Bool :=
  match rest with
  | .drop => fun k => (sems.lookup k).isSome
  | _ => fun _ => true

def objectCodecCore (sems : List (Name × FieldSem)) (rc? : Option Codec)
    (kn : Name → Bool) : Codec :=
  { T := fun v => match v with
      | .map kvs =>
        valPresentB sems (kvs.map (·.1)) = true ∧
        ∀ kv ∈ kvs, match sems.lookup kv.1 with
          | some fs => fs.codec.T kv.2
          | none => ∃ rc, rc? = some rc ∧ rc.T kv.2
      | _ => False
    μ := some .M
    e := fun v => match v with
      | .map kvs =>
        if valPresentB sems (kvs.map (·.1)) = true then
          (traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e))) kvs).map Attr.m
        else none
      | _ => none
    p := fun a => match a with
      | .m kvs =>
        if reqPresentB sems (kvs.map (·.1)) = true then
          (traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
            (kvs.filter fun kv => kn kv.1)).map fun ds =>
              Value.map (ds ++ fbDefaults (kvs.map (·.1)) sems)
        else none
      | _ => none }

def objectCodec (sems : List (Name × FieldSem)) (rest : RestSem) : Codec :=
  objectCodecCore sems (rcOf rest) (keepB rest sems)

/-! ### The object, taken apart

Three namings, and everything §4 asks becomes short. **`entryCodec`** is the codec one
entry goes through — the field its name declares, or else the rest policy's — which is
the only thing `encEntry`/`decEntry` do with a name, so every per-entry law is one appeal
to `entryCodec_of`. **`objWrite`/`objRead`** are the payload pair: the guard and the
steps going out, the guard, the `drop` filter, the steps and the fallback stand-ins
coming back. **`objectCodecCore_eq`** then makes the object `carriedCodec` between `map`
and `M`, so §2's prism halves are the ones already discharged. -/

/-- The per-name half of §4's held set: a declared name holds its field's set, an
    undeclared one falls to the open part `R(ρ)`. -/
def objEntryT (sems : List (Name × FieldSem)) (rc? : Option Codec) :
    Name × Value → Prop := fun kv =>
  match sems.lookup kv.1 with
  | some fs => fs.codec.T kv.2
  | none => ∃ rc, rc? = some rc ∧ rc.T kv.2

/-- The codec one entry goes through: the field its name declares, or else the rest
    policy's. `none` is an undeclared name under `refuse`. -/
def entryCodec (sems : List (Name × FieldSem)) (rc? : Option Codec) (k : Name) :
    Option Codec :=
  match sems.lookup k with
  | some fs => some fs.codec
  | none => rc?

section Object
variable {sems : List (Name × FieldSem)} {rc? : Option Codec} {kn : Name → Bool}

/-- A property of every field and of the rest codec is a property of every entry's
    codec — which is how the object's per-entry laws are discharged, once each. -/
theorem entryCodec_of {Q : Codec → Prop} (hf : ∀ kf ∈ sems, Q kf.2.codec)
    (hrc : ∀ c ∈ rc?, Q c) {k c} (h : entryCodec sems rc? k = some c) : Q c := by
  simp only [entryCodec] at h
  cases hsp : sems.lookup k with
  | some fs => rw [hsp] at h; cases h; exact hf _ (mem_of_lookup hsp)
  | none => rw [hsp] at h; exact hrc c h

theorem encEntry_eq {kv ka} :
    encEntry (fun k => sems.lookup k) (rc?.map (·.e)) kv = some ka ↔
      ∃ c a, entryCodec sems rc? kv.1 = some c ∧ c.e kv.2 = some a ∧ ka = (kv.1, a) := by
  simp only [encEntry, entryCodec]
  cases sems.lookup kv.1 <;> cases rc? <;> simp [Option.map_eq_some', eq_comm (a := ka)]

theorem decEntry_eq {ka kv} :
    decEntry (fun k => sems.lookup k) (rc?.map (·.p)) ka = some kv ↔
      ∃ c v, entryCodec sems rc? ka.1 = some c ∧ c.p ka.2 = some v ∧ kv = (ka.1, v) := by
  simp only [decEntry, entryCodec]
  cases sems.lookup ka.1 <;> cases rc? <;> simp [Option.map_eq_some', eq_comm (a := kv)]

/-- §4's held set, per entry, in the same vocabulary. -/
theorem objEntryT_eq {kv} :
    objEntryT sems rc? kv ↔ ∃ c, entryCodec sems rc? kv.1 = some c ∧ c.T kv.2 := by
  simp only [objEntryT, entryCodec]
  cases sems.lookup kv.1 <;> simp

/-- The object's payload pair, going out: the value-side presence guard, then the
    name-dispatched steps. -/
def objWrite (sems : List (Name × FieldSem)) (rc? : Option Codec) :
    List (Name × Value) → Option (List (Name × Attr)) := fun kvs =>
  if valPresentB sems (kvs.map (·.1)) = true then
    traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e))) kvs
  else none

/-- …and coming back: the stored-side guard, the `drop` filter, the steps, and the
    stand-ins for the fallback names the row omits. -/
def objRead (sems : List (Name × FieldSem)) (rc? : Option Codec) (kn : Name → Bool) :
    List (Name × Attr) → Option (List (Name × Value)) := fun kas =>
  if reqPresentB sems (kas.map (·.1)) = true then
    (traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
      (kas.filter fun ka => kn ka.1)).map (· ++ fbDefaults (kas.map (·.1)) sems)
  else none

theorem objWrite_eq {kvs kas} :
    objWrite sems rc? kvs = some kas ↔
      valPresentB sems (kvs.map (·.1)) = true ∧
        traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e))) kvs = some kas := by
  simp only [objWrite]; split <;> simp_all

theorem objRead_eq {kas kvs} :
    objRead sems rc? kn kas = some kvs ↔
      ∃ ds, reqPresentB sems (kas.map (·.1)) = true ∧
        traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
          (kas.filter fun ka => kn ka.1) = some ds ∧
        kvs = ds ++ fbDefaults (kas.map (·.1)) sems := by
  simp only [objRead]; split <;> simp_all [Option.map_eq_some', eq_comm (a := kvs)]

/-- The object is `carriedCodec` between `map` and `M`, at that pair. -/
theorem objectCodecCore_eq :
    objectCodecCore sems rc? kn =
      carriedCodec mapV mA .M
        (fun kvs => valPresentB sems (kvs.map (·.1)) = true ∧
          ∀ kv ∈ kvs, objEntryT sems rc? kv)
        (objWrite sems rc?) (objRead sems rc? kn) := by
  refine Codec.ext ?_ rfl ?_ ?_ <;> funext v <;> cases v <;>
    simp only [objectCodecCore, carriedCodec, objWrite, objRead, objEntryT, mapV, mA,
      Ctor.into, Ctor.out, Option.bind_some, Option.bind_none, Option.map_none'] <;>
    first
      | rfl
      | (split_ifs with hg <;> simp [hg, Option.map_map, Function.comp_def])
      | simp

/-- Inversion of an object-encode success: the value is a map, the guard held, and the
    written item is the entrywise traversal. -/
theorem objectCodecCore_e_inv {t a} (he : (objectCodecCore sems rc? kn).e t = some a) :
    ∃ kvs ds, t = Value.map kvs ∧ a = Attr.m ds ∧
      valPresentB sems (kvs.map (·.1)) = true ∧
      traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e))) kvs = some ds := by
  obtain ⟨kvs, kas, hv, hw, rfl⟩ := carried_e.mp (objectCodecCore_eq ▸ he)
  obtain ⟨hval, htr⟩ := objWrite_eq.mp hw
  exact ⟨kvs, kas, mapV.into_out hv, rfl, hval, htr⟩

end Object

/-! ## Sums (§5): admission as data -/

/-- One union option: its admission functions and its pair. The doc's `κ`/`ident`/name
    devices become *builders* of these. -/
structure OptionSem where
  admitA : Attr → Bool
  admitV : Value → Bool
  c : Codec

/-- Name admission (objects): every present name declared, every required name present. -/
def keysOk {α : Type} (spec : List (Name × Bool)) (kvs : List (Name × α)) : Bool :=
  kvs.all (fun kv => spec.any (·.1 == kv.1)) &&
  spec.all (fun kb => !kb.2 || (kvs.lookup kb.1).isSome)

/-- An object option decides by names, never by being attempted. -/
def OptionSem.byNames (spec : List (Name × Bool)) (c : Codec) : OptionSem :=
  { admitA := fun a => match a with | .m kvs => keysOk spec kvs | _ => false
    admitV := fun v => match v with | .map kvs => keysOk spec kvs | _ => false
    c := c }

/-- Any other option is admitted by attempt — the doc's `ident` caveat lives in the
    (U) premise, not here. -/
def OptionSem.byAttempt (c : Codec) : OptionSem :=
  { admitA := fun a => (c.p a).isSome
    admitV := fun v => (c.e v).isSome
    c := c }

/-- The `⟨NULL⟩` point as a union option — §3's second half of `nullable(c)` read as
    `union(c, ⟨NULL⟩-point)`. It decides by attempting, like any ground option. -/
abbrev nullOption : OptionSem := .byAttempt nullCodec

/-- A `(dunion)` option is admitted by its discriminator tag. -/
def OptionSem.byTag (d : Name) (tags : List String) (c : Codec) : OptionSem :=
  { admitA := fun a =>
      match a with
      | .m kvs =>
        match kvs.lookup d with
        | some (.s tag) => tags.contains tag
        | _ => false
      | _ => false
    admitV := fun v =>
      match v with
      | .map kvs =>
        match kvs.lookup d with
        | some (.str tag) => tags.contains tag
        | _ => false
      | _ => false
    c := c }

/-- The builder `denote` uses for a union option. -/
def optionSemOf (c : Codec) : Option (List (Name × Bool)) → OptionSem
  | some spec => .byNames spec c
  | none => .byAttempt c

/-- §5 (U): every canonical pair of an option is admitted by that option alone, on
    both sides. The residue of the soundness theorem, as a premise. -/
def UniqueAdmission (os : List OptionSem) : Prop :=
  ∀ o ∈ os, ∀ t a, o.c.e t = some a →
    os.filter (·.admitA a) = [o] ∧ os.filter (·.admitV t) = [o]

/-- A union's member: `μ` when unanimous, else `⊤` (§5 `(union)`). -/
def unanimous : List (Option Member) → Option Member
  | [] => none
  | μ :: μs => if μs.all (· == μ) then μ else none

/-- `union`: the sum, resolved by unique admission — never by declaration order. -/
def altCodec (os : List OptionSem) (μA : Option Member) : Codec :=
  { T := fun v => ∃ o ∈ os, o.c.T v
    μ := μA
    e := fun v => match os.filter (·.admitV v) with
      | [o] => o.c.e v
      | _ => none
    p := fun a => match os.filter (·.admitA a) with
      | [o] => o.c.p a
      | _ => none }

/-- `discriminatedUnion` is not its own codec: it is the sum over tag-admission
    options. Its (U) is `uniqueAdmission_byTag` — a theorem, which is what the term
    is for. -/
def dunionCodec (d : Name) (os : List (List String × Codec)) : Codec :=
  altCodec (os.map fun o => .byTag d o.1 o.2) (some .M)

/-! ## Unknown values (§3 `(opaque)`) -/

/-- `opaque` is not special: it is the recursive union of everything self-identifying,
    closed under the containers — "the values whose type is recoverable", as a
    fixpoint of the algebra. Its (U) is kind-disjointness
    (`uniqueAdmission_of_disjoint`), and the `Numbers` policy gets its cleanest
    statement: **`refuse` is the absence of an option.** -/
def opaqCodec : Nat → Bool → Codec
  | 0, _ => .empty
  | fuel+1, lossy =>
    altCodec
      [.byAttempt stringCodec, .byAttempt booleanCodec, .byAttempt binaryCodec,
       .byAttempt nullCodec,
       -- `refuse` is the absence of the number option — here, the empty option.
       .byAttempt (if lossy then numberCodec else Codec.empty),
       .byAttempt (setCodec (opaqCodec fuel lossy)),
       .byAttempt (arrayCodec (opaqCodec fuel lossy)),
       .byAttempt (recordCodec (opaqCodec fuel lossy))]
      none

/-! ## Carriers — the pair is on `T` (§3 `e : T ⇀ 𝔸`, `p : 𝔸 ⇀ T`)

    One `Carrier` lemma per combinator, mirroring the lawfulness lemmas below. Together
    with `typed_TSub` (Soundness.lean) these make the judgement's held-set index a
    checked claim: what a derivable term writes and reads lies in the `T` it names. -/


/-- The carrier, likewise: `e` only writes what `V` matched, `p` only reads what `V`
    built. -/
theorem carrier_pointCodec {α : Type} {V : Ctor α Value} {A : Ctor α Attr} {μ₀ : Member} :
    Carrier (pointCodec V A μ₀) := by
  refine ⟨?_, ?_⟩
  · intro v a h
    obtain ⟨x, hx, _⟩ := Option.map_eq_some'.mp h
    exact ⟨x, V.into_out hx⟩
  · intro a v h
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some'.mp h
    exact ⟨x, rfl⟩

/-- The four point ground codecs are on their carriers for one reason, the same one that
    made them lawful: `e` only writes what the value prism matched, and `p` only reads what
    it built. See `carrier_pointCodec`. -/
theorem carrier_stringCodec : Carrier stringCodec :=
  Carrier.congr (d := pointCodec strV sC .S)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl)
    (fun _ h => h) carrier_pointCodec

theorem carrier_decimalCodec : Carrier decimalCodec := by
  refine ⟨?_, ?_⟩
  · intro v a h
    cases v with
    | str s =>
      replace h : (if Numeral.WF s = true then some (Attr.n s) else none) = some a := h
      by_cases hw : Numeral.WF s = true
      · exact ⟨s, rfl, hw⟩
      · rw [if_neg hw] at h; exact nomatch h
    | _ => exact nomatch h
  · intro a v h
    cases a with
    | n x =>
      replace h : (if Numeral.WF x = true then some (Value.str x) else none) = some v := h
      by_cases hw : Numeral.WF x = true
      · rw [if_pos hw] at h; cases h; exact ⟨x, rfl, hw⟩
      · rw [if_neg hw] at h; exact nomatch h
    | _ => exact nomatch h

theorem carrier_booleanCodec : Carrier booleanCodec :=
  Carrier.congr (d := pointCodec boolV boolA .BOOL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl)
    (fun _ h => h) carrier_pointCodec

theorem carrier_binaryCodec : Carrier binaryCodec :=
  Carrier.congr (d := pointCodec binV bC .B)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl)
    (fun _ h => h) carrier_pointCodec

theorem carrier_nullCodec : Carrier nullCodec :=
  Carrier.congr (d := pointCodec nullV nullA .NULL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl)
    (fun _ h => h.elim fun _ hh => hh) carrier_pointCodec

theorem carrier_numberCodec : Carrier numberCodec := by
  refine ⟨?_, ?_⟩
  · intro v a h; cases v <;> first | exact ⟨_, rfl⟩ | exact nomatch h
  · intro a v h
    cases a
    case n x =>
      replace h : ((Double.ofDec x).map Value.num) = some v := h
      cases hd : Double.ofDec x with
      | none => rw [hd] at h; exact nomatch h
      | some d => rw [hd] at h; replace h : some (Value.num d) = some v := h
                  cases h; exact ⟨_, rfl⟩
    all_goals exact nomatch h

/-! ### Sums -/

/-! ### How a union resolves

`altCodec`'s two halves are the same shape: filter the options by admission, and answer
if and only if exactly one survives. Stated as an `iff`, that is the whole of the union
— every theorem about `union` below, and every row of §6 that mentions one, is a
statement about `os.filter` and nothing else. -/

/-- **What a union writes**: exactly one option admitted the value, and it wrote. -/
theorem altCodec_e {os : List OptionSem} {μA : Option Member} {v a} :
    (altCodec os μA).e v = some a ↔
      ∃ o, os.filter (·.admitV v) = [o] ∧ o.c.e v = some a := by
  show (match os.filter (·.admitV v) with | [o] => o.c.e v | _ => none) = some a ↔ _
  cases hf : os.filter (·.admitV v) with
  | nil => simp
  | cons o tl => cases tl <;> simp

/-- **What a union reads**: the mirror, on the attribute side. -/
theorem altCodec_p {os : List OptionSem} {μA : Option Member} {a v} :
    (altCodec os μA).p a = some v ↔
      ∃ o, os.filter (·.admitA a) = [o] ∧ o.c.p a = some v := by
  show (match os.filter (·.admitA a) with | [o] => o.c.p a | _ => none) = some v ↔ _
  cases hf : os.filter (·.admitA a) with
  | nil => simp
  | cons o tl => cases tl <;> simp

/-- A sum's encode routes through an admitting option — the weaker form, which forgets
    that the option was the *only* one. Enough where the uniqueness is not needed. -/
theorem altCodec_e_admits {os : List OptionSem} {μA : Option Member} {v a}
    (he : (altCodec os μA).e v = some a) :
    ∃ o ∈ os, o.admitV v = true ∧ o.c.e v = some a := by
  obtain ⟨o, hf, hoe⟩ := altCodec_e.mp he
  obtain ⟨ho, hadm⟩ := mem_of_filter_eq_singleton hf
  exact ⟨o, ho, hadm, hoe⟩

/-- A sum's decode routes through an admitting option — the mirror of
    `altCodec_e_admits`. -/
theorem altCodec_p_admits {os : List OptionSem} {μA : Option Member} {a v}
    (hp : (altCodec os μA).p a = some v) :
    ∃ o ∈ os, o.admitA a = true ∧ o.c.p a = some v := by
  obtain ⟨o, hf, hop⟩ := altCodec_p.mp hp
  obtain ⟨ho, hadm⟩ := mem_of_filter_eq_singleton hf
  exact ⟨o, ho, hadm, hop⟩

/-! ### Wrappers -/

theorem carrier_through {c : Codec} {f g : Value → Value} (hc : Carrier c)
    (hlaw : LawfulCore c) (hfg : ∀ v, (c.e v).isSome → f (g v) = v) :
    Carrier (c.through f g) where
  domE he := hc.domE (through_e.mp he)
  ranP hp := by
    obtain ⟨w, hw, rfl⟩ := through_p.mp hp
    show c.T (f (g w))
    rw [hfg w (hlaw.canon hw)]
    exact hc.ranP hw

theorem carrier_restrict {c : Codec} (hc : Carrier c) (q : Value → Bool) :
    Carrier (c.restrict q) where
  domE he := let ⟨hq, hcv⟩ := restrict_e.mp he; ⟨hc.domE hcv, hq⟩
  ranP hp := let ⟨hcv, hq⟩ := restrict_p.mp hp; ⟨hc.ranP hcv, hq⟩


/-! ### The refinement ground codecs, on their carriers -/

theorem carrier_literalSCodec (ls : List String) : Carrier (literalSCodec ls) :=
  Carrier.congr (by funext v; cases v <;> simp [literalSCodec, Codec.restrict, stringCodec, inLS])
    (by funext a; cases a <;> simp [literalSCodec, Codec.restrict, stringCodec, inLS])
    (by rintro v ⟨⟨s, rfl⟩, hq⟩; exact ⟨s, by simpa [inLS] using hq, rfl⟩)
    (carrier_restrict carrier_stringCodec (inLS ls))

theorem carrier_numericCodec (q : Double → Bool) : Carrier (numericCodec q) := by
  refine Carrier.congr ?_ ?_ ?_ (carrier_restrict carrier_numberCodec (onNum q))
  · funext v; cases v <;> simp [numericCodec, Codec.restrict, numberCodec, onNum]
  · funext a
    cases a
    case n x =>
      cases hd : Double.ofDec x <;>
        simp [numericCodec, Codec.restrict, numberCodec, onNum, hd]
    all_goals simp [numericCodec, Codec.restrict, numberCodec]
  · rintro v ⟨⟨d, rfl⟩, hq⟩; exact ⟨d, by simpa [onNum] using hq, rfl⟩

theorem carrier_literalNCodec (ls : List Double) : Carrier (literalNCodec ls) := by
  refine Carrier.congr ?_ ?_ ?_ (carrier_restrict carrier_numberCodec (inLN ls))
  · funext v; cases v <;> simp [literalNCodec, Codec.restrict, numberCodec, inLN]
  · funext a
    cases a
    case n x =>
      cases hd : Double.ofDec x <;>
        simp [literalNCodec, Codec.restrict, numberCodec, inLN, hd]
    all_goals simp [literalNCodec, Codec.restrict, numberCodec]
  · rintro v ⟨⟨d, rfl⟩, hq⟩; exact ⟨d, by simpa [inLN] using hq, rfl⟩

/-- `legacy`: the migration lands in `T` because §3's `ran(r) ⊆ dom(e)` puts it in
    `dom(e)`, and `e`'s domain is `T`. The doc writes `r : 𝔸 ⇀ T` directly; this is the
    same premise arrived at through the one the proof already needs. -/
theorem carrier_extendRead {c : Codec} {r : Attr → Option Value} (hc : Carrier c)
    (hran : ∀ a v, r a = some v → (c.e v).isSome) :
    Carrier (c.extendRead r) where
  domE he := hc.domE (extendRead_e.mp he)
  ranP hp := by
    rcases extendRead_p.mp hp with hcv | ⟨-, hrv⟩
    · exact hc.ranP hcv
    · obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hran _ _ hrv)
      exact hc.domE ha'

theorem carrier_orNull {c : Codec} (hc : Carrier c) : Carrier c.orNull where
  domE he := by
    rcases orNull_e.mp he with ⟨hv, -⟩ | ⟨-, hcv⟩
    · exact .inr hv
    · exact .inl (hc.domE hcv)
  ranP hp := by
    rcases orNull_p.mp hp with ⟨-, hv⟩ | ⟨-, hcv⟩
    · exact .inr hv
    · exact .inl (hc.ranP hcv)

/-! ### Containers -/


/-- `set`: nonemptiness comes from the wire, on both sides — `asWireSet` refuses the
    empty list going out, and `p` refuses an empty wire set coming in. §3's `℘⁺fin`.
    The three read-side families differ only in which prism the payloads sit in, so the
    argument is the traversal fact applied three times to the same shape. -/
theorem carrier_setCodec {c : Codec} (hc : Carrier c) : Carrier (setCodec c) where
  domE he := by
    obtain ⟨vs, as, rfl, htr, hw⟩ := setCodec_e_eq.mp he
    refine ⟨?_, traverse_mem_input (fun _ _ hxy => hc.domE hxy) htr⟩
    rintro rfl
    cases (by simpa using htr : as = [])
    exact nomatch hw
  ranP hp := by
    obtain ⟨vs, rfl, hcase⟩ := setCodec_p_eq.mp hp
    have nonempty : ∀ {β : Type} (ws : List β) (f : β → Option Value),
        ws ≠ [] → traverse f ws = some vs → vs ≠ [] := by
      rintro β ws f hws htr rfl
      exact hws (List.eq_nil_of_length_eq_zero (traverse_length ws [] htr))
    rcases hcase with ⟨ss, -, hne, htr⟩ | ⟨ns, -, hne, htr⟩ | ⟨bs, -, hne, htr⟩ <;>
      exact ⟨nonempty _ _ hne htr, traverse_mem (fun _ _ hxy => hc.ranP hxy) htr⟩


/-! ### Sums -/

theorem carrier_dead {m? : Option Member} :
    Carrier { T := fun _ => False, μ := m?, e := fun _ => none, p := fun _ => none } := by
  refine ⟨?_, ?_⟩ <;> intro _ _ h <;> exact nomatch h

theorem carrier_altCodec {os : List OptionSem} {μA : Option Member}
    (h : ∀ o ∈ os, Carrier o.c) : Carrier (altCodec os μA) := by
  refine ⟨?_, ?_⟩
  · intro v a he
    obtain ⟨o, ho, -, hoe⟩ := altCodec_e_admits he
    exact ⟨o, ho, (h o ho).domE hoe⟩
  · intro a v hp
    obtain ⟨o, ho, -, hop⟩ := altCodec_p_admits hp
    exact ⟨o, ho, (h o ho).ranP hop⟩


/-- `opaque`'s fixpoint is on its carrier at every fuel — §3's `Uν`, one option per
    kind, `refuse` being the absence of the `number` option. -/
theorem carrier_opaqCodec : ∀ (fuel : Nat) (lossy : Bool), Carrier (opaqCodec fuel lossy)
  | 0, _ => Carrier.empty
  | fuel+1, lossy => by
    have ih := carrier_opaqCodec fuel lossy
    refine carrier_altCodec ?_
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact carrier_stringCodec
    · exact carrier_booleanCodec
    · exact carrier_binaryCodec
    · exact carrier_nullCodec
    · cases lossy with
      | false => exact Carrier.empty
      | true => exact carrier_numberCodec
    · exact carrier_setCodec ih
    · exact carrier_arrayCodec ih
    · exact carrier_recordCodec ih

/-! ## Lawfulness — proved -/

/-! ### The point ground codecs, argued once

`string`, `boolean`, `binary` and `null` are `pointCodec` at four different pairs of
prisms. Below, each of the four is that one lemma transported across the definitional
equality by `Lawful.congr`, which is what lets the definitions stay in the unfolded form
the rest of the development `simp`s with. -/

/-- §2's four laws for any pair of prisms. The two premises are the only things a prism
    pair does not already supply: which member the attribute side stamps, and that `≼` is
    reflexive on its image. Everything else is `out_into` and `into_out`. -/
theorem lawful_pointCodec {α : Type} {V : Ctor α Value} {A : Ctor α Attr} {μ₀ : Member}
    (hμ : ∀ x, (A.into x).member = μ₀) (hrefl : ∀ x, Agree (A.into x) (A.into x)) :
    Lawful (pointCodec V A μ₀) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (R): match, rebuild, match again — `out_into` on each side.
    intro t a he
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some'.mp he
    simp [pointCodec, A.out_into, ← V.into_out hx]
  · -- (C): what `p` produced was built by `V`, so `V.out` matches it.
    intro a t hp
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some'.mp hp
    simp [pointCodec, V.out_into]
  · -- (W): everything written is `A.into` of something.
    intro μ hm t a he
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some'.mp he
    cases hm; exact hμ x
  · -- (MP): the re-encoding is the attribute itself, not merely an agreeing one.
    intro a t a' hp he
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some'.mp hp
    simp only [pointCodec, V.out_into, Option.map_some'] at he
    cases he
    rw [A.into_out hx]
    exact hrefl x

theorem lawful_stringCodec : Lawful stringCodec :=
  Lawful.congr (d := pointCodec strV sC .S)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl) (fun _ => .s ..))

theorem lawful_booleanCodec : Lawful booleanCodec :=
  Lawful.congr (d := pointCodec boolV boolA .BOOL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl) (fun _ => .bool ..))

theorem lawful_binaryCodec : Lawful binaryCodec :=
  Lawful.congr (d := pointCodec binV bC .B)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl) (fun _ => .b ..))

theorem lawful_nullCodec : Lawful nullCodec :=
  Lawful.congr (d := pointCodec nullV nullA .NULL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl) (fun _ => .null))

/-- `e` and `p` gate on the *same* predicate applied to the *same* text, so each law
    reduces to that one decision. -/
theorem decimalCodec_e_str (s : String) :
    decimalCodec.e (.str s) = if Numeral.WF s then some (.n s) else none := rfl

theorem decimalCodec_p_n (x : Numeral) :
    decimalCodec.p (.n x) = if Numeral.WF x then some (.str x) else none := rfl

theorem lawful_decimalCodec : Lawful decimalCodec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t with
    | str s =>
      rw [decimalCodec_e_str] at he
      by_cases hw : Numeral.WF s = true
      · rw [if_pos hw] at he; cases he; rw [decimalCodec_p_n, if_pos hw]
      · rw [if_neg hw] at he; exact nomatch he
    | _ => exact nomatch he
  · intro a t hp
    cases a with
    | n x =>
      rw [decimalCodec_p_n] at hp
      by_cases hw : Numeral.WF x = true
      · rw [if_pos hw] at hp; cases hp; rw [decimalCodec_e_str, if_pos hw]; rfl
      · rw [if_neg hw] at hp; exact nomatch hp
    | _ => exact nomatch hp
  · intro μ hμ t a he
    cases t with
    | str s =>
      rw [decimalCodec_e_str] at he
      by_cases hw : Numeral.WF s = true
      · rw [if_pos hw] at he; cases he; cases hμ; rfl
      · rw [if_neg hw] at he; exact nomatch he
    | _ => exact nomatch he
  · intro a t a' hp he
    cases a with
    | n x =>
      rw [decimalCodec_p_n] at hp
      by_cases hw : Numeral.WF x = true
      · rw [if_pos hw] at hp
        cases hp
        rw [decimalCodec_e_str, if_pos hw] at he
        cases he
        exact .n ..
      · rw [if_neg hw] at hp; exact nomatch hp
    | _ => exact nomatch hp

/-- The `(number)` case — the one consuming the shortest-text axiom. -/
theorem lawful_numberCodec : Lawful numberCodec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t <;> simp_all [numberCodec]
    subst_vars
    simp [numberCodec, Double.roundtrip]
  · intro a t hp
    cases a <;> simp_all [numberCodec]
    rename_i x
    cases hx : Double.ofDec x <;> rw [hx] at hp <;> simp_all [numberCodec]
    subst_vars
    rfl
  · intro μ hμ t a he
    cases t <;> simp_all [numberCodec, Attr.member]
    subst_vars
    rfl
  · intro a t a' hp he
    cases a <;> simp_all [numberCodec]
    rename_i x
    cases hx : Double.ofDec x <;> rw [hx] at hp <;> simp_all [numberCodec]
    subst_vars
    try simp_all [numberCodec]
    subst_vars
    exact .n ..

theorem LawfulCore.through {c : Codec} (h : LawfulCore c) {f g : Value → Value}
    (hgf : ∀ v, (c.e (f v)).isSome → g (f v) = v)
    (hfg : ∀ v, (c.e v).isSome → f (g v) = v) :
    LawfulCore (c.through f g) where
  retract he := through_p.mpr ⟨_, h.retract (through_e.mp he),
    (hgf _ (by rw [through_e.mp he]; rfl)).symm⟩
  canon hp := by
    obtain ⟨w, hw, rfl⟩ := through_p.mp hp
    show (c.e (f (g w))).isSome
    rw [hfg w (h.canon hw)]
    exact h.canon hw
  writes := by intro μ hμ t a he; exact h.writes hμ (through_e.mp he)

/-- `held` preserves the full laws: the core lemma, plus `≼` through the iso. -/
theorem Lawful.through {c : Codec} (h : Lawful c) {f g : Value → Value}
    (hgf : ∀ v, (c.e (f v)).isSome → g (f v) = v)
    (hfg : ∀ v, (c.e v).isSome → f (g v) = v) :
    Lawful (c.through f g) :=
  { LawfulCore.through h.core hgf hfg with
    agree := by
      intro a t a' hp he
      obtain ⟨w, hw, rfl⟩ := through_p.mp hp
      rw [through_e, hfg w (h.canon hw)] at he
      exact h.agree hw he }

/-- `refine` preserves the laws: everything restricts. -/
theorem LawfulCore.restrict {c : Codec} (h : LawfulCore c) (q : Value → Bool) :
    LawfulCore (c.restrict q) where
  retract he :=
    let ⟨hq, hc⟩ := restrict_e.mp he
    restrict_p.mpr ⟨h.retract hc, hq⟩
  canon hp :=
    let ⟨hc, hq⟩ := restrict_p.mp hp
    Option.isSome_iff_exists.mpr
      (let ⟨a, ha⟩ := Option.isSome_iff_exists.mp (h.canon hc)
       ⟨a, restrict_e.mpr ⟨hq, ha⟩⟩)
  writes := by intro μ hμ t a he; exact h.writes hμ (restrict_e.mp he).2

theorem Lawful.restrict {c : Codec} (h : Lawful c) (q : Value → Bool) :
    Lawful (c.restrict q) :=
  { LawfulCore.restrict h.core q with
    agree := fun hp he => h.agree (restrict_p.mp hp).1 (restrict_e.mp he).2 }


/-! ### The refinement ground codecs are lawful because their bases are

`literal` and `numeric` add a prism and nothing else, so all four laws come from
`Lawful.restrict`. What used to be three inductions is now three statements of which
codec is being refined by which predicate. -/

theorem lawful_literalSCodec (ls : List String) : Lawful (literalSCodec ls) := by
  refine Lawful.congr ?_ ?_ ?_ (Lawful.restrict lawful_stringCodec (inLS ls))
  · funext v; cases v <;> simp [literalSCodec, Codec.restrict, stringCodec, inLS]
  · funext a; cases a <;> simp [literalSCodec, Codec.restrict, stringCodec, inLS]
  · rfl

theorem lawful_numericCodec (q : Double → Bool) : Lawful (numericCodec q) := by
  refine Lawful.congr ?_ ?_ ?_ (Lawful.restrict lawful_numberCodec (onNum q))
  · funext v; cases v <;> simp [numericCodec, Codec.restrict, numberCodec, onNum]
  · funext a
    cases a
    case n x =>
      cases hd : Double.ofDec x <;>
        simp [numericCodec, Codec.restrict, numberCodec, onNum, hd]
    all_goals simp [numericCodec, Codec.restrict, numberCodec]
  · rfl

theorem lawful_literalNCodec (ls : List Double) : Lawful (literalNCodec ls) := by
  refine Lawful.congr ?_ ?_ ?_ (Lawful.restrict lawful_numberCodec (inLN ls))
  · funext v; cases v <;> simp [literalNCodec, Codec.restrict, numberCodec, inLN]
  · funext a
    cases a
    case n x =>
      cases hd : Double.ofDec x <;>
        simp [literalNCodec, Codec.restrict, numberCodec, inLN, hd]
    all_goals simp [literalNCodec, Codec.restrict, numberCodec]
  · rfl

theorem LawfulCore.extendRead {c : Codec} (h : LawfulCore c) {r : Attr → Option Value}
    (hran : ∀ a v, r a = some v → (c.e v).isSome) :
    LawfulCore (c.extendRead r) where
  retract he := extendRead_p.mpr (.inl (h.retract (extendRead_e.mp he)))
  canon hp := (extendRead_p.mp hp).elim h.canon fun ⟨_, hr⟩ => hran _ _ hr
  writes := by intro μ hμ t a he; exact h.writes hμ (extendRead_e.mp he)

/-- `nullable` keeps the core laws under null-honesty. Structurally this is the sum
    `alt [c, null-point]`; the honesty premises are its (U), specialised — and they are
    used in exactly one place each, to rule out the wrapper's own point colliding with
    the base's. -/
theorem LawfulCore.orNull {c : Codec} (h : LawfulCore c)
    (hw : ∀ v a, c.e v = some a → a = .null → v = .null)
    (hr : ∀ a v, c.p a = some v → v = .null → a = .null) :
    LawfulCore c.orNull where
  retract he := by
    rcases orNull_e.mp he with ⟨rfl, rfl⟩ | ⟨hv, hc⟩
    · exact orNull_p.mpr (.inl ⟨rfl, rfl⟩)
    · exact orNull_p.mpr (.inr ⟨fun hn => hv (hw _ _ hc hn), h.retract hc⟩)
  canon hp := by
    rcases orNull_p.mp hp with ⟨rfl, rfl⟩ | ⟨ha, hc⟩
    · exact Option.isSome_iff_exists.mpr ⟨.null, orNull_e.mpr (.inl ⟨rfl, rfl⟩)⟩
    · obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (h.canon hc)
      exact Option.isSome_iff_exists.mpr
        ⟨a', orNull_e.mpr (.inr ⟨fun hn => ha (hr _ _ hc hn), ha'⟩)⟩
  writes := by intro μ hμ; exact nomatch hμ

/-- `nullable` preserves the full laws: the core lemma, plus `≼` — read-honesty is
    what keeps a non-`NULL` attribute from re-encoding as `⟨NULL, ∗⟩`. -/
theorem Lawful.orNull {c : Codec} (h : Lawful c)
    (hw : ∀ v a, c.e v = some a → a = .null → v = .null)
    (hr : ∀ a v, c.p a = some v → v = .null → a = .null) :
    Lawful c.orNull :=
  { LawfulCore.orNull h.core hw hr with
    agree := by
      intro a t a' hp he
      rcases orNull_p.mp hp with ⟨rfl, rfl⟩ | ⟨ha, hc⟩
      · rcases orNull_e.mp he with ⟨-, rfl⟩ | ⟨hv, -⟩
        · exact .null
        · exact absurd rfl hv
      · rcases orNull_e.mp he with ⟨rfl, -⟩ | ⟨-, hc'⟩
        · exact absurd (hr _ _ hc rfl) ha
        · exact h.agree hc hc' }

/-! ## Lawfulness — the open frontier (README roadmap) -/

/-! ### Payload facts for the quotiented product -/


theorem strPayloads_eq {as : List Attr} {ss} (h : strPayloads as = some ss) :
    as = ss.map Attr.s := traverse_ctor_eq sC h

theorem numPayloads_eq {as : List Attr} {ns} (h : numPayloads as = some ns) :
    as = ns.map Attr.n := traverse_ctor_eq nC h

theorem binPayloads_eq {as : List Attr} {bs} (h : binPayloads as = some bs) :
    as = bs.map Attr.b := traverse_ctor_eq bC h

theorem strPayloads_isSome {as : List Attr} (h : ∀ x ∈ as, x.member = .S) :
    ∃ ss, strPayloads as = some ss :=
  traverse_ctor_isSome sC fun a ha => by
    have hm := h a ha
    cases a
    case s v => rfl
    all_goals exact nomatch hm

theorem numPayloads_isSome {as : List Attr} (h : ∀ x ∈ as, x.member = .N) :
    ∃ ns, numPayloads as = some ns :=
  traverse_ctor_isSome nC fun a ha => by
    have hm := h a ha
    cases a
    case n v => rfl
    all_goals exact nomatch hm

theorem binPayloads_isSome {as : List Attr} (h : ∀ x ∈ as, x.member = .B) :
    ∃ bs, binPayloads as = some bs :=
  traverse_ctor_isSome bC fun a ha => by
    have hm := h a ha
    cases a
    case b v => rfl
    all_goals exact nomatch hm

/-- What a written wire set can be: one member family, uniformly. -/
theorem asWireSet_cases {as : List Attr} {a} (h : asWireSet as = some a) :
    as ≠ [] ∧
    ((∃ ss, as = ss.map Attr.s ∧ a = .ss ss) ∨
     (∃ ns, as = ns.map Attr.n ∧ a = .ns ns) ∨
     (∃ bs, as = bs.map Attr.b ∧ a = .bs bs)) := by
  cases as with
  | nil => exact nomatch h
  | cons x rest =>
    refine ⟨by simp, ?_⟩
    replace h : (match strPayloads (x :: rest) with
      | some ss => some (Attr.ss ss)
      | none =>
        match numPayloads (x :: rest) with
        | some ns => some (Attr.ns ns)
        | none => (binPayloads (x :: rest)).map Attr.bs) = some a := h
    cases hs : strPayloads (x :: rest) with
    | some ss =>
      rw [hs] at h
      replace h : some (Attr.ss ss) = some a := h
      cases h
      exact Or.inl ⟨ss, strPayloads_eq hs, rfl⟩
    | none =>
      rw [hs] at h
      cases hn : numPayloads (x :: rest) with
      | some ns =>
        rw [hn] at h
        replace h : some (Attr.ns ns) = some a := h
        cases h
        exact Or.inr (Or.inl ⟨ns, numPayloads_eq hn, rfl⟩)
      | none =>
        rw [hn] at h
        replace h : (binPayloads (x :: rest)).map Attr.bs = some a := h
        cases hb : binPayloads (x :: rest) with
        | none => rw [hb] at h; exact nomatch h
        | some bs =>
          rw [hb] at h
          replace h : some (Attr.bs bs) = some a := h
          cases h
          exact Or.inr (Or.inr ⟨bs, binPayloads_eq hb, rfl⟩)

/-! ### `setCodec`'s three payload families, once

`lawful_setCodec` proved `canon` and `agree` three times over — once for `SS`, once for
`NS`, once for `BS` — with the branches textually identical apart from which prism the
payload sits in. What actually varies is two facts, and they are the only two the
argument consults: which member the element attributes name, and that `asWireSet` accepts
a nonempty run of them. Both are stated below, per family, and the argument itself is
stated once.

This is the payload triplication of the wire sets, the same shape `Ctor` already retired
for `strPayloads`/`numPayloads`/`binPayloads`. -/

/-- On the flat members — everything but `L` and `M` — `≼` is just equality of member.
    The wire sets are flat, which is why the agreement half never inspects payloads. -/
theorem agree_of_member_flat {x y : Attr} (hm : x.member = y.member)
    (hL : x.member ≠ .L) (hM : x.member ≠ .M) : Agree x y := by
  cases x <;> cases y <;>
    simp_all [Attr.member] <;> constructor

/-- A nonempty run of one member is a wire set of the matching wire member. One proof per
    family, and each is only about `asWireSet`'s dispatch order. -/
theorem asWireSet_of_S {as : List Attr} (hne : as ≠ [])
    (hm : ∀ y ∈ as, y.member = .S) :
    ∃ a', asWireSet as = some a' ∧ a'.member = .SS := by
  obtain ⟨ss, hss⟩ := strPayloads_isSome hm
  refine ⟨.ss ss, ?_, rfl⟩
  cases as with
  | nil => exact absurd rfl hne
  | cons x r => simp only [asWireSet]; rw [hss]; rfl

theorem asWireSet_of_N {as : List Attr} (hne : as ≠ [])
    (hm : ∀ y ∈ as, y.member = .N) :
    ∃ a', asWireSet as = some a' ∧ a'.member = .NS := by
  obtain ⟨ns, hns⟩ := numPayloads_isSome hm
  refine ⟨.ns ns, ?_, rfl⟩
  cases as with
  | nil => exact absurd rfl hne
  | cons x r =>
    have hs : strPayloads (x :: r) = none := by
      have hx := hm x (List.mem_cons_self _ _)
      cases x <;> simp_all [Attr.member, strPayloads, traverse, sC]
    simp only [asWireSet]; rw [hs, hns]; rfl

theorem asWireSet_of_B {as : List Attr} (hne : as ≠ [])
    (hm : ∀ y ∈ as, y.member = .B) :
    ∃ a', asWireSet as = some a' ∧ a'.member = .BS := by
  obtain ⟨bs, hbs⟩ := binPayloads_isSome hm
  refine ⟨.bs bs, ?_, rfl⟩
  cases as with
  | nil => exact absurd rfl hne
  | cons x r =>
    have hx := hm x (List.mem_cons_self _ _)
    have hs : strPayloads (x :: r) = none := by
      cases x <;> simp_all [Attr.member, strPayloads, traverse, sC]
    have hn : numPayloads (x :: r) = none := by
      cases x <;> simp_all [Attr.member, numPayloads, traverse, nC]
    simp only [asWireSet]; rw [hs, hn, hbs]; rfl

/-- The shared core of `setCodec`'s read-side laws: whatever a wire set decodes to,
    re-encoding it yields a nonempty run of that family's member. Both `canon` and `agree`
    consult exactly this and then differ only in what they do with it. -/
theorem setCodec_reencode_of {α : Type} {c : Codec} (h : Lawful c)
    (elem : Ctor α Attr) (m : Member) (hm : ∀ x, (elem.into x).member = m)
    {xs : List α} {ws : List Value} (hxs : xs ≠ [])
    (htr : traverse (fun x => c.p (elem.into x)) xs = some ws) :
    ∃ as', traverse c.e ws = some as' ∧ as' ≠ [] ∧ ∀ y ∈ as', y.member = m := by
  obtain ⟨as', has'⟩ := Option.isSome_iff_exists.mp
    (traverse_isSome (f := c.e) (fun _ _ hyx => h.canon hyx) xs ws htr)
  have hmem : ∀ y ∈ as', y.member = m := by
    have hz := traverse_rel (g := fun x => c.p (elem.into x)) (f := c.e)
      (R := fun z (_ : α) => z.member = m)
      (fun x0 _ z hg hf => by
        show z.member = m
        rw [(h.agree hg hf).member_eq, hm x0])
      xs ws as' htr has'
    intro y hy
    have hlen1 := traverse_length xs ws htr
    have hlen2 := traverse_length ws as' has'
    obtain ⟨y2, hy2⟩ := mem_zip_left as' xs (by omega) y hy
    exact hz (y, y2) hy2
  refine ⟨as', has', ?_, hmem⟩
  intro h0
  have hlen1 := traverse_length xs ws htr
  have hlen2 := traverse_length ws as' has'
  rw [h0] at hlen2
  cases xs with
  | nil => exact absurd rfl hxs
  | cons _ _ => simp only [List.length_cons, List.length_nil] at hlen1 hlen2; omega

/-- `setCodec`'s `canon`, stated once. The payload family enters only through `elem` and
    the two facts about the member it names. -/
theorem setCodec_canon_of {α : Type} {c : Codec} (h : Lawful c)
    (elem : Ctor α Attr) (m wm : Member) (hm : ∀ x, (elem.into x).member = m)
    (hwire : ∀ as : List Attr, as ≠ [] → (∀ y ∈ as, y.member = m) →
      ∃ a', asWireSet as = some a' ∧ a'.member = wm)
    {xs : List α} {t : Value} (hxs : xs ≠ [])
    (hp : (traverse (fun x => c.p (elem.into x)) xs).map Value.set = some t) :
    ((setCodec c).e t).isSome := by
  cases htr : traverse (fun x => c.p (elem.into x)) xs with
  | none => rw [htr] at hp; exact nomatch hp
  | some ws =>
    rw [htr] at hp
    replace hp : some (Value.set ws) = some t := hp
    cases hp
    obtain ⟨as', has', hne', hmem⟩ := setCodec_reencode_of h elem m hm hxs htr
    obtain ⟨a', ha', -⟩ := hwire as' hne' hmem
    show ((traverse c.e ws).bind asWireSet).isSome
    rw [has']
    show (asWireSet as').isSome
    rw [ha']
    rfl

/-- `setCodec`'s `agree`, stated once. Wire sets are flat, so the whole content is that
    the re-encoding lands on the same wire member — no payload is ever inspected. -/
theorem setCodec_agree_of {α : Type} {c : Codec} (h : Lawful c)
    (elem : Ctor α Attr) (m wm : Member) (hm : ∀ x, (elem.into x).member = m)
    (hwire : ∀ as : List Attr, as ≠ [] → (∀ y ∈ as, y.member = m) →
      ∃ a', asWireSet as = some a' ∧ a'.member = wm)
    (hL : wm ≠ .L) (hM : wm ≠ .M)
    {xs : List α} {t : Value} {a a' : Attr} (hxs : xs ≠ [])
    (ha : a.member = wm)
    (hp : (traverse (fun x => c.p (elem.into x)) xs).map Value.set = some t)
    (he : (setCodec c).e t = some a') : Agree a' a := by
  cases htr : traverse (fun x => c.p (elem.into x)) xs with
  | none => rw [htr] at hp; exact nomatch hp
  | some ws =>
    rw [htr] at hp
    replace hp : some (Value.set ws) = some t := hp
    cases hp
    obtain ⟨as', has', hne', hmem⟩ := setCodec_reencode_of h elem m hm hxs htr
    replace he : (traverse c.e ws).bind asWireSet = some a' := he
    rw [has'] at he
    replace he : asWireSet as' = some a' := he
    obtain ⟨a'', ha'', hwm⟩ := hwire as' hne' hmem
    rw [ha''] at he
    cases he
    exact agree_of_member_flat (by rw [hwm, ha]) (by rw [hwm]; exact hL) (by rw [hwm]; exact hM)

/-! #### (R) and (W), argued once for both strengths

These two clauses read the same whether the element codec is `Lawful` or only
`LawfulCore` — (MP) contributes nothing to either — so they are stated once and both
`lawfulCore_setCodec` and `lawful_setCodec` cite them. What the two strengths really
differ on is (C): with (MP) the element's member comes from agreement, without it the
`(set)` rule's own premise supplies it. -/

/-- (R) per family: a wire set reads back by the same traversal, through the same prism
    the payload projection put it in. -/
theorem setCodec_retract_of {α : Type} {c : Codec} (h : LawfulCore c) (elem : Ctor α Attr)
    {vs : List Value} {x : α} {xs : List α}
    (htr : traverse c.e vs = some ((x :: xs).map elem.into)) :
    (traverse (fun y => c.p (elem.into y)) (x :: xs)).map Value.set = some (.set vs) := by
  have h1 := traverse_roundTrip (fun _ _ hxy => h.retract hxy) vs _ htr
  rw [traverse_map] at h1
  rw [h1]
  rfl

theorem set_retract {c : Codec} (h : LawfulCore c) :
    ∀ {t a}, (setCodec c).e t = some a → (setCodec c).p a = some t := by
  intro t a he
  obtain ⟨vs, as, rfl, htr, hw⟩ := setCodec_e_eq.mp he
  obtain ⟨hne, hcase⟩ := asWireSet_cases hw
  rcases hcase with ⟨ss, rfl, rfl⟩ | ⟨ns, rfl, rfl⟩ | ⟨bs, rfl, rfl⟩
  · cases ss with
    | nil => exact absurd rfl hne
    | cons _ _ => exact setCodec_retract_of h sC htr
  · cases ns with
    | nil => exact absurd rfl hne
    | cons _ _ => exact setCodec_retract_of h nC htr
  · cases bs with
    | nil => exact absurd rfl hne
    | cons _ _ => exact setCodec_retract_of h bC htr

/-- (W) per family: the wire member is `setMember` of the element member, and the first
    element is enough to name the latter. -/
theorem setCodec_writes_of {α : Type} {elem : Ctor α Attr} {μE μS μ₀ μ : Member}
    (hm : ∀ x, (elem.into x).member = μE) (hsm : setMember μE = some μS)
    {x : α} {xs : List α} (hmem : ∀ y ∈ (x :: xs).map elem.into, y.member = μ₀)
    (hμ : setMember μ₀ = some μ) : μS = μ := by
  have hx := hmem _ (List.mem_cons_self _ _)
  rw [hm] at hx
  subst hx
  rw [hsm] at hμ
  exact Option.some.inj hμ

theorem set_writes {c : Codec} (h : LawfulCore c) :
    ∀ {μ}, (setCodec c).μ = some μ → ∀ {t a}, (setCodec c).e t = some a →
      a.member = μ := by
  intro μ hμ t a he
  obtain ⟨vs, as, rfl, htr, hw⟩ := setCodec_e_eq.mp he
  replace hμ : c.μ.bind setMember = some μ := hμ
  cases hc : c.μ with
  | none => rw [hc] at hμ; exact nomatch hμ
  | some μ₀ =>
    rw [hc] at hμ
    replace hμ : setMember μ₀ = some μ := hμ
    have hmem := traverse_mem (P := fun y => y.member = μ₀)
      (fun _ y hxy => h.writes hc hxy) htr
    obtain ⟨hne, hcase⟩ := asWireSet_cases hw
    rcases hcase with ⟨ss, rfl, rfl⟩ | ⟨ns, rfl, rfl⟩ | ⟨bs, rfl, rfl⟩
    · cases ss with
      | nil => exact absurd rfl hne
      | cons _ _ => exact setCodec_writes_of (elem := sC) (fun _ => rfl) rfl hmem hμ
    · cases ns with
      | nil => exact absurd rfl hne
      | cons _ _ => exact setCodec_writes_of (elem := nC) (fun _ => rfl) rfl hmem hμ
    · cases bs with
      | nil => exact absurd rfl hne
      | cons _ _ => exact setCodec_writes_of (elem := bC) (fun _ => rfl) rfl hmem hμ

/-- Core set: the member-uniformity that (MP) supplied comes from (W) instead, so the
    element's named member is a hypothesis — exactly the `(set)` rule's premise. -/
theorem lawfulCore_setCodec {c : Codec} {μ₀ μS : Member} (h : LawfulCore c)
    (hμ : c.μ = some μ₀) (hsm : setMember μ₀ = some μS) :
    LawfulCore (setCodec c) := by
  refine ⟨set_retract h, ?_, set_writes h⟩
  have hbranch : ∀ (ws : List Value), ∀ as', traverse c.e ws = some as' → ws ≠ [] →
      ((traverse c.e ws).bind asWireSet).isSome = true := by
    intro ws as' has' hws
    have hmem : ∀ x ∈ as', x.member = μ₀ :=
      traverse_mem (fun _ y hxy => h.writes hμ hxy) has'
    have hne' : as' ≠ [] := by
      intro h0
      have hlen := traverse_length ws as' has'
      rw [h0] at hlen
      exact hws (List.length_eq_zero.mp hlen)
    rw [has']
    show (asWireSet as').isSome = true
    cases as' with
    | nil => exact absurd rfl hne'
    | cons x r =>
      have hx := hmem x (List.mem_cons_self x r)
      cases μ₀
      case S =>
        obtain ⟨ss', hss'⟩ := strPayloads_isSome hmem
        simp only [asWireSet]; rw [hss']; rfl
      case N =>
        obtain ⟨ns', hns'⟩ := numPayloads_isSome hmem
        cases x
        case n v => simp only [asWireSet, strPayloads]; rw [hns']; rfl
        all_goals exact nomatch hx
      case B =>
        obtain ⟨bs', hbs'⟩ := binPayloads_isSome hmem
        cases x
        case b v => simp only [asWireSet, strPayloads, numPayloads]; rw [hbs']; rfl
        all_goals exact nomatch hx
      all_goals exact nomatch hsm
  have branch : ∀ {α : Type} (elem : Ctor α Attr) (x : α) (r : List α) (t : Value),
      (traverse (fun y => c.p (elem.into y)) (x :: r)).map Value.set = some t →
      ((setCodec c).e t).isSome = true := by
    intro α elem x r t hp
    obtain ⟨ws, htr, rfl⟩ := Option.map_eq_some'.mp hp
    show ((traverse c.e ws).bind asWireSet).isSome = true
    obtain ⟨as', has'⟩ := Option.isSome_iff_exists.mp
      (traverse_isSome (f := c.e) (fun _ _ hyx => h.canon hyx) (x :: r) ws htr)
    refine hbranch ws as' has' ?_
    intro h0
    have hlen := traverse_length (x :: r) ws htr
    rw [h0] at hlen
    exact nomatch hlen
  intro a t hp
  cases a
  case ss vs' => cases vs' with
    | nil => exact nomatch hp
    | cons _ _ => exact branch sC _ _ t hp
  case ns vs' => cases vs' with
    | nil => exact nomatch hp
    | cons _ _ => exact branch nC _ _ t hp
  case bs vs' => cases vs' with
    | nil => exact nomatch hp
    | cons _ _ => exact branch bC _ _ t hp
  all_goals exact nomatch hp

/-- The quotiented product; `p` need not be injective — the shrink is the quotient. -/
theorem lawful_setCodec {c : Codec} (h : Lawful c) : Lawful (setCodec c) := by
  refine ⟨set_retract h.core, ?_, set_writes h.core, ?_⟩
  · intro a t hp
    cases a
    case ss vs' => cases vs' with
      | nil => exact nomatch hp
      | cons _ _ =>
        exact setCodec_canon_of h sC .S .SS (fun _ => rfl)
          (fun _ hne hmem => asWireSet_of_S hne hmem) (by simp) hp
    case ns vs' => cases vs' with
      | nil => exact nomatch hp
      | cons _ _ =>
        exact setCodec_canon_of h nC .N .NS (fun _ => rfl)
          (fun _ hne hmem => asWireSet_of_N hne hmem) (by simp) hp
    case bs vs' => cases vs' with
      | nil => exact nomatch hp
      | cons _ _ =>
        exact setCodec_canon_of h bC .B .BS (fun _ => rfl)
          (fun _ hne hmem => asWireSet_of_B hne hmem) (by simp) hp
    all_goals exact nomatch hp
  · intro a t a' hp he
    cases a
    case ss vs' => cases vs' with
      | nil => exact nomatch hp
      | cons _ _ =>
        exact setCodec_agree_of h sC .S .SS (fun _ => rfl)
          (fun _ hne hmem => asWireSet_of_S hne hmem) (by decide) (by decide)
          (by simp) rfl hp he
    case ns vs' => cases vs' with
      | nil => exact nomatch hp
      | cons _ _ =>
        exact setCodec_agree_of h nC .N .NS (fun _ => rfl)
          (fun _ hne hmem => asWireSet_of_N hne hmem) (by decide) (by decide)
          (by simp) rfl hp he
    case bs vs' => cases vs' with
      | nil => exact nomatch hp
      | cons _ _ =>
        exact setCodec_agree_of h bC .B .BS (fun _ => rfl)
          (fun _ hne hmem => asWireSet_of_B hne hmem) (by decide) (by decide)
          (by simp) rfl hp he
    all_goals exact nomatch hp


/-! ### Keyed lookup and traversal facts (the keyed product consumes these) -/


/-- `fbDefaults` is a `filterMap`: the `fb` fields whose name the row omits, paired with
    their stand-ins. Stating it that way retires four hand-rolled recursions in favour of
    mathlib's `mem_filterMap`. -/
theorem fbDefaults_eq (names : List Name) (sems : List (Name × FieldSem)) :
    fbDefaults names sems
      = sems.filterMap fun kf =>
          match kf.2 with
          | .fb _ v => if names.contains kf.1 then none else some (kf.1, v)
          | _ => none := by
  induction sems with
  | nil => rfl
  | cons kf sems ih =>
    obtain ⟨k, f⟩ := kf
    cases f <;> simp [fbDefaults, List.filterMap, ih]
    split <;> simp_all [fbDefaults]

theorem fbDefaults_mem {sems : List (Name × FieldSem)} {names k c v}
    (hm : (k, FieldSem.fb c v) ∈ sems) (hc : names.contains k = false) :
    (k, v) ∈ fbDefaults names sems := by
  rw [fbDefaults_eq]
  exact List.mem_filterMap.mpr ⟨(k, .fb c v), hm, by
    simp only []
    rw [if_neg (by simpa using hc)]⟩

theorem fbDefaults_spec {sems : List (Name × FieldSem)} {names k v}
    (hm : (k, v) ∈ fbDefaults names sems) :
    ∃ c, (k, FieldSem.fb c v) ∈ sems ∧ names.contains k = false := by
  rw [fbDefaults_eq] at hm
  obtain ⟨⟨k', f⟩, hmem, hg⟩ := List.mem_filterMap.mp hm
  cases f with
  | req _ => exact nomatch hg
  | opt _ => exact nomatch hg
  | fb c v' =>
    simp only [] at hg
    split at hg
    · exact nomatch hg
    · obtain ⟨rfl, rfl⟩ := by simpa using hg
      exact ⟨c, hmem, by simpa using ‹¬names.contains k' = true›⟩

theorem fbDefaults_nil {sems : List (Name × FieldSem)} {names}
    (h : ∀ k c v, (k, FieldSem.fb c v) ∈ sems → names.contains k = true) :
    fbDefaults names sems = [] := by
  cases h' : fbDefaults names sems with
  | nil => rfl
  | cons x xs =>
    obtain ⟨k, v⟩ := x
    obtain ⟨c, hmem, hc⟩ := fbDefaults_spec (by rw [h']; exact List.mem_cons_self _ _)
    rw [h k c v hmem] at hc
    exact nomatch hc

theorem fbDefaults_not_mem {sems : List (Name × FieldSem)} {names k}
    (hc : names.contains k = true) : k ∉ (fbDefaults names sems).map (·.1) := by
  intro hm
  obtain ⟨⟨k', v⟩, hmem, rfl⟩ := List.mem_map.mp hm
  obtain ⟨-, -, hc'⟩ := fbDefaults_spec hmem
  rw [hc] at hc'
  exact nomatch hc'

/-- The guard characterizations, via `List.all`. -/
theorem valPresentB_spec {sems : List (Name × FieldSem)} {names : List Name}
    (h : valPresentB sems names = true) {k fs} (hm : (k, fs) ∈ sems)
    (hno : ∀ c, fs ≠ FieldSem.opt c) : names.contains k = true := by
  have := List.all_eq_true.mp h (k, fs) hm
  cases fs with
  | opt c => exact absurd rfl (hno c)
  | req c => exact this
  | fb c v => exact this

theorem valPresentB_of {sems : List (Name × FieldSem)} {names : List Name}
    (h : ∀ k fs, (k, fs) ∈ sems → (∀ c, fs ≠ FieldSem.opt c) →
      names.contains k = true) : valPresentB sems names = true := by
  refine List.all_eq_true.mpr fun kf hkf => ?_
  obtain ⟨k, fs⟩ := kf
  cases fs with
  | opt c => rfl
  | req c => exact h k (.req c) hkf (fun _ h' => nomatch h')
  | fb c v => exact h k (.fb c v) hkf (fun _ h' => nomatch h')

theorem reqPresentB_spec {sems : List (Name × FieldSem)} {names : List Name}
    (h : reqPresentB sems names = true) {k c} (hm : (k, FieldSem.req c) ∈ sems) :
    names.contains k = true :=
  List.all_eq_true.mp h (k, .req c) hm

theorem reqPresentB_of {sems : List (Name × FieldSem)} {names : List Name}
    (h : ∀ k c, (k, FieldSem.req c) ∈ sems → names.contains k = true) :
    reqPresentB sems names = true := by
  refine List.all_eq_true.mpr fun kf hkf => ?_
  obtain ⟨k, fs⟩ := kf
  cases fs with
  | req c => exact h k c hkf
  | opt c => rfl
  | fb c v => rfl


/-! ### The keyed steps: round trip, definedness, agreement, and name preservation -/

theorem encEntry_fst {sems : List (Name × FieldSem)} {rc? : Option Codec} :
    ∀ (kv : Name × Value) (ka : Name × Attr),
      encEntry (fun k => sems.lookup k) (rc?.map (·.e)) kv = some ka → ka.1 = kv.1 := by
  intro ⟨k, v⟩ ka h
  simp only [encEntry] at h
  cases hsp : sems.lookup k with
  | some fs =>
    rw [hsp] at h
    replace h : (fs.codec.e v).map ((k, ·)) = some ka := h
    cases hev : fs.codec.e v with
    | none => rw [hev] at h; exact nomatch h
    | some a₀ =>
      rw [hev] at h
      replace h : some (k, a₀) = some ka := h
      cases h
      rfl
  | none =>
    rw [hsp] at h
    cases rc? with
    | none => exact nomatch h
    | some rc =>
      replace h : (rc.e v).map ((k, ·)) = some ka := h
      cases hev : rc.e v with
      | none => rw [hev] at h; exact nomatch h
      | some a₀ =>
        rw [hev] at h
        replace h : some (k, a₀) = some ka := h
        cases h
        rfl

theorem decEntry_fst {sems : List (Name × FieldSem)} {rc? : Option Codec} :
    ∀ (ka : Name × Attr) (kv : Name × Value),
      decEntry (fun k => sems.lookup k) (rc?.map (·.p)) ka = some kv → kv.1 = ka.1 := by
  intro ⟨k, a⟩ kv h
  simp only [decEntry] at h
  cases hsp : sems.lookup k with
  | some fs =>
    rw [hsp] at h
    replace h : (fs.codec.p a).map ((k, ·)) = some kv := h
    cases hpa : fs.codec.p a with
    | none => rw [hpa] at h; exact nomatch h
    | some v₀ =>
      rw [hpa] at h
      replace h : some (k, v₀) = some kv := h
      cases h
      rfl
  | none =>
    rw [hsp] at h
    cases rc? with
    | none => exact nomatch h
    | some rc =>
      replace h : (rc.p a).map ((k, ·)) = some kv := h
      cases hpa : rc.p a with
      | none => rw [hpa] at h; exact nomatch h
      | some v₀ =>
        rw [hpa] at h
        replace h : some (k, v₀) = some kv := h
        cases h
        rfl

/-! ### Carriers, continued: objects

    Placed here, after the name-dispatch helpers `p` needs. -/

/-- An entry survives `p`'s name filter and so appears among its outputs. -/
theorem mem_decoded_names {kvs : List (Name × Attr)} {kn : Name → Bool}
    {sems : List (Name × FieldSem)} {rc? : Option Codec} {ds k}
    (htr : traverse (decEntry (fun k' => sems.lookup k') (rc?.map (·.p)))
      (kvs.filter fun kv => kn kv.1) = some ds)
    (hk : k ∈ kvs.map (·.1)) (hkeep : kn k = true) : k ∈ ds.map (·.1) := by
  rw [traverse_fst decEntry_fst htr]
  obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp hk
  exact List.mem_map.mpr ⟨kv, List.mem_filter.mpr ⟨hkv, hkeep⟩, rfl⟩

/-- Every entry lands on the set its name declares — the write side. -/
theorem entry_domE {sems : List (Name × FieldSem)} {rc? : Option Codec}
    (hs : ∀ kf ∈ sems, Carrier kf.2.codec) (hrc : ∀ c ∈ rc?, Carrier c) :
    ∀ kv ka, encEntry (fun k => sems.lookup k) (rc?.map (·.e)) kv = some ka →
      objEntryT sems rc? kv := by
  rintro kv ka h
  obtain ⟨c, a, hc, he, rfl⟩ := encEntry_eq.mp h
  exact objEntryT_eq.mpr ⟨c, hc, (entryCodec_of hs hrc hc).domE he⟩

/-- …and the read side. -/
theorem entry_ranP {sems : List (Name × FieldSem)} {rc? : Option Codec}
    (hs : ∀ kf ∈ sems, Carrier kf.2.codec) (hrc : ∀ c ∈ rc?, Carrier c) :
    ∀ ka kv, decEntry (fun k => sems.lookup k) (rc?.map (·.p)) ka = some kv →
      objEntryT sems rc? kv := by
  rintro ka kv h
  obtain ⟨c, v, hc, hp, rfl⟩ := decEntry_eq.mp h
  exact objEntryT_eq.mpr ⟨c, hc, (entryCodec_of hs hrc hc).ranP hp⟩

/-- §4's held set, both ways. The two premises past lawfulness are the doc's own:
    `hfb` is `(fallback)`'s `v(∗) ∈ dom(e)`, which with `domE` gives §4's `v : 𝟙 → T`;
    `hkeep` says the name filter never discards a declared name, which is what all
    three rest policies do.

    Writing is immediate. Reading has to account for the stand-ins: every non-`opt`
    name is present in the result — a `req` from the row it was stored in, an `fb`
    from the row or else from its stand-in — and every entry is on its set, the kept
    ones by `entry_ranP`, the stand-ins by `hfb`. -/
theorem carrier_objectCodecCore {sems : List (Name × FieldSem)} {rc? : Option Codec}
    {kn : Name → Bool}
    (hsems : ∀ kf ∈ sems, Carrier kf.2.codec)
    (hrc : ∀ rc, rc? = some rc → Carrier rc)
    (hfb : ∀ kf ∈ sems, ∀ c v, kf.2 = .fb c v → (c.e v).isSome)
    (hnd : (sems.map (·.1)).Nodup)
    (hkeep : ∀ k, (sems.lookup k).isSome → kn k = true) :
    Carrier (objectCodecCore sems rc? kn) := by
  refine objectCodecCore_eq ▸ carrier_carried ?_ ?_
  · intro kvs kas h
    obtain ⟨hval, htr⟩ := objWrite_eq.mp h
    exact ⟨hval, traverse_mem_input (entry_domE hsems hrc) htr⟩
  · intro kas kvs h
    obtain ⟨ds, hreq, htr, rfl⟩ := objRead_eq.mp h
    refine ⟨valPresentB_of fun k fs hm hno => ?_, ?_⟩
    · have hkn : kn k = true := hkeep k (by rw [lookup_eq_of_mem_nodup hnd hm]; rfl)
      rw [List.map_append]
      refine List.elem_eq_true_of_mem (List.mem_append.mpr ?_)
      cases fs with
      | opt c => exact absurd rfl (hno c)
      | req c =>
        exact Or.inl (mem_decoded_names htr
          (mem_of_contains (List.all_eq_true.mp hreq (k, .req c) hm)) hkn)
      | fb c v₀ =>
        cases hc : (kas.map (·.1)).contains k with
        | true => exact Or.inl (mem_decoded_names htr (mem_of_contains hc) hkn)
        | false => exact Or.inr (List.mem_map.mpr ⟨(k, v₀), fbDefaults_mem hm hc, rfl⟩)
    · intro kv hkv
      rcases List.mem_append.mp hkv with hd | hfd
      · exact traverse_mem (entry_ranP hsems hrc) htr kv hd
      · obtain ⟨c, hmem, hc⟩ := fbDefaults_spec hfd
        obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
          (hfb (kv.1, .fb c kv.2) hmem c kv.2 rfl)
        exact objEntryT_eq.mpr ⟨c, by
          simp [entryCodec, lookup_eq_of_mem_nodup hnd hmem, FieldSem.codec],
          (hsems (kv.1, .fb c kv.2) hmem).domE ha'⟩

private theorem objStep_rt {sems : List (Name × FieldSem)} {rc? : Option Codec}
    (hf : ∀ kf ∈ sems, LawfulCore kf.2.codec) (hrc : ∀ c ∈ rc?, LawfulCore c) :
    ∀ kv ka, encEntry (fun k => sems.lookup k) (rc?.map (·.e)) kv = some ka →
      decEntry (fun k => sems.lookup k) (rc?.map (·.p)) ka = some kv := by
  rintro ⟨k, v⟩ ka h
  obtain ⟨c, a, hc, he, rfl⟩ := encEntry_eq.mp h
  exact decEntry_eq.mpr ⟨c, v, hc, (entryCodec_of hf hrc hc).retract he, rfl⟩

private theorem objStep_canon {sems : List (Name × FieldSem)} {rc? : Option Codec}
    (hf : ∀ kf ∈ sems, LawfulCore kf.2.codec) (hrc : ∀ c ∈ rc?, LawfulCore c) :
    ∀ ka kv, decEntry (fun k => sems.lookup k) (rc?.map (·.p)) ka = some kv →
      (encEntry (fun k => sems.lookup k) (rc?.map (·.e)) kv).isSome = true := by
  rintro ⟨k, a⟩ kv h
  obtain ⟨c, v, hc, hp, rfl⟩ := decEntry_eq.mp h
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ((entryCodec_of hf hrc hc).canon hp)
  exact Option.isSome_iff_exists.mpr ⟨_, encEntry_eq.mpr ⟨c, a', hc, ha', rfl⟩⟩

private theorem objStep_agree {sems : List (Name × FieldSem)} {rc? : Option Codec}
    (hf : ∀ kf ∈ sems, Lawful kf.2.codec) (hrc : ∀ c ∈ rc?, Lawful c) :
    ∀ ka kv ka', decEntry (fun k => sems.lookup k) (rc?.map (·.p)) ka = some kv →
      encEntry (fun k => sems.lookup k) (rc?.map (·.e)) kv = some ka' →
      ka'.1 = ka.1 ∧ Agree ka'.2 ka.2 := by
  rintro ⟨k, a⟩ kv ka' h h'
  obtain ⟨c, v, hc, hp, rfl⟩ := decEntry_eq.mp h
  obtain ⟨c', a', hc', he, rfl⟩ := encEntry_eq.mp h'
  cases hc'.symm.trans hc
  exact ⟨rfl, (entryCodec_of hf hrc hc).agree hp he⟩


/-! #### §2's clauses for the object's payload pair

Each is proved once, from core children, and both `lawfulCore_objectCore` and
`lawful_objectCore` consume them. -/

section ObjectLaws
variable {sems : List (Name × FieldSem)} {rc? : Option Codec} {kn : Name → Bool}

/-- (R): a written row is complete — every declared name present, none filtered out, no
    stand-in owed — so reading it back is the entrywise round trip and nothing else. -/
theorem object_retract (hf : ∀ kf ∈ sems, LawfulCore kf.2.codec)
    (hrc : ∀ c ∈ rc?, LawfulCore c)
    (hknE : ∀ kv ka, encEntry (fun k => sems.lookup k) (rc?.map (·.e)) kv = some ka →
      kn ka.1 = true) :
    ∀ kvs kas, objWrite sems rc? kvs = some kas → objRead sems rc? kn kas = some kvs := by
  intro kvs kas h
  obtain ⟨hval, htr⟩ := objWrite_eq.mp h
  have hnames : kas.map (·.1) = kvs.map (·.1) := traverse_fst encEntry_fst htr
  refine objRead_eq.mpr ⟨kvs, ?_, ?_, ?_⟩
  · rw [hnames]
    exact reqPresentB_of fun k c hm => valPresentB_spec hval hm (fun _ h' => nomatch h')
  · rw [filter_eq_self_of_all fun d hd => by
      obtain ⟨kv, _, hkv⟩ := traverse_mem₂ htr d hd
      exact hknE kv d hkv]
    exact traverse_roundTrip (objStep_rt hf hrc) kvs kas htr
  · rw [hnames, fbDefaults_nil fun k c v hm =>
      valPresentB_spec hval hm (fun _ h' => nomatch h'), List.append_nil]

/-- (C): what was read is writable again — the kept entries by (C) one level down, the
    stand-ins by `(fallback)`'s own premise `v(∗) ∈ dom(e)`. -/
theorem object_canon (hf : ∀ kf ∈ sems, LawfulCore kf.2.codec)
    (hrc : ∀ c ∈ rc?, LawfulCore c)
    (hfb : ∀ kf ∈ sems, ∀ c v, kf.2 = .fb c v → (c.e v).isSome = true)
    (hnd : (sems.map (·.1)).Nodup)
    (hknDecl : ∀ k, (sems.lookup k).isSome = true → kn k = true) :
    ∀ kas kvs, objRead sems rc? kn kas = some kvs →
      (objWrite sems rc? kvs).isSome = true := by
  intro kas kvs h
  obtain ⟨ds, hreq, htr, rfl⟩ := objRead_eq.mp h
  obtain ⟨es₁, hes₁⟩ := Option.isSome_iff_exists.mp
    (traverse_isSome (f := encEntry (fun k => sems.lookup k) (rc?.map (·.e)))
      (objStep_canon hf hrc) (kas.filter fun ka => kn ka.1) ds htr)
  have hdefs : ∀ x ∈ fbDefaults (kas.map (·.1)) sems,
      ((encEntry (fun k => sems.lookup k) (rc?.map (·.e))) x).isSome = true := by
    rintro ⟨k', v'⟩ hx
    obtain ⟨c, hmem, hcf⟩ := fbDefaults_spec hx
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hfb (k', .fb c v') hmem c v' rfl)
    exact Option.isSome_iff_exists.mpr ⟨(k', a'), encEntry_eq.mpr ⟨c, a',
      by simp [entryCodec, lookup_eq_of_mem_nodup hnd hmem, FieldSem.codec], ha', rfl⟩⟩
  obtain ⟨es₂, hes₂⟩ := Option.isSome_iff_exists.mp (traverse_isSome_of_all hdefs)
  have hnames : ds.map (·.1) = (kas.filter fun ka => kn ka.1).map (·.1) :=
    traverse_fst decEntry_fst htr
  refine Option.isSome_iff_exists.mpr ⟨_, objWrite_eq.mpr ⟨?_, traverse_append hes₁ hes₂⟩⟩
  refine valPresentB_of fun k fs hm hno => ?_
  rw [List.map_append]
  cases hck : (kas.map (·.1)).contains k with
  | true =>
    obtain ⟨ax, haxm⟩ := exists_of_mem_fst (mem_of_contains hck)
    have hknk : kn k = true := hknDecl k (lookup_isSome_of_mem_fst
      (List.mem_map.mpr ⟨(k, fs), hm, rfl⟩))
    have hkfl : k ∈ (kas.filter fun ka => kn ka.1).map (·.1) :=
      List.mem_map.mpr ⟨(k, ax), List.mem_filter.mpr ⟨haxm, hknk⟩, rfl⟩
    rw [← hnames] at hkfl
    exact contains_of_mem (List.mem_append.mpr (Or.inl hkfl))
  | false =>
    cases fs with
    | opt c => exact absurd rfl (hno c)
    | req c => rw [reqPresentB_spec hreq hm] at hck; exact nomatch hck
    | fb c v =>
      exact contains_of_mem (List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨(k, v), fbDefaults_mem hm hck, rfl⟩)))

/-- (MP): the stand-ins have no stored counterpart to disagree with — they are exactly
    the names the row omitted — so `≼` is decided on the kept entries, by name. -/
theorem object_agree (hf : ∀ kf ∈ sems, Lawful kf.2.codec) (hrc : ∀ c ∈ rc?, Lawful c) :
    ∀ kas kvs kas', objRead sems rc? kn kas = some kvs →
      objWrite sems rc? kvs = some kas' → Agree (mA.into kas') (mA.into kas) := by
  intro kas kvs kas' hD hE
  obtain ⟨ds, hreq, htr, rfl⟩ := objRead_eq.mp hD
  obtain ⟨hval, hall⟩ := objWrite_eq.mp hE
  obtain ⟨es₁, es₂, rfl, h₁, h₂⟩ := traverse_append_inv hall
  refine .m (es₁ ++ es₂) kas ?_
  intro k x y hxk hyk
  have hnodef : k ∉ (fbDefaults (kas.map (·.1)) sems).map (·.1) :=
    fbDefaults_not_mem (contains_of_mem (mem_fst_of_lookup hyk))
  have hnoes₂ : es₂.lookup k = none :=
    lookup_none_of_not_mem_fst (by rw [traverse_fst encEntry_fst h₂]; exact hnodef)
  rw [lookup_append es₁ es₂ k] at hxk
  cases h₁k : es₁.lookup k with
  | none => rw [h₁k, hnoes₂] at hxk; exact nomatch hxk
  | some x' =>
    rw [h₁k] at hxk
    replace hxk : some x' = some x := hxk
    cases hxk
    cases hknk : kn k with
    | false =>
      rw [lookup_none_of_not_mem_fst (by
        rw [traverse_fst encEntry_fst h₁, traverse_fst decEntry_fst htr]
        intro hmm
        have h1 := lookup_isSome_of_mem_fst hmm
        rw [lookup_filter_neg hknk kas] at h1
        exact nomatch h1)] at h₁k
      exact nomatch h₁k
    | true =>
      refine lookup_rel es₁ (kas.filter fun ka => kn ka.1) ?_ ?_ k x y h₁k ?_
      · have l1 := traverse_length (kas.filter fun ka => kn ka.1) ds htr
        have l2 := traverse_length ds es₁ h₁
        omega
      · exact traverse_rel (objStep_agree hf hrc) _ _ _ htr h₁
      · rw [lookup_filter_pos hknk kas]; exact hyk

end ObjectLaws

/-- Core keyed product: (R), (C), (W) with only core children. -/
private theorem lawfulCore_objectCore
    (sems : List (Name × FieldSem)) (rc? : Option Codec) (kn : Name → Bool)
    (hf : ∀ kf ∈ sems, LawfulCore kf.2.codec)
    (hfb : ∀ kf ∈ sems, ∀ c v, kf.2 = .fb c v → (c.e v).isSome = true)
    (hnd : (sems.map (·.1)).Nodup)
    (hrc : ∀ c ∈ rc?, LawfulCore c)
    (hknE : ∀ kv ka, encEntry (fun k => sems.lookup k) (rc?.map (·.e)) kv = some ka →
      kn ka.1 = true)
    (hknDecl : ∀ k, (sems.lookup k).isSome = true → kn k = true) :
    LawfulCore (objectCodecCore sems rc? kn) :=
  objectCodecCore_eq ▸ lawfulCore_carried (fun _ => rfl)
    (object_retract hf hrc hknE) (object_canon hf hrc hfb hnd hknDecl)

/-- The keyed product, parametrically: the same three clauses, plus (MP). -/
private theorem lawful_objectCore
    (sems : List (Name × FieldSem)) (rc? : Option Codec) (kn : Name → Bool)
    (hf : ∀ kf ∈ sems, Lawful kf.2.codec)
    (hfb : ∀ kf ∈ sems, ∀ c v, kf.2 = .fb c v → (c.e v).isSome = true)
    (hnd : (sems.map (·.1)).Nodup)
    (hrc : ∀ c ∈ rc?, Lawful c)
    (hknE : ∀ kv ka, encEntry (fun k => sems.lookup k) (rc?.map (·.e)) kv = some ka →
      kn ka.1 = true)
    (hknDecl : ∀ k, (sems.lookup k).isSome = true → kn k = true) :
    Lawful (objectCodecCore sems rc? kn) :=
  let hf' := fun kf hkf => (hf kf hkf).core
  let hrc' := fun c hc => (hrc c hc).core
  objectCodecCore_eq ▸ lawful_carried (fun _ => rfl)
    (object_retract hf' hrc' hknE) (object_canon hf' hrc' hfb hnd hknDecl)
    (object_agree hf hrc)

/-- A property of the rest policy's codec, from one per `rest = .codec c`. -/
theorem rcOf_forall {P : Codec → Prop} {rest : RestSem}
    (h : ∀ c, rest = .codec c → P c) : ∀ c ∈ rcOf rest, P c := by
  intro c hc
  cases rest with
  | codec c' =>
    replace hc : some c' = some c := hc
    cases hc
    exact h c rfl
  | drop => exact nomatch hc
  | refuse => exact nomatch hc

/-- What object-encode produces, `keepB` keeps: under `drop` an encoded entry's name
    is declared, and the other policies keep everything. -/
theorem keepB_of_encEntry {sems : List (Name × FieldSem)} {rest : RestSem} :
    ∀ kv ka, encEntry (fun k => sems.lookup k) ((rcOf rest).map (·.e)) kv = some ka →
      keepB rest sems ka.1 = true := by
  intro kv ka h
  cases rest with
  | drop =>
    simp only [encEntry] at h
    cases hsp : sems.lookup kv.1 with
    | none =>
      rw [hsp] at h
      exact nomatch h
    | some fs =>
      rw [hsp] at h
      replace h : (fs.codec.e kv.2).map ((kv.1, ·)) = some ka := h
      cases hev : fs.codec.e kv.2 with
      | none => rw [hev] at h; exact nomatch h
      | some a₀ =>
        rw [hev] at h
        replace h : some (kv.1, a₀) = some ka := h
        cases h
        show (sems.lookup kv.1).isSome = true
        rw [hsp]
        rfl
  | refuse => rfl
  | codec rc => rfl

/-- Declared names pass every keep filter. -/
theorem keepB_of_declared {sems : List (Name × FieldSem)} {rest : RestSem} :
    ∀ k, (sems.lookup k).isSome = true → keepB rest sems k = true := by
  intro k h
  cases rest with
  | drop => exact h
  | refuse => rfl
  | codec rc => rfl

/-- The keyed product — the doc's `object`. `hfb` is §4's `v(∗) ∈ dom(e)`. -/
theorem lawful_objectCodec {sems : List (Name × FieldSem)} {rest : RestSem}
    (hf : ∀ kf ∈ sems, Lawful kf.2.codec)
    (hfb : ∀ kf ∈ sems, ∀ c v, kf.2 = .fb c v → (c.e v).isSome)
    (hnd : (sems.map (·.1)).Nodup)
    (hrest : ∀ c, rest = .codec c → Lawful c) :
    Lawful (objectCodec sems rest) :=
  lawful_objectCore sems (rcOf rest) (keepB rest sems) hf hfb hnd
    (rcOf_forall hrest) keepB_of_encEntry keepB_of_declared

theorem lawfulCore_objectCodec {sems : List (Name × FieldSem)} {rest : RestSem}
    (hf : ∀ kf ∈ sems, LawfulCore kf.2.codec)
    (hfb : ∀ kf ∈ sems, ∀ c v, kf.2 = .fb c v → (c.e v).isSome)
    (hnd : (sems.map (·.1)).Nodup)
    (hrest : ∀ c, rest = .codec c → LawfulCore c) :
    LawfulCore (objectCodec sems rest) :=
  lawfulCore_objectCore sems (rcOf rest) (keepB rest sems) hf hfb hnd
    (rcOf_forall hrest) keepB_of_encEntry keepB_of_declared

/-- The sum's core laws. (U) is what makes them hold: it says the option that wrote is
    the only one admitting either side of the pair, so the round trip comes back through
    the same option it went out through. -/
theorem lawfulCore_altCodec {os : List OptionSem} {μA : Option Member}
    (h : ∀ o ∈ os, LawfulCore o.c) (hU : UniqueAdmission os)
    (hW : ∀ m, μA = some m → ∀ o ∈ os, ∀ t a, o.c.e t = some a → a.member = m) :
    LawfulCore (altCodec os μA) where
  retract he := by
    obtain ⟨o, hf, hoe⟩ := altCodec_e.mp he
    have ho := (mem_of_filter_eq_singleton hf).1
    exact altCodec_p.mpr ⟨o, (hU o ho _ _ hoe).1, (h o ho).retract hoe⟩
  canon hp := by
    obtain ⟨o, hf, hop⟩ := altCodec_p.mp hp
    have ho := (mem_of_filter_eq_singleton hf).1
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ((h o ho).canon hop)
    exact Option.isSome_iff_exists.mpr
      ⟨a', altCodec_e.mpr ⟨o, (hU o ho _ _ ha').2, ha'⟩⟩
  writes := by
    intro μ hμ t a he
    obtain ⟨o, hf, hoe⟩ := altCodec_e.mp he
    exact hW μ hμ o (mem_of_filter_eq_singleton hf).1 t a hoe

/-- …and (MP) with them: the option that read is the option that re-writes, again by
    (U), so `≼` at the union is `≼` at that one option. -/
theorem lawful_altCodec {os : List OptionSem} {μA : Option Member}
    (h : ∀ o ∈ os, Lawful o.c) (hU : UniqueAdmission os)
    (hW : ∀ m, μA = some m → ∀ o ∈ os, ∀ t a, o.c.e t = some a → a.member = m) :
    Lawful (altCodec os μA) :=
  { lawfulCore_altCodec (fun o ho => (h o ho).core) hU hW with
    agree := by
      intro a t a' hp he
      obtain ⟨o, hf, hop⟩ := altCodec_p.mp hp
      have ho := (mem_of_filter_eq_singleton hf).1
      obtain ⟨a'', ha''⟩ := Option.isSome_iff_exists.mp ((h o ho).canon hop)
      obtain ⟨-, hV⟩ := hU o ho t a'' ha''
      obtain ⟨o', hf', hoe⟩ := altCodec_e.mp he
      have hoo : o' = o := by simpa using hf'.symm.trans hV
      subst hoo
      exact (h _ ho).agree hop hoe }


/-- Disjoint tag lists select at most one option, and a member tag selects exactly it —
    duplicates are impossible because a pair would be self-disjoint with a nonempty tag
    list. -/
theorem tag_filter_singleton {tag : String} :
    ∀ (os : List (List String × Codec)),
      List.Pairwise (fun x y => ∀ t ∈ x.1, t ∉ y.1) os →
      ∀ x ∈ os, tag ∈ x.1 →
      os.filter (fun y => y.1.contains tag) = [x]
  | [], _, x, hx, _ => nomatch hx
  | y :: os, hp, x, hx, htag => by
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
      rcases List.mem_cons.mp hx with rfl | hx'
      · have hnil : os.filter (fun y => y.1.contains tag) = [] :=
          filter_nil_of fun b hb =>
            contains_eq_false_of_not_mem (hhead b hb tag htag)
        simp only [List.filter, contains_of_mem htag, hnil]
      · have hny : tag ∉ y.1 := fun hin => (hhead x hx' tag hin) htag
        simp only [List.filter, contains_eq_false_of_not_mem hny]
        exact tag_filter_singleton os htail x hx' htag

/-! ### (U) by kind, and `opaque`'s fixpoint

    §5's other disjointness discharger, and the one `(opaque)` needs. An option is
    *pinned to a kind* when it admits only values and attributes of that kind — which is
    precisely what §3 means by calling `opaque`'s options "self-identifying". Pin each
    option and keep the kinds distinct, and (U) follows with nothing said about what the
    options contain: `onKind_set` and its two neighbours hold for *any* element codec,
    which is why the fixpoint's unique admission needs nothing from the recursive call. -/

/-- An option pinned to a kind: it admits only values and attributes of that kind. -/
def OptionSem.OnKind (o : OptionSem) (k : Kind) : Prop :=
  (∀ v, o.admitV v = true → v.kind = k) ∧ (∀ a, o.admitA a = true → a.kind = k)

/-- **(U) by kind-separation.** Pinned options with pairwise-distinct kinds can never
    both admit, on either side of the pair. -/
theorem uniqueAdmission_of_kinds {os : List OptionSem} {ks : List Kind}
    (hz : List.Forall₂ OptionSem.OnKind os ks) (hnd : ks.Nodup)
    (hw : ∀ o ∈ os, ∀ t a, o.c.e t = some a →
      o.admitV t = true ∧ o.admitA a = true) :
    UniqueAdmission os := fun o ho t a he =>
  let ⟨hv, ha⟩ := hw o ho t a he
  ⟨filter_eq_singleton_of_keys (key := Attr.kind) (hz.imp fun _ _ h => h.2) hnd o ho ha,
   filter_eq_singleton_of_keys (key := Value.kind) (hz.imp fun _ _ h => h.1) hnd o ho hv⟩

/-- An option that decides by attempting admits what it writes, on both sides — the
    read side by (R), which is the only thing `hw` above ever needs. -/
theorem byAttempt_write {c : Codec} (h : Lawful c) {t a} (he : c.e t = some a) :
    (OptionSem.byAttempt c).admitV t = true ∧ (OptionSem.byAttempt c).admitA a = true :=
  ⟨by simp [OptionSem.byAttempt, he], by simp [OptionSem.byAttempt, h.retract he]⟩

/-- §5's "the one union whose (U) is a theorem", literally: disjoint tags on stamped
    options give unique admission. `hstamp` is what object-encode of a `req literalS`
    discriminator provides — the tag on the attribute side and the same tag on the
    value side, since a literal writes its value verbatim. (An earlier statement split
    this into an encode-side and a decode-side stamp; the proof showed the value side
    of the *canonical pair* is what admission reads, and only the combined form
    supplies it without assuming (R).) -/
theorem uniqueAdmission_byTag {d : Name} {os : List (List String × Codec)}
    (hstamp : ∀ o ∈ os, ∀ t a, o.2.e t = some a →
      ∃ tag ∈ o.1, (∃ kvs, a = .m kvs ∧ kvs.lookup d = some (.s tag)) ∧
        (∃ kvs, t = .map kvs ∧ kvs.lookup d = some (.str tag)))
    (hdisj : List.Pairwise (fun x y => ∀ tag ∈ x.1, tag ∉ y.1) os) :
    UniqueAdmission (os.map fun o => .byTag d o.1 o.2) := by
  refine forall_mem_map fun x hx t a he => ?_
  replace he : x.2.e t = some a := he
  obtain ⟨tag, htag, ⟨kvsA, rfl, hlookA⟩, ⟨kvsV, rfl, hlookV⟩⟩ := hstamp x hx t a he
  have hsel := tag_filter_singleton (tag := tag) os hdisj x hx htag
  constructor
  · have hpred : (fun y : List String × Codec =>
        (OptionSem.byTag d y.1 y.2).admitA (Attr.m kvsA)) =
        (fun y : List String × Codec => y.1.contains tag) := by
      funext y
      simp only [OptionSem.byTag]
      rw [hlookA]
    simp only [filter_map_comm]
    rw [hpred, hsel]
    rfl
  · have hpred : (fun y : List String × Codec =>
        (OptionSem.byTag d y.1 y.2).admitV (Value.map kvsV)) =
        (fun y : List String × Codec => y.1.contains tag) := by
      funext y
      simp only [OptionSem.byTag]
      rw [hlookV]
    simp only [filter_map_comm]
    rw [hpred, hsel]
    rfl

/-- Every option of a `(dunion)` writes an `M` — the stamp says so, and the stamp is
    all either strength consults. -/
private theorem dunion_writes {d : Name} {os : List (List String × Codec)}
    (hstamp : ∀ o ∈ os, ∀ t a, o.2.e t = some a →
      ∃ tag ∈ o.1, (∃ kvs, a = .m kvs ∧ kvs.lookup d = some (.s tag)) ∧
        (∃ kvs, t = .map kvs ∧ kvs.lookup d = some (.str tag))) :
    ∀ m, some Member.M = some m →
      ∀ o ∈ os.map fun o => OptionSem.byTag d o.1 o.2,
        ∀ t a, o.c.e t = some a → a.member = m := by
  rintro m hm
  cases hm
  refine forall_mem_map fun x hx t a he => ?_
  replace he : x.2.e t = some a := he
  obtain ⟨tag, htag, ⟨kvs, rfl, hlook⟩, -⟩ := hstamp x hx t a he
  rfl

/-- `(dunion)` soundness is a corollary: the sum lemma composed with its (U) theorem;
    the member law comes from the stamp itself — a stamped canonical attribute is an
    `M`. -/
theorem lawful_dunionCodec {d : Name} {os : List (List String × Codec)}
    (h : ∀ o ∈ os, Lawful o.2)
    (hstamp : ∀ o ∈ os, ∀ t a, o.2.e t = some a →
      ∃ tag ∈ o.1, (∃ kvs, a = .m kvs ∧ kvs.lookup d = some (.s tag)) ∧
        (∃ kvs, t = .map kvs ∧ kvs.lookup d = some (.str tag)))
    (hdisj : List.Pairwise (fun x y => ∀ tag ∈ x.1, tag ∉ y.1) os) :
    Lawful (dunionCodec d os) :=
  lawful_altCodec (forall_mem_map h) (uniqueAdmission_byTag hstamp hdisj)
    (dunion_writes hstamp)

/-- Core `(dunion)`: the same corollary, with core options. -/
theorem lawfulCore_dunionCodec {d : Name} {os : List (List String × Codec)}
    (h : ∀ o ∈ os, LawfulCore o.2)
    (hstamp : ∀ o ∈ os, ∀ t a, o.2.e t = some a →
      ∃ tag ∈ o.1, (∃ kvs, a = .m kvs ∧ kvs.lookup d = some (.s tag)) ∧
        (∃ kvs, t = .map kvs ∧ kvs.lookup d = some (.str tag)))
    (hdisj : List.Pairwise (fun x y => ∀ tag ∈ x.1, tag ∉ y.1) os) :
    LawfulCore (dunionCodec d os) :=
  lawfulCore_altCodec (forall_mem_map h) (uniqueAdmission_byTag hstamp hdisj)
    (dunion_writes hstamp)

/-! ### `opaque`'s options, each pinned to its kind -/

theorem onKind_string : OptionSem.OnKind (.byAttempt stringCodec) .string := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, stringCodec, Value.kind, Attr.kind]

theorem onKind_boolean : OptionSem.OnKind (.byAttempt booleanCodec) .boolean := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, booleanCodec, Value.kind, Attr.kind]

theorem onKind_binary : OptionSem.OnKind (.byAttempt binaryCodec) .binary := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, binaryCodec, Value.kind, Attr.kind]

theorem onKind_null : OptionSem.OnKind (.byAttempt nullCodec) .null := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, nullCodec, Value.kind, Attr.kind]

/-- The `Numbers` policy: `lossy` offers the number option, `refuse` offers the empty
    one — which admits nothing, so the pinning holds either way. -/
theorem onKind_number (lossy : Bool) :
    OptionSem.OnKind (.byAttempt (if lossy then numberCodec else Codec.empty)) .number := by
  cases lossy <;> constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, numberCodec, Codec.empty, Value.kind, Attr.kind]

/-- A container option is pinned by its own constructor, whatever it contains. This is
    why the fixpoint's (U) needs nothing from the recursive call — and why `opaque` is
    not a special construction. -/
theorem onKind_set (c : Codec) : OptionSem.OnKind (.byAttempt (setCodec c)) .set := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, setCodec, Value.kind, Attr.kind]

theorem onKind_array (c : Codec) :
    OptionSem.OnKind (.byAttempt (arrayCodec c)) .array := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, arrayCodec, Value.kind, Attr.kind]

theorem onKind_record (c : Codec) :
    OptionSem.OnKind (.byAttempt (recordCodec c)) .map := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, recordCodec, Value.kind, Attr.kind]

/-- The kinds `opaque`'s options are pinned to, in the order they are offered. -/
def opaqKinds : List Kind :=
  [.string, .boolean, .binary, .null, .number, .set, .array, .map]

/-- "The recursive union of everything self-identifying" (§3), spelled out: the eight
    options and the eight kinds that identify them. -/
theorem opaq_onKinds (fuel : Nat) (lossy : Bool) :
    List.Forall₂ OptionSem.OnKind
      [.byAttempt stringCodec, .byAttempt booleanCodec, .byAttempt binaryCodec,
       .byAttempt nullCodec,
       .byAttempt (if lossy then numberCodec else Codec.empty),
       .byAttempt (setCodec (opaqCodec fuel lossy)),
       .byAttempt (arrayCodec (opaqCodec fuel lossy)),
       .byAttempt (recordCodec (opaqCodec fuel lossy))]
      opaqKinds :=
  .cons onKind_string (.cons onKind_boolean (.cons onKind_binary (.cons onKind_null
    (.cons (onKind_number lossy) (.cons (onKind_set _) (.cons (onKind_array _)
      (.cons (onKind_record _) .nil)))))))

/-- `opaque` closes with no bespoke induction: the sum lemma, its options' lemmas, and
    unique admission computed from the shapes — kinds partition the values, and the same
    kinds partition the attributes. -/
theorem lawful_opaqCodec : ∀ (fuel : Nat) (lossy : Bool), Lawful (opaqCodec fuel lossy)
  | 0, _ => Lawful.empty
  | fuel+1, lossy => by
    have hop : Lawful (opaqCodec fuel lossy) := lawful_opaqCodec fuel lossy
    have hnum : Lawful (if lossy then numberCodec else Codec.empty) := by
      cases lossy
      · exact Lawful.empty
      · exact lawful_numberCodec
    -- `μ` is `⊤`: the options name eight different members, so `unanimous` is `none`
    refine lawful_altCodec ?_ ?_ (fun m hm => nomatch hm)
    · intro o ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
      exacts [lawful_stringCodec, lawful_booleanCodec, lawful_binaryCodec,
        lawful_nullCodec, hnum, lawful_setCodec hop, lawful_arrayCodec hop,
        lawful_recordCodec hop, absurd h (by simp)]
    · refine uniqueAdmission_of_kinds (opaq_onKinds fuel lossy) (by decide) ?_
      intro o ho t a he
      simp only [List.mem_cons] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
      exacts [byAttempt_write lawful_stringCodec he,
        byAttempt_write lawful_booleanCodec he, byAttempt_write lawful_binaryCodec he,
        byAttempt_write lawful_nullCodec he, byAttempt_write hnum he,
        byAttempt_write (lawful_setCodec hop) he,
        byAttempt_write (lawful_arrayCodec hop) he,
        byAttempt_write (lawful_recordCodec hop) he, absurd h (by simp)]

end

end Calculus
