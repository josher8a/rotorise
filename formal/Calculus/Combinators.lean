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
* products — `arrayCodec`, `recordCodec` **proved** from the toolkit; `tupleCodec`,
  `setCodec`, `objectCodec` open;
* sums — `altCodec` over `OptionSem`s that carry their *admission as data*, with
  `UniqueAdmission` ((U) as a premise). `dunionCodec` is `altCodec` over
  tag-admission options — "the one union whose (U) is a theorem" (doc §5) is
  literally `uniqueAdmission_byTag`. `opaqCodec` is `altCodec`'s fueled fixpoint
  over everything self-identifying — its (U) is `uniqueAdmission_of_disjoint`, and
  the `refuse` policy is the absence of the number option.
-/

namespace Calculus

noncomputable section

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

/-! ## The traversal toolkit

One proof shape, proved once: a list traversed by an entrywise partial function, with
the laws lifting pointwise. `drop`'s skipping is not a traversal mode: it filters by
name first, then traverses — so every product consumes these same lemmas. -/

def traverse {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs =>
    match f x, traverse f xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

theorem traverse_length {α β : Type} {f : α → Option β} :
    ∀ (xs : List α) (ys : List β), traverse f xs = some ys → xs.length = ys.length
  | [], ys, ht => by
      replace ht : some [] = some ys := ht
      cases ht
      rfl
  | x :: xs, ys, ht => by
      simp only [traverse] at ht
      cases hfx : f x with
      | none => rw [hfx] at ht; exact nomatch ht
      | some y =>
        rw [hfx] at ht
        cases hxs : traverse f xs with
        | none => rw [hxs] at ht; exact nomatch ht
        | some ys' =>
          rw [hxs] at ht
          replace ht : some (y :: ys') = some ys := ht
          cases ht
          simp [traverse_length xs ys' hxs]

/-- Pointwise (R) lifts to the traversal. -/
theorem traverse_roundTrip {α β : Type} {f : α → Option β} {g : β → Option α}
    (h : ∀ x y, f x = some y → g y = some x) :
    ∀ (xs : List α) (ys : List β), traverse f xs = some ys → traverse g ys = some xs
  | [], ys, ht => by
      replace ht : some [] = some ys := ht
      cases ht
      rfl
  | x :: xs, ys, ht => by
      simp only [traverse] at ht
      cases hfx : f x with
      | none => rw [hfx] at ht; exact nomatch ht
      | some y =>
        rw [hfx] at ht
        cases hxs : traverse f xs with
        | none => rw [hxs] at ht; exact nomatch ht
        | some ys' =>
          rw [hxs] at ht
          replace ht : some (y :: ys') = some ys := ht
          cases ht
          simp only [traverse]
          rw [h x y hfx, traverse_roundTrip h xs ys' hxs]

/-- Pointwise (C) lifts to the traversal. -/
theorem traverse_isSome {α β γ : Type} {f : α → Option γ} {g : β → Option α}
    (h : ∀ y x, g y = some x → (f x).isSome) :
    ∀ (ys : List β) (xs : List α), traverse g ys = some xs → (traverse f xs).isSome
  | [], xs, ht => by
      replace ht : some [] = some xs := ht
      cases ht
      rfl
  | y :: ys, xs, ht => by
      simp only [traverse] at ht
      cases hgy : g y with
      | none => rw [hgy] at ht; exact nomatch ht
      | some x =>
        rw [hgy] at ht
        cases hys : traverse g ys with
        | none => rw [hys] at ht; exact nomatch ht
        | some xs' =>
          rw [hys] at ht
          replace ht : some (x :: xs') = some xs := ht
          cases ht
          obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (h y x hgy)
          obtain ⟨zs, hzs⟩ :=
            Option.isSome_iff_exists.mp (traverse_isSome h ys xs' hys)
          simp only [traverse]
          rw [hz, hzs]
          rfl

/-- A pointwise relation on the read-then-rewrite pair lifts to the zip — the shape of
    every product's (MP). -/
theorem traverse_rel {α β γ : Type} {g : β → Option α} {f : α → Option γ}
    {R : γ → β → Prop}
    (h : ∀ y x z, g y = some x → f x = some z → R z y) :
    ∀ (ys : List β) (xs : List α) (zs : List γ),
      traverse g ys = some xs → traverse f xs = some zs →
      ∀ q ∈ zs.zip ys, R q.1 q.2
  | [], xs, zs, hg, hf, q, hq => by
      replace hg : some [] = some xs := hg
      cases hg
      replace hf : some [] = some zs := hf
      cases hf
      exact absurd hq (by simp)
  | y :: ys, xs, zs, hg, hf, q, hq => by
      simp only [traverse] at hg
      cases hgy : g y with
      | none => rw [hgy] at hg; exact nomatch hg
      | some x =>
        rw [hgy] at hg
        cases hys : traverse g ys with
        | none => rw [hys] at hg; exact nomatch hg
        | some xs' =>
          rw [hys] at hg
          replace hg : some (x :: xs') = some xs := hg
          cases hg
          simp only [traverse] at hf
          cases hfx : f x with
          | none => rw [hfx] at hf; exact nomatch hf
          | some z =>
            rw [hfx] at hf
            cases hxs : traverse f xs' with
            | none => rw [hxs] at hf; exact nomatch hf
            | some zs' =>
              rw [hxs] at hf
              replace hf : some (z :: zs') = some zs := hf
              cases hf
              simp only [List.zip_cons_cons, List.mem_cons] at hq
              rcases hq with rfl | hq
              · exact h y x z hgy hfx
              · exact traverse_rel h ys xs' zs' hys hxs q hq

/-- A pointwise-related pair of keyed lists relates their lookups — what `Agree.m`
    consumes. -/
theorem lookup_rel {α β : Type} {R : α → β → Prop} :
    ∀ (l₁ : List (Name × α)) (l₂ : List (Name × β)),
      l₁.length = l₂.length →
      (∀ q ∈ l₁.zip l₂, q.1.1 = q.2.1 ∧ R q.1.2 q.2.2) →
      ∀ k a b, l₁.lookup k = some a → l₂.lookup k = some b → R a b
  | [], [], _, _, _, _, _, h1, _ => nomatch h1
  | [], _ :: _, hlen, _, _, _, _, _, _ => nomatch hlen
  | _ :: _, [], hlen, _, _, _, _, _, _ => nomatch hlen
  | (k₁, a₁) :: l₁, (k₂, b₁) :: l₂, hlen, hzip, k, a, b, h1, h2 => by
      obtain ⟨hk, hR⟩ := hzip ((k₁, a₁), (k₂, b₁)) (List.mem_cons_self _ _)
      simp only at hk
      subst hk
      simp only [List.lookup] at h1 h2
      cases hbe : (k == k₁) with
      | true =>
        rw [hbe] at h1 h2
        replace h1 : some a₁ = some a := h1
        replace h2 : some b₁ = some b := h2
        cases h1; cases h2; exact hR
      | false =>
        rw [hbe] at h1 h2
        replace h1 : l₁.lookup k = some a := h1
        replace h2 : l₂.lookup k = some b := h2
        exact lookup_rel l₁ l₂ (by simpa using hlen)
          (fun q hq => hzip q (List.mem_cons_of_mem _ hq)) k a b h1 h2

/-- Membership gives `contains`, and back. -/
theorem contains_of_mem : ∀ {l : List String} {s : String}, s ∈ l → l.contains s = true
  | a :: l, s, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · show List.elem s (s :: l) = true
        simp [List.elem]
      · show List.elem s (a :: l) = true
        simp only [List.elem]
        cases hbe : s == a with
        | true => rfl
        | false => exact contains_of_mem h'

theorem contains_eq_false_of_not_mem :
    ∀ {l : List String} {s : String}, s ∉ l → l.contains s = false
  | [], _, _ => rfl
  | a :: l, s, h => by
      show List.elem s (a :: l) = false
      simp only [List.elem]
      cases hbe : s == a with
      | true => exact absurd (List.mem_cons.mpr (Or.inl (eq_of_beq hbe))) h
      | false =>
        exact contains_eq_false_of_not_mem fun h' => h (List.mem_cons_of_mem a h')

/-- A dead pair — nothing readable, nothing writable — is lawful whatever its `μ`. -/
theorem lawful_dead {m? : Option Member} :
    Lawful { T := fun _ => False, μ := m?, e := fun _ => none, p := fun _ => none } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ h; exact nomatch h
  · intro _ _ h; exact nomatch h
  · intro _ _ _ _ h; exact nomatch h
  · intro _ _ _ h _; exact nomatch h

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

theorem filter_nil_of {α : Type} {p : α → Bool} :
    ∀ {l : List α}, (∀ y ∈ l, p y = false) → l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
      have ha := h a (List.mem_cons_self a l)
      simp only [List.filter, ha]
      exact filter_nil_of fun y hy => h y (List.mem_cons_of_mem a hy)

theorem filter_singleton_of {α : Type} {p : α → Bool} :
    ∀ {l : List α} {x : α}, l.Nodup → x ∈ l → p x = true →
      (∀ y ∈ l, y ≠ x → p y = false) → l.filter p = [x]
  | [], x, _, hx, _, _ => nomatch hx
  | a :: l, x, hnd, hx, hpx, hout => by
      have hnd' := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp hx with rfl | hx'
      · have hnil : l.filter p = [] :=
          filter_nil_of fun y hy =>
            hout y (List.mem_cons_of_mem x hy) (fun h => hnd'.1 (h ▸ hy))
        simp only [List.filter, hpx, hnil]
      · have hax : a ≠ x := fun h => hnd'.1 (h ▸ hx')
        have hpa := hout a (List.mem_cons_self a l) hax
        simp only [List.filter, hpa]
        exact filter_singleton_of hnd'.2 hx' hpx
          (fun y hy hyx => hout y (List.mem_cons_of_mem a hy) hyx)

/-! ## Products -/

/-! ### Constructors as prisms

The three wire-set payload projections are the *same function* three times, and their
lemmas were the same proof three times. What they have in common is a constructor viewed
as a partial iso onto its image — the prism §7 of the specification already names when it
calls `held` and `refine` "the same shape at different strengths".

Naming that shape once collapses the triplication: each payload projection is `traverse`
of a prism's inverse, and each of its two lemmas is an instance of one general fact. -/

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

/-- `S`'s payload. -/
def sC : Ctor String Attr where
  into := Attr.s
  out := fun a => match a with | .s v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `N`'s payload. -/
def nC : Ctor Numeral Attr where
  into := Attr.n
  out := fun a => match a with | .n v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `B`'s payload. -/
def bC : Ctor Bytes Attr where
  into := Attr.b
  out := fun a => match a with | .b v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

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

def arrayCodec (c : Codec) : Codec :=
  { T := fun v => match v with | .arr vs => ∀ x ∈ vs, c.T x | _ => False
    μ := some .L
    e := fun v => match v with
      | .arr vs => (traverse c.e vs).map Attr.l
      | _ => none
    p := fun a => match a with
      | .l as => (traverse c.p as).map Value.arr
      | _ => none }

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

/-- The keyed entry steps: `record` is their uniform instance, `object` their
    name-dispatched one. -/
def encPair (c : Codec) : Name × Value → Option (Name × Attr) :=
  fun kv => (c.e kv.2).map ((kv.1, ·))

def decPair (c : Codec) : Name × Attr → Option (Name × Value) :=
  fun kv => (c.p kv.2).map ((kv.1, ·))

def recordCodec (c : Codec) : Codec :=
  { T := fun v => match v with | .map kvs => ∀ kv ∈ kvs, c.T kv.2 | _ => False
    μ := some .M
    e := fun v => match v with
      | .map kvs => (traverse (encPair c) kvs).map Attr.m
      | _ => none
    p := fun a => match a with
      | .m kvs => (traverse (decPair c) kvs).map Value.map
      | _ => none }

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

/-- The dual of `traverse_mem`: every *input* of a successful traversal satisfies what
    its own success gives. -/
theorem traverse_mem_input {α β : Type} {f : α → Option β} {P : α → Prop}
    (hP : ∀ x y, f x = some y → P x) :
    ∀ {xs : List α} {ys}, traverse f xs = some ys → ∀ x ∈ xs, P x
  | [], _, _, x, hx => absurd hx (by simp)
  | x₀ :: xs, ys, h, x, hx => by
      simp only [traverse] at h
      cases hfx : f x₀ with
      | none => rw [hfx] at h; exact nomatch h
      | some y₀ =>
        rw [hfx] at h
        cases hxs : traverse f xs with
        | none => rw [hxs] at h; exact nomatch h
        | some ys' =>
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hP x y₀ hfx
          · exact traverse_mem_input hP hxs x hx'

theorem carrier_stringCodec : Carrier stringCodec := by
  refine ⟨?_, ?_⟩
  · intro v a h; cases v <;> first | exact ⟨_, rfl⟩ | exact nomatch h
  · intro a v h; cases a <;> first | (cases h; exact ⟨_, rfl⟩) | exact nomatch h

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

theorem carrier_booleanCodec : Carrier booleanCodec := by
  refine ⟨?_, ?_⟩
  · intro v a h; cases v <;> first | exact ⟨_, rfl⟩ | exact nomatch h
  · intro a v h; cases a <;> first | (cases h; exact ⟨_, rfl⟩) | exact nomatch h

theorem carrier_binaryCodec : Carrier binaryCodec := by
  refine ⟨?_, ?_⟩
  · intro v a h; cases v <;> first | exact ⟨_, rfl⟩ | exact nomatch h
  · intro a v h; cases a <;> first | (cases h; exact ⟨_, rfl⟩) | exact nomatch h

theorem carrier_nullCodec : Carrier nullCodec := by
  refine ⟨?_, ?_⟩
  · intro v a h; cases v <;> first | rfl | exact nomatch h
  · intro a v h; cases a <;> first | (cases h; rfl) | exact nomatch h

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

theorem carrier_numericCodec (q : Double → Bool) : Carrier (numericCodec q) := by
  refine ⟨?_, ?_⟩
  · intro v a h
    cases v
    case num d =>
      replace h : (if q d then some (Attr.n d.toDec) else none) = some a := h
      split at h
      next hq => exact ⟨d, hq, rfl⟩
      next => exact nomatch h
    all_goals exact nomatch h
  · intro a v h
    cases a
    case n x =>
      replace h : ((Double.ofDec x).bind
        fun d => if q d then some (Value.num d) else none) = some v := h
      cases hd : Double.ofDec x with
      | none => rw [hd] at h; exact nomatch h
      | some d =>
        rw [hd] at h
        replace h : (if q d then some (Value.num d) else none) = some v := h
        split at h
        next hq => cases h; exact ⟨d, hq, rfl⟩
        next => exact nomatch h
    all_goals exact nomatch h

theorem carrier_literalSCodec (ls : List String) : Carrier (literalSCodec ls) := by
  refine ⟨?_, ?_⟩
  · intro v a h
    cases v
    case str s =>
      replace h : (if s ∈ ls then some (Attr.s s) else none) = some a := h
      split at h
      next hm => exact ⟨s, hm, rfl⟩
      next => exact nomatch h
    all_goals exact nomatch h
  · intro a v h
    cases a
    case s s =>
      replace h : (if s ∈ ls then some (Value.str s) else none) = some v := h
      split at h
      next hm => cases h; exact ⟨s, hm, rfl⟩
      next => exact nomatch h
    all_goals exact nomatch h

theorem carrier_literalNCodec (ls : List Double) : Carrier (literalNCodec ls) := by
  refine ⟨?_, ?_⟩
  · intro v a h
    cases v
    case num d =>
      replace h : (if d ∈ ls then some (Attr.n d.toDec) else none) = some a := h
      split at h
      next hm => exact ⟨d, hm, rfl⟩
      next => exact nomatch h
    all_goals exact nomatch h
  · intro a v h
    cases a
    case n x =>
      replace h : ((Double.ofDec x).bind
        fun d => if d ∈ ls then some (Value.num d) else none) = some v := h
      cases hd : Double.ofDec x with
      | none => rw [hd] at h; exact nomatch h
      | some d =>
        rw [hd] at h
        replace h : (if d ∈ ls then some (Value.num d) else none) = some v := h
        split at h
        next hm => cases h; exact ⟨d, hm, rfl⟩
        next => exact nomatch h
    all_goals exact nomatch h

/-! ### Sums -/

/-- A sum's encode routes through an admitting option. -/
theorem altCodec_e_admits {os : List OptionSem} {μA : Option Member} {v a}
    (he : (altCodec os μA).e v = some a) :
    ∃ o ∈ os, o.admitV v = true ∧ o.c.e v = some a := by
  replace he : (match os.filter (·.admitV v) with
    | [o] => o.c.e v | _ => none) = some a := he
  cases hf : os.filter (·.admitV v) with
  | nil => rw [hf] at he; exact nomatch he
  | cons o tl =>
    cases tl with
    | cons _ _ => rw [hf] at he; exact nomatch he
    | nil =>
      rw [hf] at he
      have hom : o ∈ os.filter (·.admitV v) := by
        rw [hf]; exact List.mem_cons_self o []
      have hmem := List.mem_filter.mp hom
      exact ⟨o, hmem.1, hmem.2, he⟩

/-- A sum's decode routes through an admitting option — the mirror of
    `altCodec_e_admits`. -/
theorem altCodec_p_admits {os : List OptionSem} {μA : Option Member} {a v}
    (hp : (altCodec os μA).p a = some v) :
    ∃ o ∈ os, o.admitA a = true ∧ o.c.p a = some v := by
  replace hp : (match os.filter (·.admitA a) with
    | [o] => o.c.p a | _ => none) = some v := hp
  cases hf : os.filter (·.admitA a) with
  | nil => rw [hf] at hp; exact nomatch hp
  | cons o tl =>
    cases tl with
    | cons _ _ => rw [hf] at hp; exact nomatch hp
    | nil =>
      rw [hf] at hp
      have hom : o ∈ os.filter (·.admitA a) := by
        rw [hf]; exact List.mem_cons_self o []
      have hmem := List.mem_filter.mp hom
      exact ⟨o, hmem.1, hmem.2, hp⟩

/-! ### Wrappers -/

/-- `held`: the reading half needs the iso to cancel where `e` is defined — §3's
    `f ∘ g = id_I`, in the carrier-restricted form `Obligations` carries. -/
theorem carrier_through {c : Codec} {f g : Value → Value} (hc : Carrier c)
    (hlaw : LawfulCore c) (hfg : ∀ v, (c.e v).isSome → f (g v) = v) :
    Carrier (c.through f g) := by
  refine ⟨fun h => hc.domE h, ?_⟩
  intro a v h
  replace h : ((c.p a).map g) = some v := h
  cases hp : c.p a with
  | none => rw [hp] at h; exact nomatch h
  | some v' =>
    rw [hp] at h
    replace h : some (g v') = some v := h
    cases h
    show c.T (f (g v'))
    rw [hfg v' (hlaw.canon hp)]
    exact hc.ranP hp

theorem carrier_restrict {c : Codec} (hc : Carrier c) (q : Value → Bool) :
    Carrier (c.restrict q) := by
  refine ⟨?_, ?_⟩
  · intro v a h
    replace h : (if q v then c.e v else none) = some a := h
    split at h
    next hq => exact ⟨hc.domE h, hq⟩
    next => exact nomatch h
  · intro a v h
    replace h : ((c.p a).bind fun v' => if q v' then some v' else none) = some v := h
    cases hp : c.p a with
    | none => rw [hp] at h; exact nomatch h
    | some v' =>
      rw [hp] at h
      replace h : (if q v' then some v' else none) = some v := h
      split at h
      next hq => cases h; exact ⟨hc.ranP hp, hq⟩
      next => exact nomatch h

/-- `legacy`: the migration lands in `T` because §3's `ran(r) ⊆ dom(e)` puts it in
    `dom(e)`, and `e`'s domain is `T`. The doc writes `r : 𝔸 ⇀ T` directly; this is the
    same premise arrived at through the one the proof already needs. -/
theorem carrier_extendRead {c : Codec} {r : Attr → Option Value} (hc : Carrier c)
    (hran : ∀ a v, r a = some v → (c.e v).isSome) :
    Carrier (c.extendRead r) := by
  refine ⟨fun h => hc.domE h, ?_⟩
  intro a v h
  replace h : (match c.p a with | some v' => some v' | none => r a) = some v := h
  cases hp : c.p a with
  | some v' => rw [hp] at h; replace h : some v' = some v := h; cases h; exact hc.ranP hp
  | none =>
    rw [hp] at h
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hran a v h)
    exact hc.domE ha'

theorem carrier_orNull {c : Codec} (hc : Carrier c) : Carrier c.orNull := by
  refine ⟨?_, ?_⟩
  · intro v a h
    cases v
    case null => exact Or.inr rfl
    all_goals exact Or.inl (hc.domE h)
  · intro a v h
    cases a
    case null =>
      replace h : some Value.null = some v := h
      cases h; exact Or.inr rfl
    all_goals exact Or.inl (hc.ranP h)

/-! ### Containers -/

theorem traverse_mem {α β : Type} {f : α → Option β} {P : β → Prop}
    (hP : ∀ x y, f x = some y → P y) :
    ∀ {xs ys}, traverse f xs = some ys → ∀ y ∈ ys, P y
  | [], ys, ht => by
      replace ht : some [] = some ys := ht
      cases ht
      intro y hy
      exact absurd hy (by simp)
  | x :: xs, ys, ht => by
      simp only [traverse] at ht
      cases hfx : f x with
      | none => rw [hfx] at ht; exact nomatch ht
      | some y₀ =>
        rw [hfx] at ht
        cases hxs : traverse f xs with
        | none => rw [hxs] at ht; exact nomatch ht
        | some ys' =>
          rw [hxs] at ht
          replace ht : some (y₀ :: ys') = some ys := ht
          cases ht
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact hP x y hfx
          · exact traverse_mem hP hxs y hy'


theorem encPair_dom {c : Codec} (hc : Carrier c) :
    ∀ kv y, encPair c kv = some y → c.T kv.2 := by
  intro kv y h
  cases he : c.e kv.2 with
  | none => rw [encPair, he] at h; exact nomatch h
  | some a => exact hc.domE he

theorem decPair_ran {c : Codec} (hc : Carrier c) :
    ∀ kv y, decPair c kv = some y → c.T y.2 := by
  intro kv y h
  cases hp : c.p kv.2 with
  | none => rw [decPair, hp] at h; exact nomatch h
  | some v =>
    rw [decPair, hp] at h
    replace h : some (kv.1, v) = some y := h
    cases h
    exact hc.ranP hp

theorem carrier_arrayCodec {c : Codec} (hc : Carrier c) : Carrier (arrayCodec c) := by
  refine ⟨?_, ?_⟩
  · intro v a h
    cases v
    case arr vs =>
      replace h : ((traverse c.e vs).map Attr.l) = some a := h
      cases htr : traverse c.e vs with
      | none => rw [htr] at h; exact nomatch h
      | some as => exact traverse_mem_input (fun _ _ hxy => hc.domE hxy) htr
    all_goals exact nomatch h
  · intro a v h
    cases a
    case l as =>
      replace h : ((traverse c.p as).map Value.arr) = some v := h
      cases htr : traverse c.p as with
      | none => rw [htr] at h; exact nomatch h
      | some vs =>
        rw [htr] at h
        replace h : some (Value.arr vs) = some v := h
        cases h
        exact traverse_mem (fun _ _ hxy => hc.ranP hxy) htr
    all_goals exact nomatch h

theorem carrier_recordCodec {c : Codec} (hc : Carrier c) : Carrier (recordCodec c) := by
  refine ⟨?_, ?_⟩
  · intro v a h
    cases v
    case map kvs =>
      replace h : ((traverse (encPair c) kvs).map Attr.m) = some a := h
      cases htr : traverse (encPair c) kvs with
      | none => rw [htr] at h; exact nomatch h
      | some ds => exact traverse_mem_input (encPair_dom hc) htr
    all_goals exact nomatch h
  · intro a v h
    cases a
    case m kvs =>
      replace h : ((traverse (decPair c) kvs).map Value.map) = some v := h
      cases htr : traverse (decPair c) kvs with
      | none => rw [htr] at h; exact nomatch h
      | some ds =>
        rw [htr] at h
        replace h : some (Value.map ds) = some v := h
        cases h
        exact traverse_mem (decPair_ran hc) htr
    all_goals exact nomatch h

/-- `set`: nonemptiness comes from the wire, on both sides — `asWireSet` refuses the
    empty list going out, and `p` refuses an empty wire set coming in. §3's `℘⁺fin`. -/
theorem carrier_setCodec {c : Codec} (hc : Carrier c) : Carrier (setCodec c) := by
  refine ⟨?_, ?_⟩
  · intro v a h
    cases v
    case set vs =>
      replace h : ((traverse c.e vs).bind asWireSet) = some a := h
      cases htr : traverse c.e vs with
      | none => rw [htr] at h; exact nomatch h
      | some as =>
        rw [htr] at h
        refine ⟨?_, traverse_mem_input (fun _ _ hxy => hc.domE hxy) htr⟩
        intro hnil
        subst hnil
        replace htr : some [] = some as := htr
        cases htr
        exact nomatch h
    all_goals exact nomatch h
  · intro a v h
    -- three wire-set members, one argument each
    have key : ∀ {β : Type} (ws : List β) (f : β → Option Value),
        (∀ x y, f x = some y → c.T y) →
        (if ws.isEmpty then none else (traverse f ws).map Value.set) = some v →
        (setCodec c).T v := by
      intro β ws f hf hw
      cases hemp : ws.isEmpty with
      | true => rw [hemp] at hw; exact nomatch hw
      | false =>
        rw [hemp] at hw
        cases htr : traverse f ws with
        | none => rw [htr] at hw; exact nomatch hw
        | some vs =>
          rw [htr] at hw
          replace hw : some (Value.set vs) = some v := hw
          cases hw
          refine ⟨?_, traverse_mem hf htr⟩
          intro hnil
          subst hnil
          have := traverse_length ws [] htr
          cases ws with
          | nil => exact nomatch hemp
          | cons _ _ => exact nomatch this
    cases a
    case ss ws => exact key ws _ (fun _ _ hxy => hc.ranP hxy) h
    case ns ws => exact key ws _ (fun _ _ hxy => hc.ranP hxy) h
    case bs ws => exact key ws _ (fun _ _ hxy => hc.ranP hxy) h
    all_goals exact nomatch h

/-- Every codec `align` pairs with a position is one it was given. -/
theorem align_mem {α : Type} :
    ∀ {cs : List Codec} {tail : Option Codec} {xs : List α} {ps},
      align cs tail xs = some ps → ∀ p ∈ ps, p.1 ∈ cs ∨ tail = some p.1
  | [], _, [], ps, h, p, hp => by
      replace h : some [] = some ps := h
      cases h
      exact absurd hp (by simp)
  | [], tail, x :: xs, ps, h, p, hp => by
      cases htl : tail with
      | none => rw [htl] at h; exact nomatch h
      | some c =>
        rw [htl] at h
        replace h : ((align [] (some c) xs).map ((c, x) :: ·)) = some ps := h
        cases hal : align ([] : List Codec) (some c) xs with
        | none => rw [hal] at h; exact nomatch h
        | some ps' =>
          rw [hal] at h
          replace h : some ((c, x) :: ps') = some ps := h
          cases h
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact Or.inr rfl
          · rcases align_mem hal p hp' with hm | ht
            · exact Or.inl hm
            · exact Or.inr ht
  | _ :: _, _, [], _, h, _, _ => nomatch h
  | c :: cs, tail, x :: xs, ps, h, p, hp => by
      replace h : ((align cs tail xs).map ((c, x) :: ·)) = some ps := h
      cases hal : align cs tail xs with
      | none => rw [hal] at h; exact nomatch h
      | some ps' =>
        rw [hal] at h
        replace h : some ((c, x) :: ps') = some ps := h
        cases h
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact Or.inl (List.mem_cons_self _ _)
        · rcases align_mem hal p hp' with hm | ht
          · exact Or.inl (List.mem_cons_of_mem _ hm)
          · exact Or.inr ht

/-- Re-aligning a decoded tuple: what `p` produced position by position is what the
    same `align` pairs with the same codecs, and each entry is on its carrier. -/
theorem align_ranP :
    ∀ (cs : List Codec) (tail : Option Codec),
      (∀ c ∈ cs, Carrier c) → (∀ c ∈ tail, Carrier c) →
      ∀ (as : List Attr) (cas : List (Codec × Attr)) (vs : List Value),
        align cs tail as = some cas →
        traverse (fun ca => ca.1.p ca.2) cas = some vs →
        ∃ cvs, align cs tail vs = some cvs ∧ ∀ p ∈ cvs, p.1.T p.2
  | [], _, _, _, [], cas, vs, hal, htr => by
      replace hal : some [] = some cas := hal
      cases hal
      replace htr : some [] = some vs := htr
      cases htr
      exact ⟨[], rfl, fun p hp => absurd hp (by simp)⟩
  | [], tail, _, htl, a :: as, cas, vs, hal, htr => by
      cases hc : tail with
      | none => rw [hc] at hal; exact nomatch hal
      | some c =>
        rw [hc] at hal
        replace hal : ((align [] (some c) as).map ((c, a) :: ·)) = some cas := hal
        cases hal' : align ([] : List Codec) (some c) as with
        | none => rw [hal'] at hal; exact nomatch hal
        | some cas' =>
          rw [hal'] at hal
          replace hal : some ((c, a) :: cas') = some cas := hal
          cases hal
          simp only [traverse] at htr
          cases hpa : c.p a with
          | none => rw [hpa] at htr; exact nomatch htr
          | some v =>
            rw [hpa] at htr
            cases htr' : traverse (fun ca => ca.1.p ca.2) cas' with
            | none => rw [htr'] at htr; exact nomatch htr
            | some vs' =>
              rw [htr'] at htr
              replace htr : some (v :: vs') = some vs := htr
              cases htr
              have hcc : Carrier c := htl c hc
              obtain ⟨cvs', hal2, hmem⟩ :=
                align_ranP [] (some c) (by simp) (fun c' h => by
                  replace h : some c = some c' := h; cases h; exact hcc)
                  as cas' vs' hal' htr'
              refine ⟨(c, v) :: cvs', ?_, ?_⟩
              · show ((align [] (some c) vs').map ((c, v) :: ·)) = _
                rw [hal2]
                rfl
              · intro p hp
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact hcc.ranP hpa
                · exact hmem p hp'
  | _ :: _, _, _, _, [], _, _, hal, _ => nomatch hal
  | c :: cs, tail, hcs, htl, a :: as, cas, vs, hal, htr => by
      replace hal : ((align cs tail as).map ((c, a) :: ·)) = some cas := hal
      cases hal' : align cs tail as with
      | none => rw [hal'] at hal; exact nomatch hal
      | some cas' =>
        rw [hal'] at hal
        replace hal : some ((c, a) :: cas') = some cas := hal
        cases hal
        simp only [traverse] at htr
        cases hpa : c.p a with
        | none => rw [hpa] at htr; exact nomatch htr
        | some v =>
          rw [hpa] at htr
          cases htr' : traverse (fun ca => ca.1.p ca.2) cas' with
          | none => rw [htr'] at htr; exact nomatch htr
          | some vs' =>
            rw [htr'] at htr
            replace htr : some (v :: vs') = some vs := htr
            cases htr
            have hcc : Carrier c := hcs c (List.mem_cons_self _ _)
            obtain ⟨cvs', hal2, hmem⟩ :=
              align_ranP cs tail (fun c' h => hcs c' (List.mem_cons_of_mem _ h)) htl
                as cas' vs' hal' htr'
            refine ⟨(c, v) :: cvs', ?_, ?_⟩
            · show ((align cs tail vs').map ((c, v) :: ·)) = _
              rw [hal2]
              rfl
            · intro p hp
              rcases List.mem_cons.mp hp with rfl | hp'
              · exact hcc.ranP hpa
              · exact hmem p hp'

theorem carrier_tupleCodec {cs : List Codec} {tail : Option Codec}
    (hcs : ∀ c ∈ cs, Carrier c) (htl : ∀ c ∈ tail, Carrier c) :
    Carrier (tupleCodec cs tail) := by
  have carrierOf : ∀ c : Codec, (c ∈ cs ∨ tail = some c) → Carrier c := by
    intro c hm
    rcases hm with hm | ht
    · exact hcs c hm
    · exact htl c ht
  refine ⟨?_, ?_⟩
  · intro v a h
    cases v
    case arr vs =>
      replace h : ((((align cs tail vs).bind
        (traverse fun cv => cv.1.e cv.2))).map Attr.l) = some a := h
      cases hal : align cs tail vs with
      | none => rw [hal] at h; exact nomatch h
      | some ps =>
        rw [hal] at h
        replace h : ((traverse (fun cv => cv.1.e cv.2) ps).map Attr.l) = some a := h
        cases htr : traverse (fun cv => cv.1.e cv.2) ps with
        | none => rw [htr] at h; exact nomatch h
        | some as =>
          refine ⟨ps, hal, ?_⟩
          have key := traverse_mem_input
            (P := fun cv : Codec × Value => (cv.1 ∈ cs ∨ tail = some cv.1) → cv.1.T cv.2)
            (fun _ _ hxy hmem => (carrierOf _ hmem).domE hxy) htr
          exact fun p hp => key p hp (align_mem hal p hp)
    all_goals exact nomatch h
  · intro a v h
    cases a
    case l as =>
      replace h : ((((align cs tail as).bind
        (traverse fun ca => ca.1.p ca.2))).map Value.arr) = some v := h
      cases hal : align cs tail as with
      | none => rw [hal] at h; exact nomatch h
      | some cas =>
        rw [hal] at h
        replace h : ((traverse (fun ca => ca.1.p ca.2) cas).map Value.arr) = some v := h
        cases htr : traverse (fun ca => ca.1.p ca.2) cas with
        | none => rw [htr] at h; exact nomatch h
        | some vs =>
          rw [htr] at h
          replace h : some (Value.arr vs) = some v := h
          cases h
          exact align_ranP cs tail hcs htl as cas vs hal htr
    all_goals exact nomatch h

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

theorem lawful_stringCodec : Lawful stringCodec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t <;> simp_all [stringCodec] <;> subst_vars <;> rfl
  · intro a t hp
    cases a <;> simp_all [stringCodec] <;> subst_vars <;> rfl
  · intro μ hμ t a he
    cases t <;> simp_all [stringCodec, Attr.member] <;> subst_vars <;> rfl
  · intro a t a' hp he
    cases a <;> simp_all [stringCodec]
    subst_vars
    try simp_all [stringCodec]
    subst_vars
    exact .s ..

theorem lawful_booleanCodec : Lawful booleanCodec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t <;> simp_all [booleanCodec] <;> subst_vars <;> rfl
  · intro a t hp
    cases a <;> simp_all [booleanCodec] <;> subst_vars <;> rfl
  · intro μ hμ t a he
    cases t <;> simp_all [booleanCodec, Attr.member] <;> subst_vars <;> rfl
  · intro a t a' hp he
    cases a <;> simp_all [booleanCodec]
    subst_vars
    try simp_all [booleanCodec]
    subst_vars
    exact .bool ..

theorem lawful_binaryCodec : Lawful binaryCodec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t <;> simp_all [binaryCodec] <;> subst_vars <;> rfl
  · intro a t hp
    cases a <;> simp_all [binaryCodec] <;> subst_vars <;> rfl
  · intro μ hμ t a he
    cases t <;> simp_all [binaryCodec, Attr.member] <;> subst_vars <;> rfl
  · intro a t a' hp he
    cases a <;> simp_all [binaryCodec]
    subst_vars
    try simp_all [binaryCodec]
    subst_vars
    exact .b ..

theorem lawful_nullCodec : Lawful nullCodec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t <;> simp_all [nullCodec] <;> subst_vars <;> rfl
  · intro a t hp
    cases a <;> simp_all [nullCodec] <;> subst_vars <;> rfl
  · intro μ hμ t a he
    cases t <;> simp_all [nullCodec, Attr.member] <;> subst_vars <;> rfl
  · intro a t a' hp he
    cases a <;> simp_all [nullCodec]
    subst_vars
    try simp_all [nullCodec]
    subst_vars
    exact .null

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
    cases t <;> simp_all [numberCodec] <;> subst_vars <;>
      simp [numberCodec, Double.roundtrip]
  · intro a t hp
    cases a <;> simp_all [numberCodec]
    rename_i x
    cases hx : Double.ofDec x <;> rw [hx] at hp <;> simp_all [numberCodec] <;>
      subst_vars <;> rfl
  · intro μ hμ t a he
    cases t <;> simp_all [numberCodec, Attr.member] <;> subst_vars <;> rfl
  · intro a t a' hp he
    cases a <;> simp_all [numberCodec]
    rename_i x
    cases hx : Double.ofDec x <;> rw [hx] at hp <;> simp_all [numberCodec]
    subst_vars
    try simp_all [numberCodec]
    subst_vars
    exact .n ..

theorem lawful_literalSCodec (ls : List String) : Lawful (literalSCodec ls) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t <;> simp_all [literalSCodec]
    obtain ⟨hin, rfl⟩ := he
    simp [hin]
  · intro a t hp
    cases a <;> simp_all [literalSCodec]
    obtain ⟨hin, rfl⟩ := hp
    simp [hin]
  · intro μ hμ t a he
    cases t <;> simp_all [literalSCodec, Attr.member]
    obtain ⟨-, rfl⟩ := he
    subst_vars
    rfl
  · intro a t a' hp he
    cases a <;> simp_all [literalSCodec]
    obtain ⟨hin, rfl⟩ := hp
    simp [literalSCodec, hin] at he
    subst_vars
    exact .s ..

theorem lawful_numericCodec (q : Double → Bool) : Lawful (numericCodec q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t <;> simp_all [numericCodec]
    obtain ⟨hq, rfl⟩ := he
    simp [Double.roundtrip, hq]
  · intro a t hp
    cases a <;> simp_all [numericCodec]
    rename_i x
    cases hx : Double.ofDec x <;> rw [hx] at hp <;> simp_all [numericCodec]
    obtain ⟨hq, rfl⟩ := hp
    simp [hq]
  · intro μ hμ t a he
    cases t <;> simp_all [numericCodec, Attr.member]
    obtain ⟨-, rfl⟩ := he
    subst_vars
    rfl
  · intro a t a' hp he
    cases a <;> simp_all [numericCodec]
    rename_i x
    cases hx : Double.ofDec x <;> rw [hx] at hp <;> simp_all [numericCodec]
    obtain ⟨hq, rfl⟩ := hp
    simp [numericCodec, hq] at he
    subst_vars
    exact .n ..

theorem lawful_literalNCodec (ls : List Double) : Lawful (literalNCodec ls) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t <;> simp_all [literalNCodec]
    obtain ⟨hin, rfl⟩ := he
    simp [Double.roundtrip, hin]
  · intro a t hp
    cases a <;> simp_all [literalNCodec]
    rename_i x
    cases hx : Double.ofDec x <;> rw [hx] at hp <;> simp_all [literalNCodec]
    obtain ⟨hin, rfl⟩ := hp
    simp [hin]
  · intro μ hμ t a he
    cases t <;> simp_all [literalNCodec, Attr.member]
    obtain ⟨-, rfl⟩ := he
    subst_vars
    rfl
  · intro a t a' hp he
    cases a <;> simp_all [literalNCodec]
    rename_i x
    cases hx : Double.ofDec x <;> rw [hx] at hp <;> simp_all [literalNCodec]
    obtain ⟨hin, rfl⟩ := hp
    simp [literalNCodec, hin] at he
    subst_vars
    exact .n ..

/-- `held` keeps the core laws: the iso cancels on both paths. The cancellation is
    asked only on the carriers — `g ∘ f = id` where `f` lands writable, `f ∘ g = id`
    on the writable values themselves — which is the doc's `T ≃ I`, not an iso of all
    of `Value`. -/
theorem LawfulCore.through {c : Codec} (h : LawfulCore c) {f g : Value → Value}
    (hgf : ∀ v, (c.e (f v)).isSome → g (f v) = v)
    (hfg : ∀ v, (c.e v).isSome → f (g v) = v) :
    LawfulCore (c.through f g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t a he
    replace he : c.e (f t) = some a := he
    show (c.p a).map g = some t
    rw [h.retract he]
    show some (g (f t)) = some t
    rw [hgf t (by rw [he]; rfl)]
  · intro a t hp
    simp only [Codec.through] at hp
    cases hpc : c.p a with
    | none => rw [hpc] at hp; simp at hp
    | some v =>
      rw [hpc] at hp
      simp at hp
      subst hp
      show (c.e (f (g v))).isSome
      rw [hfg v (h.canon hpc)]
      exact h.canon hpc
  · intro μ hμ t a he
    exact h.writes hμ he

/-- `held` preserves the full laws: the core lemma, plus `≼` through the iso. -/
theorem Lawful.through {c : Codec} (h : Lawful c) {f g : Value → Value}
    (hgf : ∀ v, (c.e (f v)).isSome → g (f v) = v)
    (hfg : ∀ v, (c.e v).isSome → f (g v) = v) :
    Lawful (c.through f g) := by
  have core := LawfulCore.through h.core hgf hfg
  refine ⟨core.retract, core.canon, core.writes, ?_⟩
  intro a t a' hp he
  simp only [Codec.through] at hp he
  cases hpc : c.p a with
  | none => rw [hpc] at hp; simp at hp
  | some v =>
    rw [hpc] at hp
    simp at hp
    subst hp
    rw [hfg v (h.canon hpc)] at he
    exact h.agree hpc he

/-- `refine` preserves the laws: everything restricts. -/
theorem LawfulCore.restrict {c : Codec} (h : LawfulCore c) (q : Value → Bool) :
    LawfulCore (c.restrict q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t a he
    simp only [Codec.restrict] at he ⊢
    split at he
    · rw [h.retract he]
      simp [*]
    · exact nomatch he
  · intro a t hp
    simp only [Codec.restrict] at hp ⊢
    cases hpc : c.p a with
    | none => rw [hpc] at hp; simp at hp
    | some v =>
      rw [hpc] at hp
      replace hp : (if q v then some v else none) = some t := hp
      split at hp
      · cases hp
        rename_i hq
        rw [if_pos hq]
        exact h.canon hpc
      · exact nomatch hp
  · intro μ hμ t a he
    simp only [Codec.restrict] at he
    split at he
    · exact h.writes hμ he
    · exact nomatch he

theorem Lawful.restrict {c : Codec} (h : Lawful c) (q : Value → Bool) :
    Lawful (c.restrict q) := by
  have core := LawfulCore.restrict h.core q
  refine ⟨core.retract, core.canon, core.writes, ?_⟩
  intro a t a' hp he
  simp only [Codec.restrict] at hp he
  cases hpc : c.p a with
  | none => rw [hpc] at hp; simp at hp
  | some v =>
    rw [hpc] at hp
    replace hp : (if q v then some v else none) = some t := hp
    split at hp
    · cases hp
      rename_i hq
      rw [if_pos hq] at he
      exact h.agree hpc he
    · exact nomatch hp

/-- `legacy` keeps the core laws. `ran(r) ⊆ dom(e)` is (C)'s premise; (MP) is the
    sanctioned breach and has no lemma here, by design. -/
theorem LawfulCore.extendRead {c : Codec} (h : LawfulCore c) {r : Attr → Option Value}
    (hran : ∀ a v, r a = some v → (c.e v).isSome) :
    LawfulCore (c.extendRead r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t a he
    show (match c.p a with | some v => some v | none => r a) = some t
    rw [h.retract he]
  · intro a t hp
    simp only [Codec.extendRead] at hp
    cases hpc : c.p a with
    | some v =>
      rw [hpc] at hp
      cases hp
      exact h.canon hpc
    | none =>
      rw [hpc] at hp
      exact hran a t hp
  · intro μ hμ t a he
    exact h.writes hμ he

/-- `nullable` keeps the core laws under null-honesty. Structurally this is the sum
    `alt [c, null-point]`; the honesty premises are its (U), specialised. -/
theorem LawfulCore.orNull {c : Codec} (h : LawfulCore c)
    (hw : ∀ v a, c.e v = some a → a = .null → v = .null)
    (hr : ∀ a v, c.p a = some v → v = .null → a = .null) :
    LawfulCore c.orNull := by
  refine ⟨?_, ?_, ?_⟩
  · intro t a he
    cases t <;>
      first
        | (cases he; rfl)
        | (cases a <;>
            first
              | exact h.retract he
              | exact nomatch (hw _ _ he rfl))
  · intro a t hp
    cases a <;>
      first
        | (cases hp; rfl)
        | (cases t <;>
            first
              | exact nomatch (hr _ _ hp rfl)
              | exact h.canon hp)
  · intro μ hμ t a he
    exact nomatch hμ

/-- `nullable` preserves the full laws: the core lemma, plus `≼` — read-honesty is
    what keeps a non-`NULL` attribute from re-encoding as `⟨NULL, ∗⟩`. -/
theorem Lawful.orNull {c : Codec} (h : Lawful c)
    (hw : ∀ v a, c.e v = some a → a = .null → v = .null)
    (hr : ∀ a v, c.p a = some v → v = .null → a = .null) :
    Lawful c.orNull := by
  have core := LawfulCore.orNull h.core hw hr
  refine ⟨core.retract, core.canon, core.writes, ?_⟩
  intro a t a' hp he
  cases a <;>
    first
      | (cases hp; cases he; exact .null)
      | (cases t <;>
          first
            | exact nomatch (hr _ _ hp rfl)
            | exact h.agree hp he)

/-- `array` keeps the core laws: the toolkit, verbatim. -/
theorem lawfulCore_arrayCodec {c : Codec} (h : LawfulCore c) :
    LawfulCore (arrayCodec c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t a he
    cases t
    case arr vs =>
      replace he : (traverse c.e vs).map Attr.l = some a := he
      cases hvs : traverse c.e vs with
      | none => rw [hvs] at he; exact nomatch he
      | some as =>
        rw [hvs] at he
        replace he : some (Attr.l as) = some a := he
        cases he
        show (traverse c.p as).map Value.arr = some (.arr vs)
        rw [traverse_roundTrip (fun _ _ hxy => h.retract hxy) vs as hvs]
        rfl
    all_goals exact nomatch he
  · intro a t hp
    cases a
    case l as =>
      replace hp : (traverse c.p as).map Value.arr = some t := hp
      cases has : traverse c.p as with
      | none => rw [has] at hp; exact nomatch hp
      | some vs =>
        rw [has] at hp
        replace hp : some (Value.arr vs) = some t := hp
        cases hp
        show ((traverse c.e vs).map Attr.l).isSome
        obtain ⟨as', has'⟩ := Option.isSome_iff_exists.mp
          (traverse_isSome (fun _ _ hyx => h.canon hyx) as vs has)
        rw [has']
        rfl
    all_goals exact nomatch hp
  · intro μ hμ t a he
    replace hμ : some Member.L = some μ := hμ
    cases hμ
    cases t
    case arr vs =>
      replace he : (traverse c.e vs).map Attr.l = some a := he
      cases hvs : traverse c.e vs with
      | none => rw [hvs] at he; exact nomatch he
      | some as =>
        rw [hvs] at he
        replace he : some (Attr.l as) = some a := he
        cases he
        rfl
    all_goals exact nomatch he

/-- `array` preserves the full laws: the core lemma, plus `≼` pointwise. -/
theorem lawful_arrayCodec {c : Codec} (h : Lawful c) : Lawful (arrayCodec c) := by
  have core := lawfulCore_arrayCodec h.core
  refine ⟨core.retract, core.canon, core.writes, ?_⟩
  intro a t a' hp he
  cases a
  case l as =>
    replace hp : (traverse c.p as).map Value.arr = some t := hp
    cases has : traverse c.p as with
    | none => rw [has] at hp; exact nomatch hp
    | some vs =>
      rw [has] at hp
      replace hp : some (Value.arr vs) = some t := hp
      cases hp
      replace he : (traverse c.e vs).map Attr.l = some a' := he
      cases hvs : traverse c.e vs with
      | none => rw [hvs] at he; exact nomatch he
      | some as' =>
        rw [hvs] at he
        replace he : some (Attr.l as') = some a' := he
        cases he
        exact .l as' as
          (traverse_rel (R := Agree) (fun _ _ _ hg hf => h.agree hg hf)
            as vs as' has hvs)
  all_goals exact nomatch hp

/-- `record` keeps the core laws: the toolkit over the keyed steps. -/
theorem lawfulCore_recordCodec {c : Codec} (h : LawfulCore c) :
    LawfulCore (recordCodec c) := by
  have hrt : ∀ kv ka, encPair c kv = some ka → decPair c ka = some kv := by
    intro ⟨k, v⟩ ka hkv
    simp only [encPair] at hkv
    cases hev : c.e v with
    | none => rw [hev] at hkv; exact nomatch hkv
    | some a₀ =>
      rw [hev] at hkv
      replace hkv : some (k, a₀) = some ka := hkv
      cases hkv
      show (c.p a₀).map _ = _
      rw [h.retract hev]
      rfl
  have hcn : ∀ ka kv, decPair c ka = some kv → (encPair c kv).isSome := by
    intro ⟨k, a⟩ kv hka
    simp only [decPair] at hka
    cases hpa : c.p a with
    | none => rw [hpa] at hka; exact nomatch hka
    | some v₀ =>
      rw [hpa] at hka
      replace hka : some (k, v₀) = some kv := hka
      cases hka
      show ((c.e v₀).map _).isSome
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (h.canon hpa)
      rw [ha']
      rfl
  refine ⟨?_, ?_, ?_⟩
  · intro t a he
    cases t
    case map kvs =>
      replace he : (traverse (encPair c) kvs).map Attr.m = some a := he
      cases hkvs : traverse (encPair c) kvs with
      | none => rw [hkvs] at he; exact nomatch he
      | some ds =>
        rw [hkvs] at he
        replace he : some (Attr.m ds) = some a := he
        cases he
        show (traverse (decPair c) ds).map Value.map = some (.map kvs)
        rw [traverse_roundTrip hrt kvs ds hkvs]
        rfl
    all_goals exact nomatch he
  · intro a t hp
    cases a
    case m ds =>
      replace hp : (traverse (decPair c) ds).map Value.map = some t := hp
      cases hds : traverse (decPair c) ds with
      | none => rw [hds] at hp; exact nomatch hp
      | some kvs =>
        rw [hds] at hp
        replace hp : some (Value.map kvs) = some t := hp
        cases hp
        show ((traverse (encPair c) kvs).map Attr.m).isSome
        obtain ⟨ds', hds'⟩ := Option.isSome_iff_exists.mp
          (traverse_isSome hcn ds kvs hds)
        rw [hds']
        rfl
    all_goals exact nomatch hp
  · intro μ hμ t a he
    replace hμ : some Member.M = some μ := hμ
    cases hμ
    cases t
    case map kvs =>
      replace he : (traverse (encPair c) kvs).map Attr.m = some a := he
      cases hkvs : traverse (encPair c) kvs with
      | none => rw [hkvs] at he; exact nomatch he
      | some ds =>
        rw [hkvs] at he
        replace he : some (Attr.m ds) = some a := he
        cases he
        rfl
    all_goals exact nomatch he

/-- `record` preserves the full laws: the core lemma, plus the keyed `≼` clause. -/
theorem lawful_recordCodec {c : Codec} (h : Lawful c) : Lawful (recordCodec c) := by
  have hag : ∀ ka kv ka', decPair c ka = some kv → encPair c kv = some ka' →
      ka'.1 = ka.1 ∧ Agree ka'.2 ka.2 := by
    intro ⟨k, a⟩ kv ka' hka hkv
    simp only [decPair] at hka
    cases hpa : c.p a with
    | none => rw [hpa] at hka; exact nomatch hka
    | some v₀ =>
      rw [hpa] at hka
      replace hka : some (k, v₀) = some kv := hka
      cases hka
      simp only [encPair] at hkv
      cases hev : c.e v₀ with
      | none => rw [hev] at hkv; exact nomatch hkv
      | some a₀ =>
        rw [hev] at hkv
        replace hkv : some (k, a₀) = some ka' := hkv
        cases hkv
        exact ⟨rfl, h.agree hpa hev⟩
  have core := lawfulCore_recordCodec h.core
  refine ⟨core.retract, core.canon, core.writes, ?_⟩
  intro a t a' hp he
  cases a
  case m ds =>
    replace hp : (traverse (decPair c) ds).map Value.map = some t := hp
    cases hds : traverse (decPair c) ds with
    | none => rw [hds] at hp; exact nomatch hp
    | some kvs =>
      rw [hds] at hp
      replace hp : some (Value.map kvs) = some t := hp
      cases hp
      replace he : (traverse (encPair c) kvs).map Attr.m = some a' := he
      cases hkvs : traverse (encPair c) kvs with
      | none => rw [hkvs] at he; exact nomatch he
      | some ds' =>
        rw [hkvs] at he
        replace he : some (Attr.m ds') = some a' := he
        cases he
        refine .m ds' ds ?_
        have hzip := traverse_rel hag ds kvs ds' hds hkvs
        have hlen : ds'.length = ds.length := by
          rw [← traverse_length kvs ds' hkvs, traverse_length ds kvs hds]
        exact lookup_rel ds' ds hlen (fun q hq => hzip q hq)
  all_goals exact nomatch hp

/-! ## Lawfulness — the open frontier (README roadmap) -/

/-! ### Payload facts for the quotiented product -/

theorem ne_nil_of_isEmpty_false {α : Type} {l : List α} (h : l.isEmpty = false) :
    l ≠ [] := by
  cases l with
  | nil => exact nomatch h
  | cons _ _ => exact fun h' => nomatch h'

theorem traverse_map {α β γ : Type} {g : α → β} {f : β → Option γ} :
    ∀ l : List α, traverse f (l.map g) = traverse (fun x => f (g x)) l
  | [] => rfl
  | x :: l => by
      simp only [List.map, traverse]
      rw [traverse_map l]

theorem mem_zip_left {α β : Type} :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
      ∀ x, x ∈ l₁ → ∃ y, (x, y) ∈ l₁.zip l₂
  | [], _, _, _, hx => nomatch hx
  | _ :: _, [], hlen, _, _ => nomatch hlen
  | a :: l₁, b :: l₂, hlen, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨b, List.mem_cons_self _ _⟩
      · obtain ⟨y, hy⟩ := mem_zip_left l₁ l₂ (by simpa using hlen) x hx'
        exact ⟨y, List.mem_cons_of_mem _ hy⟩

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

/-- The quotiented product; `p` need not be injective — the shrink is the quotient. -/
theorem lawful_setCodec {c : Codec} (h : Lawful c) : Lawful (setCodec c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t
    case set vs =>
      replace he : (traverse c.e vs).bind asWireSet = some a := he
      cases htr : traverse c.e vs with
      | none => rw [htr] at he; exact nomatch he
      | some as =>
        rw [htr] at he
        replace he : asWireSet as = some a := he
        obtain ⟨hne, hcase⟩ := asWireSet_cases he
        rcases hcase with ⟨ss, rfl, rfl⟩ | ⟨ns, rfl, rfl⟩ | ⟨bs, rfl, rfl⟩
        · have h1 := traverse_roundTrip (fun _ _ hxy => h.retract hxy)
            vs (ss.map Attr.s) htr
          rw [traverse_map] at h1
          cases ss with
          | nil => exact absurd rfl hne
          | cons s ss' =>
            show (traverse (fun s => c.p (.s s)) (s :: ss')).map Value.set =
              some (.set vs)
            rw [h1]
            rfl
        · have h1 := traverse_roundTrip (fun _ _ hxy => h.retract hxy)
            vs (ns.map Attr.n) htr
          rw [traverse_map] at h1
          cases ns with
          | nil => exact absurd rfl hne
          | cons n ns' =>
            show (traverse (fun x => c.p (.n x)) (n :: ns')).map Value.set =
              some (.set vs)
            rw [h1]
            rfl
        · have h1 := traverse_roundTrip (fun _ _ hxy => h.retract hxy)
            vs (bs.map Attr.b) htr
          rw [traverse_map] at h1
          cases bs with
          | nil => exact absurd rfl hne
          | cons b bs' =>
            show (traverse (fun x => c.p (.b x)) (b :: bs')).map Value.set =
              some (.set vs)
            rw [h1]
            rfl
    all_goals exact nomatch he
  · intro a t hp
    cases a
    case ss vs' =>
      cases vs' with
      | nil => exact nomatch hp
      | cons s rest =>
        replace hp : (traverse (fun s => c.p (.s s)) (s :: rest)).map Value.set =
          some t := hp
        cases htr : traverse (fun s => c.p (Attr.s s)) (s :: rest) with
        | none => rw [htr] at hp; exact nomatch hp
        | some ws =>
          rw [htr] at hp
          replace hp : some (Value.set ws) = some t := hp
          cases hp
          obtain ⟨as', has'⟩ := Option.isSome_iff_exists.mp
            (traverse_isSome (f := c.e) (fun _ _ hyx => h.canon hyx)
              (s :: rest) ws htr)
          have hmem : ∀ x ∈ as', x.member = Member.S := by
            have hz := traverse_rel (g := fun s => c.p (Attr.s s)) (f := c.e)
              (R := fun z _ => z.member = Member.S)
              (fun _ _ _ hg hf => (h.agree hg hf).member_eq)
              (s :: rest) ws as' htr has'
            intro x hx
            have hlen1 := traverse_length (s :: rest) ws htr
            have hlen2 := traverse_length ws as' has'
            obtain ⟨y, hy⟩ := mem_zip_left as' (s :: rest) (by omega) x hx
            exact hz (x, y) hy
          have hne' : as' ≠ [] := by
            intro h0
            have hlen1 := traverse_length (s :: rest) ws htr
            have hlen2 := traverse_length ws as' has'
            rw [h0] at hlen2
            simp only [List.length_cons, List.length_nil] at hlen1 hlen2
            omega
          obtain ⟨ss', hss'⟩ := strPayloads_isSome hmem
          show ((traverse c.e ws).bind asWireSet).isSome
          rw [has']
          show (asWireSet as').isSome
          cases as' with
          | nil => exact absurd rfl hne'
          | cons x r =>
            simp only [asWireSet]
            rw [hss']
            rfl
    case ns vs' =>
      cases vs' with
      | nil => exact nomatch hp
      | cons n rest =>
        replace hp : (traverse (fun x => c.p (.n x)) (n :: rest)).map Value.set =
          some t := hp
        cases htr : traverse (fun x => c.p (Attr.n x)) (n :: rest) with
        | none => rw [htr] at hp; exact nomatch hp
        | some ws =>
          rw [htr] at hp
          replace hp : some (Value.set ws) = some t := hp
          cases hp
          obtain ⟨as', has'⟩ := Option.isSome_iff_exists.mp
            (traverse_isSome (f := c.e) (fun _ _ hyx => h.canon hyx)
              (n :: rest) ws htr)
          have hmem : ∀ x ∈ as', x.member = Member.N := by
            have hz := traverse_rel (g := fun x => c.p (Attr.n x)) (f := c.e)
              (R := fun z _ => z.member = Member.N)
              (fun _ _ _ hg hf => (h.agree hg hf).member_eq)
              (n :: rest) ws as' htr has'
            intro x hx
            have hlen1 := traverse_length (n :: rest) ws htr
            have hlen2 := traverse_length ws as' has'
            obtain ⟨y, hy⟩ := mem_zip_left as' (n :: rest) (by omega) x hx
            exact hz (x, y) hy
          have hne' : as' ≠ [] := by
            intro h0
            have hlen1 := traverse_length (n :: rest) ws htr
            have hlen2 := traverse_length ws as' has'
            rw [h0] at hlen2
            simp only [List.length_cons, List.length_nil] at hlen1 hlen2
            omega
          obtain ⟨ns', hns'⟩ := numPayloads_isSome hmem
          show ((traverse c.e ws).bind asWireSet).isSome
          rw [has']
          show (asWireSet as').isSome
          cases as' with
          | nil => exact absurd rfl hne'
          | cons x r =>
            have hx := hmem x (List.mem_cons_self x r)
            cases x
            case n v =>
              simp only [asWireSet, strPayloads]
              rw [hns']
              rfl
            all_goals exact nomatch hx
    case bs vs' =>
      cases vs' with
      | nil => exact nomatch hp
      | cons b rest =>
        replace hp : (traverse (fun x => c.p (.b x)) (b :: rest)).map Value.set =
          some t := hp
        cases htr : traverse (fun x => c.p (Attr.b x)) (b :: rest) with
        | none => rw [htr] at hp; exact nomatch hp
        | some ws =>
          rw [htr] at hp
          replace hp : some (Value.set ws) = some t := hp
          cases hp
          obtain ⟨as', has'⟩ := Option.isSome_iff_exists.mp
            (traverse_isSome (f := c.e) (fun _ _ hyx => h.canon hyx)
              (b :: rest) ws htr)
          have hmem : ∀ x ∈ as', x.member = Member.B := by
            have hz := traverse_rel (g := fun x => c.p (Attr.b x)) (f := c.e)
              (R := fun z _ => z.member = Member.B)
              (fun _ _ _ hg hf => (h.agree hg hf).member_eq)
              (b :: rest) ws as' htr has'
            intro x hx
            have hlen1 := traverse_length (b :: rest) ws htr
            have hlen2 := traverse_length ws as' has'
            obtain ⟨y, hy⟩ := mem_zip_left as' (b :: rest) (by omega) x hx
            exact hz (x, y) hy
          have hne' : as' ≠ [] := by
            intro h0
            have hlen1 := traverse_length (b :: rest) ws htr
            have hlen2 := traverse_length ws as' has'
            rw [h0] at hlen2
            simp only [List.length_cons, List.length_nil] at hlen1 hlen2
            omega
          obtain ⟨bs', hbs'⟩ := binPayloads_isSome hmem
          show ((traverse c.e ws).bind asWireSet).isSome
          rw [has']
          show (asWireSet as').isSome
          cases as' with
          | nil => exact absurd rfl hne'
          | cons x r =>
            have hx := hmem x (List.mem_cons_self x r)
            cases x
            case b v =>
              simp only [asWireSet, strPayloads, numPayloads]
              rw [hbs']
              rfl
            all_goals exact nomatch hx
    all_goals exact nomatch hp
  · intro μ hμ t a he
    simp only [setCodec] at hμ
    cases hc : c.μ with
    | none => rw [hc] at hμ; exact nomatch hμ
    | some μ₀ =>
      rw [hc] at hμ
      cases t
      case set vs =>
        replace he : (traverse c.e vs).bind asWireSet = some a := he
        cases htr : traverse c.e vs with
        | none => rw [htr] at he; exact nomatch he
        | some as =>
          rw [htr] at he
          replace he : asWireSet as = some a := he
          obtain ⟨hne, hcase⟩ := asWireSet_cases he
          have hmem := traverse_mem (P := fun y => y.member = μ₀)
            (fun _ y hxy => h.writes hc hxy) htr
          rcases hcase with ⟨ss, rfl, rfl⟩ | ⟨ns, rfl, rfl⟩ | ⟨bs, rfl, rfl⟩
          · cases ss with
            | nil => exact absurd rfl hne
            | cons s ss' =>
              have hm := hmem (Attr.s s) (List.mem_cons_self _ _)
              replace hm : Member.S = μ₀ := hm
              cases hm
              replace hμ : some Member.SS = some μ := hμ
              cases hμ
              rfl
          · cases ns with
            | nil => exact absurd rfl hne
            | cons n ns' =>
              have hm := hmem (Attr.n n) (List.mem_cons_self _ _)
              replace hm : Member.N = μ₀ := hm
              cases hm
              replace hμ : some Member.NS = some μ := hμ
              cases hμ
              rfl
          · cases bs with
            | nil => exact absurd rfl hne
            | cons b bs' =>
              have hm := hmem (Attr.b b) (List.mem_cons_self _ _)
              replace hm : Member.B = μ₀ := hm
              cases hm
              replace hμ : some Member.BS = some μ := hμ
              cases hμ
              rfl
      all_goals exact nomatch he
  · intro a t a' hp he
    cases a
    case ss vs' =>
      cases vs' with
      | nil => exact nomatch hp
      | cons s rest =>
        replace hp : (traverse (fun s => c.p (.s s)) (s :: rest)).map Value.set =
          some t := hp
        cases htr : traverse (fun s => c.p (Attr.s s)) (s :: rest) with
        | none => rw [htr] at hp; exact nomatch hp
        | some ws =>
          rw [htr] at hp
          replace hp : some (Value.set ws) = some t := hp
          cases hp
          replace he : (traverse c.e ws).bind asWireSet = some a' := he
          cases has' : traverse c.e ws with
          | none => rw [has'] at he; exact nomatch he
          | some as' =>
            rw [has'] at he
            replace he : asWireSet as' = some a' := he
            have hmem : ∀ x ∈ as', x.member = Member.S := by
              have hz := traverse_rel (g := fun s => c.p (Attr.s s)) (f := c.e)
                (R := fun z _ => z.member = Member.S)
                (fun _ _ _ hg hf => (h.agree hg hf).member_eq)
                (s :: rest) ws as' htr has'
              intro x hx
              have hlen1 := traverse_length (s :: rest) ws htr
              have hlen2 := traverse_length ws as' has'
              obtain ⟨y, hy⟩ := mem_zip_left as' (s :: rest) (by omega) x hx
              exact hz (x, y) hy
            obtain ⟨hne', hcase⟩ := asWireSet_cases he
            rcases hcase with ⟨ss', rfl, rfl⟩ | ⟨ns', heq, rfl⟩ | ⟨bs', heq, rfl⟩
            · exact .ss ..
            · cases ns' with
              | nil => exact absurd heq hne'
              | cons n r =>
                have := hmem (Attr.n n) (by rw [heq]; exact List.mem_cons_self _ _)
                exact nomatch this
            · cases bs' with
              | nil => exact absurd heq hne'
              | cons b r =>
                have := hmem (Attr.b b) (by rw [heq]; exact List.mem_cons_self _ _)
                exact nomatch this
    case ns vs' =>
      cases vs' with
      | nil => exact nomatch hp
      | cons n rest =>
        replace hp : (traverse (fun x => c.p (.n x)) (n :: rest)).map Value.set =
          some t := hp
        cases htr : traverse (fun x => c.p (Attr.n x)) (n :: rest) with
        | none => rw [htr] at hp; exact nomatch hp
        | some ws =>
          rw [htr] at hp
          replace hp : some (Value.set ws) = some t := hp
          cases hp
          replace he : (traverse c.e ws).bind asWireSet = some a' := he
          cases has' : traverse c.e ws with
          | none => rw [has'] at he; exact nomatch he
          | some as' =>
            rw [has'] at he
            replace he : asWireSet as' = some a' := he
            have hmem : ∀ x ∈ as', x.member = Member.N := by
              have hz := traverse_rel (g := fun x => c.p (Attr.n x)) (f := c.e)
                (R := fun z _ => z.member = Member.N)
                (fun _ _ _ hg hf => (h.agree hg hf).member_eq)
                (n :: rest) ws as' htr has'
              intro x hx
              have hlen1 := traverse_length (n :: rest) ws htr
              have hlen2 := traverse_length ws as' has'
              obtain ⟨y, hy⟩ := mem_zip_left as' (n :: rest) (by omega) x hx
              exact hz (x, y) hy
            obtain ⟨hne', hcase⟩ := asWireSet_cases he
            rcases hcase with ⟨ss', heq, rfl⟩ | ⟨ns', rfl, rfl⟩ | ⟨bs', heq, rfl⟩
            · cases ss' with
              | nil => exact absurd heq hne'
              | cons x r =>
                have := hmem (Attr.s x) (by rw [heq]; exact List.mem_cons_self _ _)
                exact nomatch this
            · exact .ns ..
            · cases bs' with
              | nil => exact absurd heq hne'
              | cons b r =>
                have := hmem (Attr.b b) (by rw [heq]; exact List.mem_cons_self _ _)
                exact nomatch this
    case bs vs' =>
      cases vs' with
      | nil => exact nomatch hp
      | cons b rest =>
        replace hp : (traverse (fun x => c.p (.b x)) (b :: rest)).map Value.set =
          some t := hp
        cases htr : traverse (fun x => c.p (Attr.b x)) (b :: rest) with
        | none => rw [htr] at hp; exact nomatch hp
        | some ws =>
          rw [htr] at hp
          replace hp : some (Value.set ws) = some t := hp
          cases hp
          replace he : (traverse c.e ws).bind asWireSet = some a' := he
          cases has' : traverse c.e ws with
          | none => rw [has'] at he; exact nomatch he
          | some as' =>
            rw [has'] at he
            replace he : asWireSet as' = some a' := he
            have hmem : ∀ x ∈ as', x.member = Member.B := by
              have hz := traverse_rel (g := fun x => c.p (Attr.b x)) (f := c.e)
                (R := fun z _ => z.member = Member.B)
                (fun _ _ _ hg hf => (h.agree hg hf).member_eq)
                (b :: rest) ws as' htr has'
              intro x hx
              have hlen1 := traverse_length (b :: rest) ws htr
              have hlen2 := traverse_length ws as' has'
              obtain ⟨y, hy⟩ := mem_zip_left as' (b :: rest) (by omega) x hx
              exact hz (x, y) hy
            obtain ⟨hne', hcase⟩ := asWireSet_cases he
            rcases hcase with ⟨ss', heq, rfl⟩ | ⟨ns', heq, rfl⟩ | ⟨bs', rfl, rfl⟩
            · cases ss' with
              | nil => exact absurd heq hne'
              | cons x r =>
                have := hmem (Attr.s x) (by rw [heq]; exact List.mem_cons_self _ _)
                exact nomatch this
            · cases ns' with
              | nil => exact absurd heq hne'
              | cons x r =>
                have := hmem (Attr.n x) (by rw [heq]; exact List.mem_cons_self _ _)
                exact nomatch this
            · exact .bs ..
    all_goals exact nomatch hp

/-- Writing a tuple then reading realigns to the same codecs, position for position. -/
theorem alignTraverse_roundTrip :
    ∀ (cs : List Codec) (tail : Option Codec),
      (∀ c ∈ cs, LawfulCore c) → (∀ c ∈ tail, LawfulCore c) →
      ∀ (vs : List Value) (cvs : List (Codec × Value)) (as : List Attr),
        align cs tail vs = some cvs →
        traverse (fun cv => cv.1.e cv.2) cvs = some as →
        (align cs tail as).bind (traverse fun ca => ca.1.p ca.2) = some vs
  | [], _, _, _, [], cvs, as, hal, htr => by
      replace hal : some [] = some cvs := hal
      cases hal
      replace htr : some [] = some as := htr
      cases htr
      rfl
  | [], tail, h, ht, v :: vs, cvs, as, hal, htr => by
      cases tail with
      | none => exact nomatch hal
      | some c =>
        replace hal : (align [] (some c) vs).map ((c, v) :: ·) = some cvs := hal
        cases hvs : align [] (some c) vs with
        | none => rw [hvs] at hal; exact nomatch hal
        | some cvs' =>
          rw [hvs] at hal
          replace hal : some ((c, v) :: cvs') = some cvs := hal
          cases hal
          simp only [traverse] at htr
          cases hev : c.e v with
          | none => rw [hev] at htr; exact nomatch htr
          | some a₀ =>
            rw [hev] at htr
            cases htr' : traverse (fun cv : Codec × Value => cv.1.e cv.2) cvs' with
            | none => rw [htr'] at htr; exact nomatch htr
            | some as' =>
              rw [htr'] at htr
              replace htr : some (a₀ :: as') = some as := htr
              cases htr
              have hc : LawfulCore c := ht c rfl
              have ih := alignTraverse_roundTrip [] (some c) h ht vs cvs' as' hvs htr'
              show ((align [] (some c) as').map ((c, a₀) :: ·)).bind
                (traverse fun ca => ca.1.p ca.2) = some (v :: vs)
              cases has : align [] (some c) as' with
              | none => rw [has] at ih; exact nomatch ih
              | some cas' =>
                rw [has] at ih
                replace ih :
                    traverse (fun ca : Codec × Attr => ca.1.p ca.2) cas' = some vs := ih
                show traverse (fun ca : Codec × Attr => ca.1.p ca.2)
                  ((c, a₀) :: cas') = some (v :: vs)
                simp only [traverse]
                rw [hc.retract hev, ih]
  | _ :: _, _, _, _, [], _, _, hal, _ => nomatch hal
  | c :: cs, tail, h, ht, v :: vs, cvs, as, hal, htr => by
      replace hal : (align cs tail vs).map ((c, v) :: ·) = some cvs := hal
      cases hvs : align cs tail vs with
      | none => rw [hvs] at hal; exact nomatch hal
      | some cvs' =>
        rw [hvs] at hal
        replace hal : some ((c, v) :: cvs') = some cvs := hal
        cases hal
        simp only [traverse] at htr
        cases hev : c.e v with
        | none => rw [hev] at htr; exact nomatch htr
        | some a₀ =>
          rw [hev] at htr
          cases htr' : traverse (fun cv : Codec × Value => cv.1.e cv.2) cvs' with
          | none => rw [htr'] at htr; exact nomatch htr
          | some as' =>
            rw [htr'] at htr
            replace htr : some (a₀ :: as') = some as := htr
            cases htr
            have hc : LawfulCore c := h c (List.mem_cons_self c cs)
            have ih := alignTraverse_roundTrip cs tail
              (fun c' hc' => h c' (List.mem_cons_of_mem c hc')) ht vs cvs' as' hvs htr'
            show ((align cs tail as').map ((c, a₀) :: ·)).bind
              (traverse fun ca => ca.1.p ca.2) = some (v :: vs)
            cases has : align cs tail as' with
            | none => rw [has] at ih; exact nomatch ih
            | some cas' =>
              rw [has] at ih
              replace ih :
                  traverse (fun ca : Codec × Attr => ca.1.p ca.2) cas' = some vs := ih
              show traverse (fun ca : Codec × Attr => ca.1.p ca.2)
                ((c, a₀) :: cas') = some (v :: vs)
              simp only [traverse]
              rw [hc.retract hev, ih]

/-- Reading a tuple then rewriting realigns, re-encodes, and member-agrees pointwise. -/
theorem alignTraverse_master :
    ∀ (cs : List Codec) (tail : Option Codec),
      (∀ c ∈ cs, Lawful c) → (∀ c ∈ tail, Lawful c) →
      ∀ (as : List Attr) (cas : List (Codec × Attr)) (vs : List Value),
        align cs tail as = some cas →
        traverse (fun ca => ca.1.p ca.2) cas = some vs →
        ∃ cvs as', align cs tail vs = some cvs ∧
          traverse (fun cv => cv.1.e cv.2) cvs = some as' ∧
          ∀ q ∈ as'.zip as, Agree q.1 q.2
  | [], _, _, _, [], cas, vs, hal, htr => by
      replace hal : some [] = some cas := hal
      cases hal
      replace htr : some [] = some vs := htr
      cases htr
      exact ⟨[], [], rfl, rfl, fun q hq => absurd hq (by simp)⟩
  | [], tail, h, ht, a :: as, cas, vs, hal, htr => by
      cases tail with
      | none => exact nomatch hal
      | some c =>
        replace hal : (align [] (some c) as).map ((c, a) :: ·) = some cas := hal
        cases has : align [] (some c) as with
        | none => rw [has] at hal; exact nomatch hal
        | some cas' =>
          rw [has] at hal
          replace hal : some ((c, a) :: cas') = some cas := hal
          cases hal
          simp only [traverse] at htr
          cases hpa : c.p a with
          | none => rw [hpa] at htr; exact nomatch htr
          | some v =>
            rw [hpa] at htr
            cases htr' : traverse (fun ca : Codec × Attr => ca.1.p ca.2) cas' with
            | none => rw [htr'] at htr; exact nomatch htr
            | some vs' =>
              rw [htr'] at htr
              replace htr : some (v :: vs') = some vs := htr
              cases htr
              have hc : Lawful c := ht c rfl
              obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp (hc.canon hpa)
              obtain ⟨cvs', as'', hal', htr'', hzip⟩ :=
                alignTraverse_master [] (some c) h ht as cas' vs' has htr'
              refine ⟨(c, v) :: cvs', a₀ :: as'', ?_, ?_, ?_⟩
              · show (align [] (some c) vs').map ((c, v) :: ·) = _
                rw [hal']
                rfl
              · simp only [traverse]
                rw [ha₀, htr'']
              · intro q hq
                simp only [List.zip_cons_cons, List.mem_cons] at hq
                rcases hq with rfl | hq
                · exact hc.agree hpa ha₀
                · exact hzip q hq
  | _ :: _, _, _, _, [], _, _, hal, _ => nomatch hal
  | c :: cs, tail, h, ht, a :: as, cas, vs, hal, htr => by
      replace hal : (align cs tail as).map ((c, a) :: ·) = some cas := hal
      cases has : align cs tail as with
      | none => rw [has] at hal; exact nomatch hal
      | some cas' =>
        rw [has] at hal
        replace hal : some ((c, a) :: cas') = some cas := hal
        cases hal
        simp only [traverse] at htr
        cases hpa : c.p a with
        | none => rw [hpa] at htr; exact nomatch htr
        | some v =>
          rw [hpa] at htr
          cases htr' : traverse (fun ca : Codec × Attr => ca.1.p ca.2) cas' with
          | none => rw [htr'] at htr; exact nomatch htr
          | some vs' =>
            rw [htr'] at htr
            replace htr : some (v :: vs') = some vs := htr
            cases htr
            have hc : Lawful c := h c (List.mem_cons_self c cs)
            obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp (hc.canon hpa)
            obtain ⟨cvs', as'', hal', htr'', hzip⟩ :=
              alignTraverse_master cs tail
                (fun c' hc' => h c' (List.mem_cons_of_mem c hc')) ht as cas' vs' has htr'
            refine ⟨(c, v) :: cvs', a₀ :: as'', ?_, ?_, ?_⟩
            · show (align cs tail vs').map ((c, v) :: ·) = _
              rw [hal']
              rfl
            · simp only [traverse]
              rw [ha₀, htr'']
            · intro q hq
              simp only [List.zip_cons_cons, List.mem_cons] at hq
              rcases hq with rfl | hq
              · exact hc.agree hpa ha₀
              · exact hzip q hq

theorem lawful_tupleCodec {cs : List Codec} {tail : Option Codec}
    (hcs : ∀ c ∈ cs, Lawful c) (ht : ∀ c ∈ tail, Lawful c) :
    Lawful (tupleCodec cs tail) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t
    case arr vs =>
      replace he : ((align cs tail vs).bind
        (traverse fun cv => cv.1.e cv.2)).map Attr.l = some a := he
      cases hal : align cs tail vs with
      | none => rw [hal] at he; exact nomatch he
      | some cvs =>
        rw [hal] at he
        replace he : (traverse (fun cv : Codec × Value => cv.1.e cv.2) cvs).map
          Attr.l = some a := he
        cases htr : traverse (fun cv : Codec × Value => cv.1.e cv.2) cvs with
        | none => rw [htr] at he; exact nomatch he
        | some as =>
          rw [htr] at he
          replace he : some (Attr.l as) = some a := he
          cases he
          show ((align cs tail as).bind
            (traverse fun ca => ca.1.p ca.2)).map Value.arr = some (.arr vs)
          rw [alignTraverse_roundTrip cs tail (fun c hc => (hcs c hc).core)
            (fun c hc => (ht c hc).core) vs cvs as hal htr]
          rfl
    all_goals exact nomatch he
  · intro a t hp
    cases a
    case l as =>
      replace hp : ((align cs tail as).bind
        (traverse fun ca => ca.1.p ca.2)).map Value.arr = some t := hp
      cases hal : align cs tail as with
      | none => rw [hal] at hp; exact nomatch hp
      | some cas =>
        rw [hal] at hp
        replace hp : (traverse (fun ca : Codec × Attr => ca.1.p ca.2) cas).map
          Value.arr = some t := hp
        cases htr : traverse (fun ca : Codec × Attr => ca.1.p ca.2) cas with
        | none => rw [htr] at hp; exact nomatch hp
        | some vs =>
          rw [htr] at hp
          replace hp : some (Value.arr vs) = some t := hp
          cases hp
          obtain ⟨cvs, as', hal', htr', -⟩ :=
            alignTraverse_master cs tail hcs ht as cas vs hal htr
          show (((align cs tail vs).bind
            (traverse fun cv => cv.1.e cv.2)).map Attr.l).isSome
          rw [hal']
          show ((traverse (fun cv : Codec × Value => cv.1.e cv.2) cvs).map
            Attr.l).isSome
          rw [htr']
          rfl
    all_goals exact nomatch hp
  · intro μ hμ t a he
    replace hμ : some Member.L = some μ := hμ
    cases hμ
    cases t
    case arr vs =>
      replace he : ((align cs tail vs).bind
        (traverse fun cv => cv.1.e cv.2)).map Attr.l = some a := he
      cases hal : align cs tail vs with
      | none => rw [hal] at he; exact nomatch he
      | some cvs =>
        rw [hal] at he
        replace he : (traverse (fun cv : Codec × Value => cv.1.e cv.2) cvs).map
          Attr.l = some a := he
        cases htr : traverse (fun cv : Codec × Value => cv.1.e cv.2) cvs with
        | none => rw [htr] at he; exact nomatch he
        | some as =>
          rw [htr] at he
          replace he : some (Attr.l as) = some a := he
          cases he
          rfl
    all_goals exact nomatch he
  · intro a t a' hp he
    cases a
    case l as =>
      replace hp : ((align cs tail as).bind
        (traverse fun ca => ca.1.p ca.2)).map Value.arr = some t := hp
      cases hal : align cs tail as with
      | none => rw [hal] at hp; exact nomatch hp
      | some cas =>
        rw [hal] at hp
        replace hp : (traverse (fun ca : Codec × Attr => ca.1.p ca.2) cas).map
          Value.arr = some t := hp
        cases htr : traverse (fun ca : Codec × Attr => ca.1.p ca.2) cas with
        | none => rw [htr] at hp; exact nomatch hp
        | some vs =>
          rw [htr] at hp
          replace hp : some (Value.arr vs) = some t := hp
          cases hp
          obtain ⟨cvs, as', hal', htr', hzip⟩ :=
            alignTraverse_master cs tail hcs ht as cas vs hal htr
          replace he : ((align cs tail vs).bind
            (traverse fun cv => cv.1.e cv.2)).map Attr.l = some a' := he
          rw [hal'] at he
          replace he : (traverse (fun cv : Codec × Value => cv.1.e cv.2) cvs).map
            Attr.l = some a' := he
          rw [htr'] at he
          replace he : some (Attr.l as') = some a' := he
          cases he
          exact .l as' as hzip
    all_goals exact nomatch hp

/-! ### Keyed lookup and traversal facts (the keyed product consumes these) -/

theorem mem_of_lookup {α : Type} :
    ∀ {l : List (Name × α)} {k v}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => nomatch h
  | (k₁, v₁) :: l, k, v, h => by
      simp only [List.lookup] at h
      cases hbe : (k == k₁) with
      | true =>
        rw [hbe] at h
        replace h : some v₁ = some v := h
        cases h
        have hk : k = k₁ := eq_of_beq hbe
        subst hk
        exact List.mem_cons_self _ _
      | false =>
        rw [hbe] at h
        replace h : List.lookup k l = some v := h
        exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem lookup_isSome_of_mem_fst {α : Type} :
    ∀ {l : List (Name × α)} {k}, k ∈ l.map (·.1) → (l.lookup k).isSome = true
  | [], _, h => absurd h (by simp)
  | (k₁, v₁) :: l, k, h => by
      simp only [List.map, List.mem_cons] at h
      simp only [List.lookup]
      cases hbe : (k == k₁) with
      | true => rfl
      | false =>
        rcases h with rfl | h'
        · exact absurd hbe (by simp)
        · exact lookup_isSome_of_mem_fst h'

theorem lookup_eq_of_mem_nodup {α : Type} :
    ∀ {l : List (Name × α)} {k v}, (l.map (·.1)).Nodup → (k, v) ∈ l →
      l.lookup k = some v
  | [], _, _, _, hm => nomatch hm
  | (k₁, v₁) :: l, k, v, hnd, hm => by
      obtain ⟨hnotin, hnd'⟩ := List.nodup_cons.mp hnd
      simp only [List.lookup]
      rcases List.mem_cons.mp hm with heq | hm'
      · cases heq
        simp
      · cases hbe : (k == k₁) with
        | true =>
          have hk : k = k₁ := eq_of_beq hbe
          subst hk
          exact absurd (List.mem_map.mpr ⟨(k, v), hm', rfl⟩) hnotin
        | false => exact lookup_eq_of_mem_nodup hnd' hm'

theorem lookup_none_of_not_mem_fst {α : Type} :
    ∀ {l : List (Name × α)} {k}, k ∉ l.map (·.1) → l.lookup k = none
  | [], _, _ => rfl
  | (k₁, v₁) :: l, k, h => by
      simp only [List.lookup]
      cases hbe : (k == k₁) with
      | true =>
        have hk : k = k₁ := eq_of_beq hbe
        subst hk
        exact absurd (by simp) h
      | false =>
        exact lookup_none_of_not_mem_fst fun h' =>
          h (by simp only [List.map, List.mem_cons]; exact Or.inr (by simpa using h'))

theorem mem_fst_of_lookup {α : Type} {l : List (Name × α)} {k v}
    (h : l.lookup k = some v) : k ∈ l.map (·.1) :=
  List.mem_map.mpr ⟨(k, v), mem_of_lookup h, rfl⟩

theorem traverse_fst {α β : Type} {f : Name × α → Option (Name × β)}
    (hf : ∀ kv kb, f kv = some kb → kb.1 = kv.1) :
    ∀ {kvs : List (Name × α)} {ds}, traverse f kvs = some ds →
      ds.map (·.1) = kvs.map (·.1)
  | [], ds, h => by
      replace h : some [] = some ds := h
      cases h
      rfl
  | kv :: kvs, ds, h => by
      simp only [traverse] at h
      cases hkv : f kv with
      | none => rw [hkv] at h; exact nomatch h
      | some kb =>
        rw [hkv] at h
        cases hks : traverse f kvs with
        | none => rw [hks] at h; exact nomatch h
        | some ds' =>
          rw [hks] at h
          replace h : some (kb :: ds') = some ds := h
          cases h
          simp only [List.map]
          rw [hf kv kb hkv, traverse_fst hf hks]

theorem traverse_mem₂ {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys}, traverse f xs = some ys →
      ∀ y ∈ ys, ∃ x ∈ xs, f x = some y
  | [], ys, h => by
      replace h : some [] = some ys := h
      cases h
      intro y hy
      exact absurd hy (by simp)
  | x :: xs, ys, h => by
      simp only [traverse] at h
      cases hfx : f x with
      | none => rw [hfx] at h; exact nomatch h
      | some y₀ =>
        rw [hfx] at h
        cases hxs : traverse f xs with
        | none => rw [hxs] at h; exact nomatch h
        | some ys' =>
          rw [hxs] at h
          replace h : some (y₀ :: ys') = some ys := h
          cases h
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact ⟨x, List.mem_cons_self _ _, hfx⟩
          · obtain ⟨x', hx', hfx'⟩ := traverse_mem₂ hxs y hy'
            exact ⟨x', List.mem_cons_of_mem _ hx', hfx'⟩

theorem traverse_append {α β : Type} {f : α → Option β} :
    ∀ {l₁ l₂ : List α} {r₁ r₂}, traverse f l₁ = some r₁ → traverse f l₂ = some r₂ →
      traverse f (l₁ ++ l₂) = some (r₁ ++ r₂)
  | [], l₂, r₁, r₂, h₁, h₂ => by
      replace h₁ : some [] = some r₁ := h₁
      cases h₁
      exact h₂
  | x :: l₁, l₂, r₁, r₂, h₁, h₂ => by
      simp only [traverse] at h₁
      cases hfx : f x with
      | none => rw [hfx] at h₁; exact nomatch h₁
      | some y =>
        rw [hfx] at h₁
        cases hl : traverse f l₁ with
        | none => rw [hl] at h₁; exact nomatch h₁
        | some r₁' =>
          rw [hl] at h₁
          replace h₁ : some (y :: r₁') = some r₁ := h₁
          cases h₁
          show traverse f (x :: (l₁ ++ l₂)) = some ((y :: r₁') ++ r₂)
          simp only [traverse]
          rw [hfx, traverse_append hl h₂]
          rfl

theorem traverse_append_inv {α β : Type} {f : α → Option β} :
    ∀ {l₁ l₂ : List α} {r}, traverse f (l₁ ++ l₂) = some r →
      ∃ r₁ r₂, r = r₁ ++ r₂ ∧ traverse f l₁ = some r₁ ∧ traverse f l₂ = some r₂
  | [], l₂, r, h => ⟨[], r, rfl, rfl, h⟩
  | x :: l₁, l₂, r, h => by
      replace h : traverse f (x :: (l₁ ++ l₂)) = some r := h
      simp only [traverse] at h
      cases hfx : f x with
      | none => rw [hfx] at h; exact nomatch h
      | some y =>
        rw [hfx] at h
        cases hl : traverse f (l₁ ++ l₂) with
        | none => rw [hl] at h; exact nomatch h
        | some r' =>
          rw [hl] at h
          replace h : some (y :: r') = some r := h
          cases h
          obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := traverse_append_inv hl
          refine ⟨y :: r₁, r₂, rfl, ?_, h₂⟩
          simp only [traverse]
          rw [hfx, h₁]

theorem traverse_isSome_of_all {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).isSome = true) → (traverse f l).isSome = true
  | [], _ => rfl
  | x :: l, h => by
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h x (List.mem_cons_self _ _))
      obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.mp
        (traverse_isSome_of_all fun z hz => h z (List.mem_cons_of_mem _ hz))
      simp only [traverse]
      rw [hy, hys]
      rfl

theorem filter_eq_self_of_all {α : Type} {p : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true) → l.filter p = l
  | [], _ => rfl
  | x :: l, h => by
      have hx := h x (List.mem_cons_self _ _)
      simp only [List.filter, hx]
      rw [filter_eq_self_of_all fun z hz => h z (List.mem_cons_of_mem _ hz)]

theorem lookup_filter_pos {α : Type} {kn : Name → Bool} {k : Name} (hk : kn k = true) :
    ∀ (l : List (Name × α)),
      (l.filter fun kv => kn kv.1).lookup k = l.lookup k
  | [] => rfl
  | (k₁, v₁) :: l => by
      simp only [List.filter]
      cases hkn₁ : kn k₁ with
      | true =>
        simp only [List.lookup]
        cases hbe : (k == k₁) with
        | true => rfl
        | false => exact lookup_filter_pos hk l
      | false =>
        simp only [List.lookup]
        cases hbe : (k == k₁) with
        | true =>
          have hkk : k = k₁ := eq_of_beq hbe
          subst hkk
          rw [hk] at hkn₁
          exact nomatch hkn₁
        | false => exact lookup_filter_pos hk l

theorem lookup_filter_neg {α : Type} {kn : Name → Bool} {k : Name} (hk : kn k = false) :
    ∀ (l : List (Name × α)),
      (l.filter fun kv => kn kv.1).lookup k = none
  | [] => rfl
  | (k₁, v₁) :: l => by
      simp only [List.filter]
      cases hkn₁ : kn k₁ with
      | true =>
        simp only [List.lookup]
        cases hbe : (k == k₁) with
        | true =>
          have hkk : k = k₁ := eq_of_beq hbe
          subst hkk
          rw [hk] at hkn₁
          exact nomatch hkn₁
        | false => exact lookup_filter_neg hk l
      | false => exact lookup_filter_neg hk l

theorem lookup_append {α : Type} :
    ∀ (l₁ l₂ : List (Name × α)) (k : Name),
      (l₁ ++ l₂).lookup k =
        match l₁.lookup k with
        | some v => some v
        | none => l₂.lookup k
  | [], _, _ => rfl
  | (k₁, v₁) :: l₁, l₂, k => by
      show ((k₁, v₁) :: (l₁ ++ l₂)).lookup k = _
      simp only [List.lookup]
      cases hbe : (k == k₁) with
      | true => rfl
      | false => exact lookup_append l₁ l₂ k

theorem fbDefaults_nil :
    ∀ {sems : List (Name × FieldSem)} {names : List Name},
      (∀ k c v, (k, FieldSem.fb c v) ∈ sems → names.contains k = true) →
      fbDefaults names sems = []
  | [], _, _ => rfl
  | (k, fs) :: sems, names, h => by
      have hrest := fbDefaults_nil fun k' c v hm =>
        h k' c v (List.mem_cons_of_mem _ hm)
      cases fs with
      | fb c v =>
        have hc := h k c v (List.mem_cons_self _ _)
        simp only [fbDefaults, hc]
        exact hrest
      | req c =>
        show fbDefaults names sems = []
        exact hrest
      | opt c =>
        show fbDefaults names sems = []
        exact hrest

theorem mem_fbDefaults :
    ∀ {sems : List (Name × FieldSem)} {names k c v},
      (k, FieldSem.fb c v) ∈ sems → names.contains k = false →
      (k, v) ∈ fbDefaults names sems
  | [], _, _, _, _, hm, _ => nomatch hm
  | (k₁, fs₁) :: sems, names, k, c, v, hm, hc => by
      rcases List.mem_cons.mp hm with heq | hm'
      · cases heq
        simp only [fbDefaults, hc]
        exact List.mem_cons_self _ _
      · cases fs₁ with
        | fb c₁ v₁ =>
          show (k, v) ∈ (if names.contains k₁ then fbDefaults names sems
            else (k₁, v₁) :: fbDefaults names sems)
          cases hc₁ : names.contains k₁ with
          | true =>
            show (k, v) ∈ fbDefaults names sems
            exact mem_fbDefaults hm' hc
          | false =>
            exact List.mem_cons_of_mem _ (mem_fbDefaults hm' hc)
        | req c₁ =>
          show (k, v) ∈ fbDefaults names sems
          exact mem_fbDefaults hm' hc
        | opt c₁ =>
          show (k, v) ∈ fbDefaults names sems
          exact mem_fbDefaults hm' hc

theorem fbDefaults_not_mem :
    ∀ {sems : List (Name × FieldSem)} {names k}, names.contains k = true →
      k ∉ (fbDefaults names sems).map (·.1)
  | [], _, _, _ => by simp [fbDefaults]
  | (k₁, fs₁) :: sems, names, k, hc => by
      cases fs₁ with
      | fb c₁ v₁ =>
        show k ∉ ((if names.contains k₁ then fbDefaults names sems
          else (k₁, v₁) :: fbDefaults names sems)).map (·.1)
        cases hc₁ : names.contains k₁ with
        | true =>
          show k ∉ (fbDefaults names sems).map (·.1)
          exact fbDefaults_not_mem hc
        | false =>
          intro hmem
          simp only [List.map, List.mem_cons] at hmem
          rcases hmem with rfl | hmem'
          · rw [hc] at hc₁; exact nomatch hc₁
          · exact fbDefaults_not_mem hc hmem'
      | req c₁ =>
        show k ∉ (fbDefaults names sems).map (·.1)
        exact fbDefaults_not_mem hc
      | opt c₁ =>
        show k ∉ (fbDefaults names sems).map (·.1)
        exact fbDefaults_not_mem hc

theorem fbDefaults_spec :
    ∀ {sems : List (Name × FieldSem)} {names k v},
      (k, v) ∈ fbDefaults names sems →
      ∃ c, (k, FieldSem.fb c v) ∈ sems ∧ names.contains k = false
  | [], _, _, _, hm => nomatch hm
  | (k₁, fs₁) :: sems, names, k, v, hm => by
      cases fs₁ with
      | fb c₁ v₁ =>
        replace hm : (k, v) ∈ (if names.contains k₁ then fbDefaults names sems
          else (k₁, v₁) :: fbDefaults names sems) := hm
        cases hc₁ : names.contains k₁ with
        | true =>
          rw [hc₁] at hm
          replace hm : (k, v) ∈ fbDefaults names sems := hm
          obtain ⟨c, hmem, hc⟩ := fbDefaults_spec hm
          exact ⟨c, List.mem_cons_of_mem _ hmem, hc⟩
        | false =>
          rw [hc₁] at hm
          replace hm : (k, v) ∈ (k₁, v₁) :: fbDefaults names sems := hm
          rcases List.mem_cons.mp hm with heq | hm'
          · cases heq
            exact ⟨c₁, List.mem_cons_self _ _, hc₁⟩
          · obtain ⟨c, hmem, hc⟩ := fbDefaults_spec hm'
            exact ⟨c, List.mem_cons_of_mem _ hmem, hc⟩
      | req c₁ =>
        replace hm : (k, v) ∈ fbDefaults names sems := hm
        obtain ⟨c, hmem, hc⟩ := fbDefaults_spec hm
        exact ⟨c, List.mem_cons_of_mem _ hmem, hc⟩
      | opt c₁ =>
        replace hm : (k, v) ∈ fbDefaults names sems := hm
        obtain ⟨c, hmem, hc⟩ := fbDefaults_spec hm
        exact ⟨c, List.mem_cons_of_mem _ hmem, hc⟩

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

theorem mem_of_contains {l : List String} {s : String} (h : l.contains s = true) :
    s ∈ l := by
  induction l with
  | nil => exact nomatch h
  | cons a l ih =>
    replace h : List.elem s (a :: l) = true := h
    simp only [List.elem] at h
    cases hbe : (s == a) with
    | true => exact List.mem_cons.mpr (Or.inl (eq_of_beq hbe))
    | false =>
      rw [hbe] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem exists_of_mem_fst {α : Type} {l : List (Name × α)} {k}
    (h : k ∈ l.map (·.1)) : ∃ x, (k, x) ∈ l := by
  obtain ⟨p, hp, hp1⟩ := List.mem_map.mp h
  exact ⟨p.2, by rw [← hp1]; exact hp⟩

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

/-- The per-name half of §4's held set: a declared name holds its field's set, an
    undeclared one falls to the open part `R(ρ)`. -/
def objEntryT (sems : List (Name × FieldSem)) (rc? : Option Codec) :
    Name × Value → Prop := fun kv =>
  match sems.lookup kv.1 with
  | some fs => fs.codec.T kv.2
  | none => ∃ rc, rc? = some rc ∧ rc.T kv.2

/-- The converse of `fbDefaults_spec`: an absent `fb` name does get its stand-in. -/
theorem fbDefaults_mem :
    ∀ {sems : List (Name × FieldSem)} {names k c v},
      (k, FieldSem.fb c v) ∈ sems → names.contains k = false →
      (k, v) ∈ fbDefaults names sems
  | [], _, _, _, _, hm, _ => nomatch hm
  | (k₁, fs₁) :: sems, names, k, c, v, hm, hc => by
      cases fs₁ with
      | req c₁ =>
        show (k, v) ∈ fbDefaults names sems
        rcases List.mem_cons.mp hm with heq | hm'
        · exact nomatch (congrArg Prod.snd heq)
        · exact fbDefaults_mem hm' hc
      | opt c₁ =>
        show (k, v) ∈ fbDefaults names sems
        rcases List.mem_cons.mp hm with heq | hm'
        · exact nomatch (congrArg Prod.snd heq)
        · exact fbDefaults_mem hm' hc
      | fb c₁ v₁ =>
        show (k, v) ∈ (if names.contains k₁ then fbDefaults names sems
          else (k₁, v₁) :: fbDefaults names sems)
        rcases List.mem_cons.mp hm with heq | hm'
        · have h1 : k = k₁ := congrArg Prod.fst heq
          have h2 : v = v₁ := by
            have hs := congrArg Prod.snd heq
            injection hs
          subst h1
          subst h2
          rw [hc]
          exact List.mem_cons_self _ _
        · have ih := fbDefaults_mem hm' hc
          cases hc₁ : names.contains k₁ with
          | true => exact ih
          | false => exact List.mem_cons_of_mem _ ih

/-- An entry survives `p`'s name filter and so appears among its outputs. -/
theorem mem_decoded_names {kvs : List (Name × Attr)} {kn : Name → Bool}
    {sems : List (Name × FieldSem)} {rc? : Option Codec} {ds k}
    (htr : traverse (decEntry (fun k' => sems.lookup k') (rc?.map (·.p)))
      (kvs.filter fun kv => kn kv.1) = some ds)
    (hk : k ∈ kvs.map (·.1)) (hkeep : kn k = true) : k ∈ ds.map (·.1) := by
  rw [traverse_fst decEntry_fst htr]
  obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp hk
  exact List.mem_map.mpr ⟨kv, List.mem_filter.mpr ⟨hkv, hkeep⟩, rfl⟩

/-- §4's held set, both ways. The two premises past lawfulness are the doc's own:
    `hfb` is `(fallback)`'s `v(∗) ∈ dom(e)`, which with `domE` gives §4's `v : 𝟙 → T`;
    `hkeep` says the name filter never discards a declared name, which is what all
    three rest policies do. -/
theorem carrier_objectCodecCore {sems : List (Name × FieldSem)} {rc? : Option Codec}
    {kn : Name → Bool}
    (hsems : ∀ kf ∈ sems, Carrier kf.2.codec)
    (hrc : ∀ rc, rc? = some rc → Carrier rc)
    (hfb : ∀ kf ∈ sems, ∀ c v, kf.2 = .fb c v → (c.e v).isSome)
    (hnd : (sems.map (·.1)).Nodup)
    (hkeep : ∀ k, (sems.lookup k).isSome → kn k = true) :
    Carrier (objectCodecCore sems rc? kn) := by
  have entry_e : ∀ kv y,
      encEntry (fun k => sems.lookup k) (rc?.map (·.e)) kv = some y →
      objEntryT sems rc? kv := by
    intro kv y hy
    simp only [encEntry] at hy
    cases hsp : sems.lookup kv.1 with
    | some fs =>
      rw [hsp] at hy
      replace hy : ((fs.codec.e kv.2).map ((kv.1, ·))) = some y := hy
      cases he : fs.codec.e kv.2 with
      | none => rw [he] at hy; exact nomatch hy
      | some a' =>
        simp only [objEntryT, hsp]
        exact (hsems (kv.1, fs) (mem_of_lookup hsp)).domE he
    | none =>
      rw [hsp] at hy
      simp only [objEntryT, hsp]
      cases hr : rc? with
      | none => rw [hr] at hy; exact nomatch hy
      | some rc =>
        rw [hr] at hy
        replace hy : ((rc.e kv.2).map ((kv.1, ·))) = some y := hy
        cases he : rc.e kv.2 with
        | none => rw [he] at hy; exact nomatch hy
        | some a' => exact ⟨rc, rfl, (hrc rc hr).domE he⟩
  have entry_p : ∀ ka kv,
      decEntry (fun k => sems.lookup k) (rc?.map (·.p)) ka = some kv →
      objEntryT sems rc? kv := by
    intro ka kv hy
    simp only [decEntry] at hy
    cases hsp : sems.lookup ka.1 with
    | some fs =>
      rw [hsp] at hy
      replace hy : ((fs.codec.p ka.2).map ((ka.1, ·))) = some kv := hy
      cases hp : fs.codec.p ka.2 with
      | none => rw [hp] at hy; exact nomatch hy
      | some v' =>
        rw [hp] at hy
        replace hy : some (ka.1, v') = some kv := hy
        cases hy
        simp only [objEntryT, hsp]
        exact (hsems (ka.1, fs) (mem_of_lookup hsp)).ranP hp
    | none =>
      rw [hsp] at hy
      cases hr : rc? with
      | none => rw [hr] at hy; exact nomatch hy
      | some rc =>
        rw [hr] at hy
        replace hy : ((rc.p ka.2).map ((ka.1, ·))) = some kv := hy
        cases hp : rc.p ka.2 with
        | none => rw [hp] at hy; exact nomatch hy
        | some v' =>
          rw [hp] at hy
          replace hy : some (ka.1, v') = some kv := hy
          cases hy
          simp only [objEntryT, hsp]
          exact ⟨rc, rfl, (hrc rc hr).ranP hp⟩
  refine ⟨?_, ?_⟩
  · intro v a h
    cases v
    case map kvs =>
      replace h : (if valPresentB sems (kvs.map (·.1)) = true then
        (traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e))) kvs).map Attr.m
        else none) = some a := h
      split at h
      next hval =>
        cases htr : traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e))) kvs with
        | none => rw [htr] at h; exact nomatch h
        | some ds => exact ⟨hval, traverse_mem_input entry_e htr⟩
      next => exact nomatch h
    all_goals exact nomatch h
  · intro a v h
    cases a
    case m kvs =>
      replace h : (if reqPresentB sems (kvs.map (·.1)) = true then
        (traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
          (kvs.filter fun kv => kn kv.1)).map (fun ds =>
            Value.map (ds ++ fbDefaults (kvs.map (·.1)) sems)) else none) = some v := h
      split at h
      next hreq =>
        cases htr : traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
            (kvs.filter fun kv => kn kv.1) with
        | none => rw [htr] at h; exact nomatch h
        | some ds =>
          rw [htr] at h
          replace h : some (Value.map (ds ++ fbDefaults (kvs.map (·.1)) sems))
            = some v := h
          cases h
          -- every non-`opt` name is written: `req` from the row, `fb` from the row or
          -- else from its stand-in
          have hpresent : ∀ k fs, (k, fs) ∈ sems → (∀ c, fs ≠ FieldSem.opt c) →
              ((ds ++ fbDefaults (kvs.map (·.1)) sems).map (·.1)).contains k = true := by
            intro k fs hm hno
            have hlk : sems.lookup k = some fs := lookup_eq_of_mem_nodup hnd hm
            have hkn : kn k = true := hkeep k (by rw [hlk]; rfl)
            rw [List.map_append]
            refine List.elem_eq_true_of_mem (List.mem_append.mpr ?_)
            cases fs with
            | opt c => exact absurd rfl (hno c)
            | req c =>
              have hpres := List.all_eq_true.mp hreq (k, .req c) hm
              exact Or.inl (mem_decoded_names htr (mem_of_contains hpres) hkn)
            | fb c v₀ =>
              cases hc : (kvs.map (·.1)).contains k with
              | true => exact Or.inl (mem_decoded_names htr (mem_of_contains hc) hkn)
              | false =>
                exact Or.inr (List.mem_map.mpr ⟨(k, v₀), fbDefaults_mem hm hc, rfl⟩)
          refine ⟨valPresentB_of hpresent, ?_⟩
          intro kv hkv
          rcases List.mem_append.mp hkv with hd | hf
          · exact traverse_mem entry_p htr kv hd
          · obtain ⟨c, hmem, hc⟩ := fbDefaults_spec hf
            have hlk : sems.lookup kv.1 = some (FieldSem.fb c kv.2) :=
              lookup_eq_of_mem_nodup hnd hmem
            simp only [objEntryT, hlk]
            obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
              (hfb (kv.1, .fb c kv.2) hmem c kv.2 rfl)
            exact (hsems (kv.1, .fb c kv.2) hmem).domE ha'
      next => exact nomatch h
    all_goals exact nomatch h

private theorem objStep_rt {sems : List (Name × FieldSem)} {rc? : Option Codec}
    (hf : ∀ kf ∈ sems, LawfulCore kf.2.codec) (hrc : ∀ c ∈ rc?, LawfulCore c) :
    ∀ kv ka, encEntry (fun k => sems.lookup k) (rc?.map (·.e)) kv = some ka →
      decEntry (fun k => sems.lookup k) (rc?.map (·.p)) ka = some kv := by
  intro ⟨k, v⟩ ka hkv
  simp only [encEntry] at hkv
  cases hsp : sems.lookup k with
  | some fs =>
    rw [hsp] at hkv
    replace hkv : (fs.codec.e v).map ((k, ·)) = some ka := hkv
    cases hev : fs.codec.e v with
    | none => rw [hev] at hkv; exact nomatch hkv
    | some a₀ =>
      rw [hev] at hkv
      replace hkv : some (k, a₀) = some ka := hkv
      cases hkv
      simp only [decEntry]
      rw [hsp]
      show (fs.codec.p a₀).map ((k, ·)) = some (k, v)
      rw [(hf (k, fs) (mem_of_lookup hsp)).retract hev]
      rfl
  | none =>
    rw [hsp] at hkv
    cases rc? with
    | none => exact nomatch hkv
    | some rc =>
      replace hkv : (rc.e v).map ((k, ·)) = some ka := hkv
      cases hev : rc.e v with
      | none => rw [hev] at hkv; exact nomatch hkv
      | some a₀ =>
        rw [hev] at hkv
        replace hkv : some (k, a₀) = some ka := hkv
        cases hkv
        simp only [decEntry]
        rw [hsp]
        show (rc.p a₀).map ((k, ·)) = some (k, v)
        rw [(hrc rc rfl).retract hev]
        rfl

private theorem objStep_canon {sems : List (Name × FieldSem)} {rc? : Option Codec}
    (hf : ∀ kf ∈ sems, LawfulCore kf.2.codec) (hrc : ∀ c ∈ rc?, LawfulCore c) :
    ∀ ka kv, decEntry (fun k => sems.lookup k) (rc?.map (·.p)) ka = some kv →
      (encEntry (fun k => sems.lookup k) (rc?.map (·.e)) kv).isSome = true := by
  intro ⟨k, a⟩ kv hka
  simp only [decEntry] at hka
  cases hsp : sems.lookup k with
  | some fs =>
    rw [hsp] at hka
    replace hka : (fs.codec.p a).map ((k, ·)) = some kv := hka
    cases hpa : fs.codec.p a with
    | none => rw [hpa] at hka; exact nomatch hka
    | some v₀ =>
      rw [hpa] at hka
      replace hka : some (k, v₀) = some kv := hka
      cases hka
      simp only [encEntry]
      rw [hsp]
      show ((fs.codec.e v₀).map ((k, ·))).isSome = true
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
        ((hf (k, fs) (mem_of_lookup hsp)).canon hpa)
      rw [ha']
      rfl
  | none =>
    rw [hsp] at hka
    cases rc? with
    | none => exact nomatch hka
    | some rc =>
      replace hka : (rc.p a).map ((k, ·)) = some kv := hka
      cases hpa : rc.p a with
      | none => rw [hpa] at hka; exact nomatch hka
      | some v₀ =>
        rw [hpa] at hka
        replace hka : some (k, v₀) = some kv := hka
        cases hka
        simp only [encEntry]
        rw [hsp]
        show ((rc.e v₀).map ((k, ·))).isSome = true
        obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ((hrc rc rfl).canon hpa)
        rw [ha']
        rfl

private theorem objStep_agree {sems : List (Name × FieldSem)} {rc? : Option Codec}
    (hf : ∀ kf ∈ sems, Lawful kf.2.codec) (hrc : ∀ c ∈ rc?, Lawful c) :
    ∀ ka kv ka', decEntry (fun k => sems.lookup k) (rc?.map (·.p)) ka = some kv →
      encEntry (fun k => sems.lookup k) (rc?.map (·.e)) kv = some ka' →
      ka'.1 = ka.1 ∧ Agree ka'.2 ka.2 := by
  intro ⟨k, a⟩ kv ka' hka hkv
  simp only [decEntry] at hka
  cases hsp : sems.lookup k with
  | some fs =>
    rw [hsp] at hka
    replace hka : (fs.codec.p a).map ((k, ·)) = some kv := hka
    cases hpa : fs.codec.p a with
    | none => rw [hpa] at hka; exact nomatch hka
    | some v₀ =>
      rw [hpa] at hka
      replace hka : some (k, v₀) = some kv := hka
      cases hka
      simp only [encEntry] at hkv
      rw [hsp] at hkv
      replace hkv : (fs.codec.e v₀).map ((k, ·)) = some ka' := hkv
      cases hev : fs.codec.e v₀ with
      | none => rw [hev] at hkv; exact nomatch hkv
      | some a₀ =>
        rw [hev] at hkv
        replace hkv : some (k, a₀) = some ka' := hkv
        cases hkv
        exact ⟨rfl, (hf (k, fs) (mem_of_lookup hsp)).agree hpa hev⟩
  | none =>
    rw [hsp] at hka
    cases rc? with
    | none => exact nomatch hka
    | some rc =>
      replace hka : (rc.p a).map ((k, ·)) = some kv := hka
      cases hpa : rc.p a with
      | none => rw [hpa] at hka; exact nomatch hka
      | some v₀ =>
        rw [hpa] at hka
        replace hka : some (k, v₀) = some kv := hka
        cases hka
        simp only [encEntry] at hkv
        rw [hsp] at hkv
        replace hkv : (rc.e v₀).map ((k, ·)) = some ka' := hkv
        cases hev : rc.e v₀ with
        | none => rw [hev] at hkv; exact nomatch hkv
        | some a₀ =>
          rw [hev] at hkv
          replace hkv : some (k, a₀) = some ka' := hkv
          cases hkv
          exact ⟨rfl, (hrc rc rfl).agree hpa hev⟩

/-- Inversion of an object-encode success: the value is a map, the guard held, and the
    written item is the entrywise traversal. -/
theorem objectCodecCore_e_inv {sems : List (Name × FieldSem)} {rc? : Option Codec}
    {kn : Name → Bool} {t a}
    (he : (objectCodecCore sems rc? kn).e t = some a) :
    ∃ kvs ds, t = Value.map kvs ∧ a = Attr.m ds ∧
      valPresentB sems (kvs.map (·.1)) = true ∧
      traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e))) kvs = some ds := by
  cases t
  case map kvs =>
    replace he : (if valPresentB sems (kvs.map (·.1)) = true then
        (traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e))) kvs).map Attr.m
      else none) = some a := he
    cases hval : valPresentB sems (kvs.map (·.1)) with
    | false => rw [hval] at he; exact nomatch he
    | true =>
      rw [hval] at he
      replace he : (traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e)))
        kvs).map Attr.m = some a := he
      cases htr : traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e))) kvs with
      | none => rw [htr] at he; exact nomatch he
      | some ds =>
        rw [htr] at he
        replace he : some (Attr.m ds) = some a := he
        cases he
        exact ⟨kvs, ds, rfl, rfl, hval, htr⟩
  all_goals exact nomatch he

/-- The keyed product, parametrically: the toolkit over the name-dispatched steps, plus
    the presence guards and the fallback stand-ins. -/
private theorem lawful_objectCore
    (sems : List (Name × FieldSem)) (rc? : Option Codec) (kn : Name → Bool)
    (hf : ∀ kf ∈ sems, Lawful kf.2.codec)
    (hfb : ∀ kf ∈ sems, ∀ c v, kf.2 = .fb c v → (c.e v).isSome = true)
    (hnd : (sems.map (·.1)).Nodup)
    (hrc : ∀ c ∈ rc?, Lawful c)
    (hknE : ∀ kv ka, encEntry (fun k => sems.lookup k) (rc?.map (·.e)) kv = some ka →
      kn ka.1 = true)
    (hknDecl : ∀ k, (sems.lookup k).isSome = true → kn k = true) :
    Lawful (objectCodecCore sems rc? kn) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t
    case map kvs =>
      replace he : (if valPresentB sems (kvs.map (·.1)) = true then
          (traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e))) kvs).map Attr.m
        else none) = some a := he
      cases hval : valPresentB sems (kvs.map (·.1)) with
      | false => rw [hval] at he; exact nomatch he
      | true =>
        rw [hval] at he
        replace he : (traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e)))
          kvs).map Attr.m = some a := he
        cases htr : traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e))) kvs with
        | none => rw [htr] at he; exact nomatch he
        | some ds =>
          rw [htr] at he
          replace he : some (Attr.m ds) = some a := he
          cases he
          have hnames : ds.map (·.1) = kvs.map (·.1) := traverse_fst encEntry_fst htr
          have hreq : reqPresentB sems (ds.map (·.1)) = true := by
            rw [hnames]
            exact reqPresentB_of fun k c hm =>
              valPresentB_spec hval hm (fun _ h' => nomatch h')
          have hkeep : ds.filter (fun kv => kn kv.1) = ds :=
            filter_eq_self_of_all fun d hd => by
              obtain ⟨kv, _, hkv⟩ := traverse_mem₂ htr d hd
              exact hknE kv d hkv
          have hfbnil : fbDefaults (ds.map (·.1)) sems = [] := by
            rw [hnames]
            exact fbDefaults_nil fun k c v hm =>
              valPresentB_spec hval hm (fun _ h' => nomatch h')
          have hdec := traverse_roundTrip
            (objStep_rt (fun kf hkf => (hf kf hkf).core) (fun c hc => (hrc c hc).core))
            kvs ds htr
          show (if reqPresentB sems (ds.map (·.1)) = true then
              (traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
                (ds.filter fun kv => kn kv.1)).map fun ds' =>
                  Value.map (ds' ++ fbDefaults (ds.map (·.1)) sems)
            else none) = some (.map kvs)
          rw [hreq, hkeep, hdec, hfbnil]
          simp only [List.append_nil]
          rfl
    all_goals exact nomatch he
  · intro a t hp
    cases a
    case m kvs =>
      replace hp : (if reqPresentB sems (kvs.map (·.1)) = true then
          (traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
            (kvs.filter fun kv => kn kv.1)).map fun ds =>
              Value.map (ds ++ fbDefaults (kvs.map (·.1)) sems)
        else none) = some t := hp
      cases hreq : reqPresentB sems (kvs.map (·.1)) with
      | false => rw [hreq] at hp; exact nomatch hp
      | true =>
        rw [hreq] at hp
        replace hp : (traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
            (kvs.filter fun kv => kn kv.1)).map (fun ds =>
              Value.map (ds ++ fbDefaults (kvs.map (·.1)) sems)) = some t := hp
        cases htr : traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
            (kvs.filter fun kv => kn kv.1) with
        | none => rw [htr] at hp; exact nomatch hp
        | some ds =>
          rw [htr] at hp
          replace hp : some (Value.map (ds ++ fbDefaults (kvs.map (·.1)) sems)) =
            some t := hp
          cases hp
          have hds := traverse_isSome
            (f := encEntry (fun k => sems.lookup k) (rc?.map (·.e)))
            (objStep_canon (fun kf hkf => (hf kf hkf).core) (fun c hc => (hrc c hc).core))
            (kvs.filter fun kv => kn kv.1) ds htr
          obtain ⟨es₁, hes₁⟩ := Option.isSome_iff_exists.mp hds
          have hdefs : ∀ x ∈ fbDefaults (kvs.map (·.1)) sems,
              ((encEntry (fun k => sems.lookup k) (rc?.map (·.e))) x).isSome = true := by
            intro ⟨k', v'⟩ hx
            obtain ⟨c, hmem, hcf⟩ := fbDefaults_spec hx
            have hlk : sems.lookup k' = some (.fb c v') := lookup_eq_of_mem_nodup hnd hmem
            simp only [encEntry]
            rw [hlk]
            show ((c.e v').map ((k', ·))).isSome = true
            obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
              (hfb (k', .fb c v') hmem c v' rfl)
            rw [ha']
            rfl
          obtain ⟨es₂, hes₂⟩ := Option.isSome_iff_exists.mp
            (traverse_isSome_of_all hdefs)
          have hall := traverse_append hes₁ hes₂
          have hnames : ds.map (·.1) = (kvs.filter fun kv => kn kv.1).map (·.1) :=
            traverse_fst decEntry_fst htr
          have hval : valPresentB sems
              ((ds ++ fbDefaults (kvs.map (·.1)) sems).map (·.1)) = true := by
            refine valPresentB_of fun k fs hm hno => ?_
            rw [List.map_append]
            cases hck : (kvs.map (·.1)).contains k with
            | true =>
              have hkmem : k ∈ kvs.map (·.1) := mem_of_contains hck
              obtain ⟨ax, haxm⟩ := exists_of_mem_fst hkmem
              have hknk : kn k = true := hknDecl k (lookup_isSome_of_mem_fst
                (List.mem_map.mpr ⟨(k, fs), hm, rfl⟩))
              have hkeepm : (k, ax) ∈ kvs.filter fun kv => kn kv.1 :=
                List.mem_filter.mpr ⟨haxm, hknk⟩
              have hkfl : k ∈ (kvs.filter fun kv => kn kv.1).map (·.1) :=
                List.mem_map.mpr ⟨(k, ax), hkeepm, rfl⟩
              rw [← hnames] at hkfl
              exact contains_of_mem (List.mem_append.mpr (Or.inl hkfl))
            | false =>
              cases fs with
              | opt c => exact absurd rfl (hno c)
              | req c => rw [reqPresentB_spec hreq hm] at hck; exact nomatch hck
              | fb c v =>
                have hin := mem_fbDefaults hm hck
                exact contains_of_mem (List.mem_append.mpr (Or.inr
                  (List.mem_map.mpr ⟨(k, v), hin, rfl⟩)))
          show (if valPresentB sems
              ((ds ++ fbDefaults (kvs.map (·.1)) sems).map (·.1)) = true then
              (traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e)))
                (ds ++ fbDefaults (kvs.map (·.1)) sems)).map Attr.m
            else none).isSome = true
          rw [hval, hall]
          rfl
    all_goals exact nomatch hp
  · intro μ hμ t a he
    replace hμ : some Member.M = some μ := hμ
    cases hμ
    cases t
    case map kvs =>
      replace he : (if valPresentB sems (kvs.map (·.1)) = true then
          (traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e))) kvs).map Attr.m
        else none) = some a := he
      cases hval : valPresentB sems (kvs.map (·.1)) with
      | false => rw [hval] at he; exact nomatch he
      | true =>
        rw [hval] at he
        replace he : (traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e)))
          kvs).map Attr.m = some a := he
        cases htr : traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e))) kvs with
        | none => rw [htr] at he; exact nomatch he
        | some ds =>
          rw [htr] at he
          replace he : some (Attr.m ds) = some a := he
          cases he
          rfl
    all_goals exact nomatch he
  · intro a t a' hp he
    cases a
    case m kvs =>
      replace hp : (if reqPresentB sems (kvs.map (·.1)) = true then
          (traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
            (kvs.filter fun kv => kn kv.1)).map fun ds =>
              Value.map (ds ++ fbDefaults (kvs.map (·.1)) sems)
        else none) = some t := hp
      cases hreq : reqPresentB sems (kvs.map (·.1)) with
      | false => rw [hreq] at hp; exact nomatch hp
      | true =>
        rw [hreq] at hp
        replace hp : (traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
            (kvs.filter fun kv => kn kv.1)).map (fun ds =>
              Value.map (ds ++ fbDefaults (kvs.map (·.1)) sems)) = some t := hp
        cases htr : traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
            (kvs.filter fun kv => kn kv.1) with
        | none => rw [htr] at hp; exact nomatch hp
        | some ds =>
          rw [htr] at hp
          replace hp : some (Value.map (ds ++ fbDefaults (kvs.map (·.1)) sems)) =
            some t := hp
          cases hp
          replace he : (if valPresentB sems
              ((ds ++ fbDefaults (kvs.map (·.1)) sems).map (·.1)) = true then
              (traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e)))
                (ds ++ fbDefaults (kvs.map (·.1)) sems)).map Attr.m
            else none) = some a' := he
          cases hval : valPresentB sems
              ((ds ++ fbDefaults (kvs.map (·.1)) sems).map (·.1)) with
          | false => rw [hval] at he; exact nomatch he
          | true =>
            rw [hval] at he
            replace he : (traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e)))
              (ds ++ fbDefaults (kvs.map (·.1)) sems)).map Attr.m = some a' := he
            cases hall : traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e)))
                (ds ++ fbDefaults (kvs.map (·.1)) sems) with
            | none => rw [hall] at he; exact nomatch he
            | some es =>
              rw [hall] at he
              replace he : some (Attr.m es) = some a' := he
              cases he
              obtain ⟨es₁, es₂, rfl, h₁, h₂⟩ := traverse_append_inv hall
              refine .m (es₁ ++ es₂) kvs ?_
              intro k x y hxk hyk
              have hkkvs : k ∈ kvs.map (·.1) := mem_fst_of_lookup hyk
              have hckvs : (kvs.map (·.1)).contains k = true := contains_of_mem hkkvs
              have hnodef : k ∉ (fbDefaults (kvs.map (·.1)) sems).map (·.1) :=
                fbDefaults_not_mem hckvs
              have hfst₂ : es₂.map (·.1) =
                  (fbDefaults (kvs.map (·.1)) sems).map (·.1) :=
                traverse_fst encEntry_fst h₂
              have hnoes₂ : es₂.lookup k = none :=
                lookup_none_of_not_mem_fst (by rw [hfst₂]; exact hnodef)
              rw [lookup_append es₁ es₂ k] at hxk
              cases h₁k : es₁.lookup k with
              | none =>
                rw [h₁k, hnoes₂] at hxk
                exact nomatch hxk
              | some x' =>
                rw [h₁k] at hxk
                replace hxk : some x' = some x := hxk
                cases hxk
                cases hknk : kn k with
                | false =>
                  have hfst₁ : es₁.map (·.1) = ds.map (·.1) :=
                    traverse_fst encEntry_fst h₁
                  have hdsf : ds.map (·.1) =
                      (kvs.filter fun kv => kn kv.1).map (·.1) :=
                    traverse_fst decEntry_fst htr
                  have hnone : es₁.lookup k = none := by
                    refine lookup_none_of_not_mem_fst ?_
                    rw [hfst₁, hdsf]
                    intro hmm
                    have h1 := lookup_isSome_of_mem_fst hmm
                    rw [lookup_filter_neg hknk kvs] at h1
                    exact nomatch h1
                  rw [hnone] at h₁k
                  exact nomatch h₁k
                | true =>
                  have hflt : (kvs.filter fun kv => kn kv.1).lookup k = some y := by
                    rw [lookup_filter_pos hknk kvs]
                    exact hyk
                  have hzip := traverse_rel
                    (g := decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
                    (f := encEntry (fun k => sems.lookup k) (rc?.map (·.e)))
                    (R := fun q r => q.1 = r.1 ∧ Agree q.2 r.2)
                    (fun y' x' z' hg hf' => objStep_agree hf hrc y' x' z' hg hf')
                    (kvs.filter fun kv => kn kv.1) ds es₁ htr h₁
                  have hlen : es₁.length = (kvs.filter fun kv => kn kv.1).length := by
                    have l1 := traverse_length (kvs.filter fun kv => kn kv.1) ds htr
                    have l2 := traverse_length ds es₁ h₁
                    omega
                  exact lookup_rel es₁ (kvs.filter fun kv => kn kv.1) hlen
                    (fun q hq => hzip q hq) k x y h₁k hflt
    all_goals exact nomatch hp

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

/-- The sum, from (U): both directions route through the same option. -/
theorem lawfulCore_altCodec {os : List OptionSem} {μA : Option Member}
    (h : ∀ o ∈ os, LawfulCore o.c) (hU : UniqueAdmission os)
    (hW : ∀ m, μA = some m → ∀ o ∈ os, ∀ t a, o.c.e t = some a → a.member = m) :
    LawfulCore (altCodec os μA) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t a he
    simp only [altCodec] at he ⊢
    cases hf : os.filter (·.admitV t) with
    | nil => rw [hf] at he; exact nomatch he
    | cons o tl =>
      cases tl with
      | cons _ _ => rw [hf] at he; exact nomatch he
      | nil =>
        rw [hf] at he
        replace he : o.c.e t = some a := he
        have hom : o ∈ os.filter (·.admitV t) := by
          rw [hf]; exact List.mem_cons_self o []
        have ho : o ∈ os := (List.mem_filter.mp hom).1
        obtain ⟨hA, hV⟩ := hU o ho t a he
        rw [hA]
        exact (h o ho).retract he
  · intro a t hp
    simp only [altCodec] at hp ⊢
    cases hf : os.filter (·.admitA a) with
    | nil => rw [hf] at hp; exact nomatch hp
    | cons o tl =>
      cases tl with
      | cons _ _ => rw [hf] at hp; exact nomatch hp
      | nil =>
        rw [hf] at hp
        replace hp : o.c.p a = some t := hp
        have hom : o ∈ os.filter (·.admitA a) := by
          rw [hf]; exact List.mem_cons_self o []
        have ho : o ∈ os := (List.mem_filter.mp hom).1
        obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ((h o ho).canon hp)
        obtain ⟨hA, hV⟩ := hU o ho t a' ha'
        rw [hV]
        show (o.c.e t).isSome
        rw [ha']
        rfl
  · intro μ hμ t a he
    simp only [altCodec] at hμ he
    cases hf : os.filter (·.admitV t) with
    | nil => rw [hf] at he; exact nomatch he
    | cons o tl =>
      cases tl with
      | cons _ _ => rw [hf] at he; exact nomatch he
      | nil =>
        rw [hf] at he
        replace he : o.c.e t = some a := he
        have hom : o ∈ os.filter (·.admitV t) := by
          rw [hf]; exact List.mem_cons_self o []
        have ho : o ∈ os := (List.mem_filter.mp hom).1
        exact hW μ hμ o ho t a he

theorem lawful_altCodec {os : List OptionSem} {μA : Option Member}
    (h : ∀ o ∈ os, Lawful o.c) (hU : UniqueAdmission os)
    (hW : ∀ m, μA = some m → ∀ o ∈ os, ∀ t a, o.c.e t = some a → a.member = m) :
    Lawful (altCodec os μA) := by
  have hcore := lawfulCore_altCodec (fun o ho => (h o ho).core) hU hW
  refine ⟨hcore.retract, hcore.canon, hcore.writes, ?_⟩
  intro a t a' hp he
  simp only [altCodec] at hp he
  cases hf : os.filter (·.admitA a) with
  | nil => rw [hf] at hp; exact nomatch hp
  | cons o tl =>
    cases tl with
    | cons _ _ => rw [hf] at hp; exact nomatch hp
    | nil =>
      rw [hf] at hp
      replace hp : o.c.p a = some t := hp
      have hom : o ∈ os.filter (·.admitA a) := by
        rw [hf]; exact List.mem_cons_self o []
      have ho : o ∈ os := (List.mem_filter.mp hom).1
      obtain ⟨a'', ha''⟩ := Option.isSome_iff_exists.mp ((h o ho).canon hp)
      obtain ⟨hA, hV⟩ := hU o ho t a'' ha''
      rw [hV] at he
      replace he : o.c.e t = some a' := he
      exact (h o ho).agree hp he

theorem filter_map_comm {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ l : List α, (l.map f).filter p = (l.filter fun x => p (f x)).map f
  | [] => rfl
  | x :: l => by
      cases hp : p (f x) with
      | true =>
        simp only [List.map, List.filter, hp]
        rw [filter_map_comm f p l]
      | false =>
        simp only [List.map, List.filter, hp]
        exact filter_map_comm f p l

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
  intro o' ho' t a he
  simp only [List.mem_map] at ho'
  obtain ⟨x, hx, rfl⟩ := ho'
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

/-- `(dunion)` soundness is a corollary: the sum lemma composed with its (U) theorem;
    the member law comes from the stamp itself — a stamped canonical attribute is an
    `M`. -/
theorem lawful_dunionCodec {d : Name} {os : List (List String × Codec)}
    (h : ∀ o ∈ os, Lawful o.2)
    (hstamp : ∀ o ∈ os, ∀ t a, o.2.e t = some a →
      ∃ tag ∈ o.1, (∃ kvs, a = .m kvs ∧ kvs.lookup d = some (.s tag)) ∧
        (∃ kvs, t = .map kvs ∧ kvs.lookup d = some (.str tag)))
    (hdisj : List.Pairwise (fun x y => ∀ tag ∈ x.1, tag ∉ y.1) os) :
    Lawful (dunionCodec d os) := by
  refine lawful_altCodec ?_ (uniqueAdmission_byTag hstamp hdisj) ?_
  · intro o ho
    simp only [List.mem_map] at ho
    obtain ⟨x, hx, rfl⟩ := ho
    exact h x hx
  · intro m hm o ho t a he
    cases hm
    simp only [List.mem_map] at ho
    obtain ⟨x, hx, rfl⟩ := ho
    replace he : x.2.e t = some a := he
    obtain ⟨tag, htag, ⟨kvs, rfl, hlook⟩, -⟩ := hstamp x hx t a he
    rfl

/-- `opaque` closes with no bespoke induction: the sum lemma, its options' lemmas, and
    shape-computed unique admission — kinds partition the values, members the
    attributes. -/
theorem lawful_opaqCodec : ∀ (fuel : Nat) (lossy : Bool), Lawful (opaqCodec fuel lossy)
  | 0, _ => Lawful.empty
  | fuel+1, lossy => by
    have hop : Lawful (opaqCodec fuel lossy) := lawful_opaqCodec fuel lossy
    have hset : Lawful (setCodec (opaqCodec fuel lossy)) := lawful_setCodec hop
    have harr : Lawful (arrayCodec (opaqCodec fuel lossy)) := lawful_arrayCodec hop
    have hrec : Lawful (recordCodec (opaqCodec fuel lossy)) := lawful_recordCodec hop
    refine lawful_altCodec ?_ ?_ (fun m hm => nomatch hm)
    · intro o ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
      · exact lawful_stringCodec
      · exact lawful_booleanCodec
      · exact lawful_binaryCodec
      · exact lawful_nullCodec
      · cases lossy with
        | true => exact lawful_numberCodec
        | false => exact Lawful.empty
      · exact hset
      · exact harr
      · exact hrec
      · exact absurd h (by simp)
    · intro o ho t a he
      simp only [List.mem_cons] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hmem
      -- string
      · replace he : stringCodec.e t = some a := he
        cases t
        case str s =>
          replace he : some (Attr.s s) = some a := he
          cases he
          have hnp : (if lossy then numberCodec else Codec.empty).p (Attr.s s) = none := by
            cases lossy <;> rfl
          have hne : (if lossy then numberCodec else Codec.empty).e (Value.str s) = none := by
            cases lossy <;> rfl
          constructor
          · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
              binaryCodec, nullCodec, setCodec, arrayCodec, recordCodec, hnp]
          · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
              binaryCodec, nullCodec, setCodec, arrayCodec, recordCodec, hne]
        all_goals exact nomatch he
      -- boolean
      · replace he : booleanCodec.e t = some a := he
        cases t
        case bool b =>
          replace he : some (Attr.bool b) = some a := he
          cases he
          have hnp : (if lossy then numberCodec else Codec.empty).p (Attr.bool b) = none := by
            cases lossy <;> rfl
          have hne : (if lossy then numberCodec else Codec.empty).e (Value.bool b) = none := by
            cases lossy <;> rfl
          constructor
          · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
              binaryCodec, nullCodec, setCodec, arrayCodec, recordCodec, hnp]
          · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
              binaryCodec, nullCodec, setCodec, arrayCodec, recordCodec, hne]
        all_goals exact nomatch he
      -- binary
      · replace he : binaryCodec.e t = some a := he
        cases t
        case bin b =>
          replace he : some (Attr.b b) = some a := he
          cases he
          have hnp : (if lossy then numberCodec else Codec.empty).p (Attr.b b) = none := by
            cases lossy <;> rfl
          have hne : (if lossy then numberCodec else Codec.empty).e (Value.bin b) = none := by
            cases lossy <;> rfl
          constructor
          · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
              binaryCodec, nullCodec, setCodec, arrayCodec, recordCodec, hnp]
          · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
              binaryCodec, nullCodec, setCodec, arrayCodec, recordCodec, hne]
        all_goals exact nomatch he
      -- null
      · replace he : nullCodec.e t = some a := he
        cases t
        case null =>
          replace he : some Attr.null = some a := he
          cases he
          have hnp : (if lossy then numberCodec else Codec.empty).p Attr.null = none := by
            cases lossy <;> rfl
          have hne : (if lossy then numberCodec else Codec.empty).e Value.null = none := by
            cases lossy <;> rfl
          constructor
          · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
              binaryCodec, nullCodec, setCodec, arrayCodec, recordCodec, hnp]
          · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
              binaryCodec, nullCodec, setCodec, arrayCodec, recordCodec, hne]
        all_goals exact nomatch he
      -- the number option
      · cases lossy with
        | false => exact nomatch he
        | true =>
          replace he : numberCodec.e t = some a := he
          cases t
          case num d =>
            replace he : some (Attr.n d.toDec) = some a := he
            cases he
            constructor
            · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
                binaryCodec, nullCodec, numberCodec, setCodec, arrayCodec,
                recordCodec, Double.roundtrip]
            · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
                binaryCodec, nullCodec, numberCodec, setCodec, arrayCodec,
                recordCodec]
          all_goals exact nomatch he
      -- set
      · replace he : (setCodec (opaqCodec fuel lossy)).e t = some a := he
        cases t
        case set vs =>
          replace he : (traverse (opaqCodec fuel lossy).e vs).bind asWireSet = some a := he
          cases htr : traverse (opaqCodec fuel lossy).e vs with
          | none => rw [htr] at he; exact nomatch he
          | some as =>
            rw [htr] at he
            replace he : asWireSet as = some a := he
            have hetotal : (setCodec (opaqCodec fuel lossy)).e (Value.set vs) = some a := by
              show (traverse (opaqCodec fuel lossy).e vs).bind asWireSet = some a
              rw [htr]
              exact he
            have hpa := hset.retract hetotal
            obtain ⟨hne', hcase⟩ := asWireSet_cases he
            have hnev : (if lossy then numberCodec else Codec.empty).e (Value.set vs) = none := by
              cases lossy <;> rfl
            rcases hcase with ⟨ss, rfl, rfl⟩ | ⟨ns, rfl, rfl⟩ | ⟨bs, rfl, rfl⟩
            · have hnp : (if lossy then numberCodec else Codec.empty).p (Attr.ss ss) = none := by
                cases lossy <;> rfl
              constructor
              · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
                  binaryCodec, nullCodec, arrayCodec, recordCodec, hnp, hpa]
              · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
                  binaryCodec, nullCodec, arrayCodec, recordCodec, hnev, hetotal]
            · have hnp : (if lossy then numberCodec else Codec.empty).p (Attr.ns ns) = none := by
                cases lossy <;> rfl
              constructor
              · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
                  binaryCodec, nullCodec, arrayCodec, recordCodec, hnp, hpa]
              · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
                  binaryCodec, nullCodec, arrayCodec, recordCodec, hnev, hetotal]
            · have hnp : (if lossy then numberCodec else Codec.empty).p (Attr.bs bs) = none := by
                cases lossy <;> rfl
              constructor
              · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
                  binaryCodec, nullCodec, arrayCodec, recordCodec, hnp, hpa]
              · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
                  binaryCodec, nullCodec, arrayCodec, recordCodec, hnev, hetotal]
        all_goals exact nomatch he
      -- array
      · replace he : (arrayCodec (opaqCodec fuel lossy)).e t = some a := he
        cases t
        case arr vs =>
          replace he : (traverse (opaqCodec fuel lossy).e vs).map Attr.l = some a := he
          cases htr : traverse (opaqCodec fuel lossy).e vs with
          | none => rw [htr] at he; exact nomatch he
          | some as =>
            rw [htr] at he
            replace he : some (Attr.l as) = some a := he
            cases he
            have hetotal : (arrayCodec (opaqCodec fuel lossy)).e (Value.arr vs) =
                some (Attr.l as) := by
              show (traverse (opaqCodec fuel lossy).e vs).map Attr.l = some (Attr.l as)
              rw [htr]
              rfl
            have hpa := harr.retract hetotal
            have hnp : (if lossy then numberCodec else Codec.empty).p (Attr.l as) = none := by
              cases lossy <;> rfl
            have hnev : (if lossy then numberCodec else Codec.empty).e (Value.arr vs) = none := by
              cases lossy <;> rfl
            constructor
            · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
                binaryCodec, nullCodec, setCodec, recordCodec, hnp, hpa]
            · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
                binaryCodec, nullCodec, setCodec, recordCodec, hnev, hetotal]
        all_goals exact nomatch he
      -- record
      · replace he : (recordCodec (opaqCodec fuel lossy)).e t = some a := he
        cases t
        case map kvs =>
          replace he : (traverse (encPair (opaqCodec fuel lossy)) kvs).map Attr.m =
            some a := he
          cases htr : traverse (encPair (opaqCodec fuel lossy)) kvs with
          | none => rw [htr] at he; exact nomatch he
          | some ds =>
            rw [htr] at he
            replace he : some (Attr.m ds) = some a := he
            cases he
            have hetotal : (recordCodec (opaqCodec fuel lossy)).e (Value.map kvs) =
                some (Attr.m ds) := by
              show (traverse (encPair (opaqCodec fuel lossy)) kvs).map Attr.m =
                some (Attr.m ds)
              rw [htr]
              rfl
            have hpa := hrec.retract hetotal
            have hnp : (if lossy then numberCodec else Codec.empty).p (Attr.m ds) = none := by
              cases lossy <;> rfl
            have hnev : (if lossy then numberCodec else Codec.empty).e (Value.map kvs) = none := by
              cases lossy <;> rfl
            constructor
            · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
                binaryCodec, nullCodec, setCodec, arrayCodec, hnp, hpa]
            · simp [OptionSem.byAttempt, List.filter, stringCodec, booleanCodec,
                binaryCodec, nullCodec, setCodec, arrayCodec, hnev, hetotal]
        all_goals exact nomatch he
      · exact absurd hmem (by simp)

/-! ## Core variants: (R), (C), (W) through `legacy`-containing subterms

The wrappers' and uniform products' core lemmas live beside their full counterparts
above; what remains here are the composites whose core statements need their own
scaffolding. -/

/-- Canon-only cousin of `alignTraverse_master` — no member agreement demanded. -/
theorem alignTraverse_canon :
    ∀ (cs : List Codec) (tail : Option Codec),
      (∀ c ∈ cs, LawfulCore c) → (∀ c ∈ tail, LawfulCore c) →
      ∀ (as : List Attr) (cas : List (Codec × Attr)) (vs : List Value),
        align cs tail as = some cas →
        traverse (fun ca => ca.1.p ca.2) cas = some vs →
        ∃ cvs as', align cs tail vs = some cvs ∧
          traverse (fun cv => cv.1.e cv.2) cvs = some as'
  | [], _, _, _, [], cas, vs, hal, htr => by
      replace hal : some [] = some cas := hal
      cases hal
      replace htr : some [] = some vs := htr
      cases htr
      exact ⟨[], [], rfl, rfl⟩
  | [], tail, h, ht, a :: as, cas, vs, hal, htr => by
      cases tail with
      | none => exact nomatch hal
      | some c =>
        replace hal : (align [] (some c) as).map ((c, a) :: ·) = some cas := hal
        cases has : align [] (some c) as with
        | none => rw [has] at hal; exact nomatch hal
        | some cas' =>
          rw [has] at hal
          replace hal : some ((c, a) :: cas') = some cas := hal
          cases hal
          simp only [traverse] at htr
          cases hpa : c.p a with
          | none => rw [hpa] at htr; exact nomatch htr
          | some v =>
            rw [hpa] at htr
            cases htr' : traverse (fun ca : Codec × Attr => ca.1.p ca.2) cas' with
            | none => rw [htr'] at htr; exact nomatch htr
            | some vs' =>
              rw [htr'] at htr
              replace htr : some (v :: vs') = some vs := htr
              cases htr
              have hc : LawfulCore c := ht c rfl
              obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp (hc.canon hpa)
              obtain ⟨cvs', as'', hal', htr''⟩ :=
                alignTraverse_canon [] (some c) h ht as cas' vs' has htr'
              refine ⟨(c, v) :: cvs', a₀ :: as'', ?_, ?_⟩
              · show (align [] (some c) vs').map ((c, v) :: ·) = _
                rw [hal']
                rfl
              · simp only [traverse]
                rw [ha₀, htr'']
  | _ :: _, _, _, _, [], _, _, hal, _ => nomatch hal
  | c :: cs, tail, h, ht, a :: as, cas, vs, hal, htr => by
      replace hal : (align cs tail as).map ((c, a) :: ·) = some cas := hal
      cases has : align cs tail as with
      | none => rw [has] at hal; exact nomatch hal
      | some cas' =>
        rw [has] at hal
        replace hal : some ((c, a) :: cas') = some cas := hal
        cases hal
        simp only [traverse] at htr
        cases hpa : c.p a with
        | none => rw [hpa] at htr; exact nomatch htr
        | some v =>
          rw [hpa] at htr
          cases htr' : traverse (fun ca : Codec × Attr => ca.1.p ca.2) cas' with
          | none => rw [htr'] at htr; exact nomatch htr
          | some vs' =>
            rw [htr'] at htr
            replace htr : some (v :: vs') = some vs := htr
            cases htr
            have hc : LawfulCore c := h c (List.mem_cons_self c cs)
            obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp (hc.canon hpa)
            obtain ⟨cvs', as'', hal', htr''⟩ :=
              alignTraverse_canon cs tail
                (fun c' hc' => h c' (List.mem_cons_of_mem c hc')) ht as cas' vs' has htr'
            refine ⟨(c, v) :: cvs', a₀ :: as'', ?_, ?_⟩
            · show (align cs tail vs').map ((c, v) :: ·) = _
              rw [hal']
              rfl
            · simp only [traverse]
              rw [ha₀, htr'']

theorem lawfulCore_tupleCodec {cs : List Codec} {tail : Option Codec}
    (hcs : ∀ c ∈ cs, LawfulCore c) (ht : ∀ c ∈ tail, LawfulCore c) :
    LawfulCore (tupleCodec cs tail) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t a he
    cases t
    case arr vs =>
      replace he : ((align cs tail vs).bind
        (traverse fun cv => cv.1.e cv.2)).map Attr.l = some a := he
      cases hal : align cs tail vs with
      | none => rw [hal] at he; exact nomatch he
      | some cvs =>
        rw [hal] at he
        replace he : (traverse (fun cv : Codec × Value => cv.1.e cv.2) cvs).map
          Attr.l = some a := he
        cases htr : traverse (fun cv : Codec × Value => cv.1.e cv.2) cvs with
        | none => rw [htr] at he; exact nomatch he
        | some as =>
          rw [htr] at he
          replace he : some (Attr.l as) = some a := he
          cases he
          show ((align cs tail as).bind
            (traverse fun ca => ca.1.p ca.2)).map Value.arr = some (.arr vs)
          rw [alignTraverse_roundTrip cs tail hcs ht vs cvs as hal htr]
          rfl
    all_goals exact nomatch he
  · intro a t hp
    cases a
    case l as =>
      replace hp : ((align cs tail as).bind
        (traverse fun ca => ca.1.p ca.2)).map Value.arr = some t := hp
      cases hal : align cs tail as with
      | none => rw [hal] at hp; exact nomatch hp
      | some cas =>
        rw [hal] at hp
        replace hp : (traverse (fun ca : Codec × Attr => ca.1.p ca.2) cas).map
          Value.arr = some t := hp
        cases htr : traverse (fun ca : Codec × Attr => ca.1.p ca.2) cas with
        | none => rw [htr] at hp; exact nomatch hp
        | some vs =>
          rw [htr] at hp
          replace hp : some (Value.arr vs) = some t := hp
          cases hp
          obtain ⟨cvs, as', hal', htr'⟩ :=
            alignTraverse_canon cs tail hcs ht as cas vs hal htr
          show (((align cs tail vs).bind
            (traverse fun cv => cv.1.e cv.2)).map Attr.l).isSome
          rw [hal']
          show ((traverse (fun cv : Codec × Value => cv.1.e cv.2) cvs).map
            Attr.l).isSome
          rw [htr']
          rfl
    all_goals exact nomatch hp
  · intro μ hμ t a he
    replace hμ : some Member.L = some μ := hμ
    cases hμ
    cases t
    case arr vs =>
      replace he : ((align cs tail vs).bind
        (traverse fun cv => cv.1.e cv.2)).map Attr.l = some a := he
      cases hal : align cs tail vs with
      | none => rw [hal] at he; exact nomatch he
      | some cvs =>
        rw [hal] at he
        replace he : (traverse (fun cv : Codec × Value => cv.1.e cv.2) cvs).map
          Attr.l = some a := he
        cases htr : traverse (fun cv : Codec × Value => cv.1.e cv.2) cvs with
        | none => rw [htr] at he; exact nomatch he
        | some as =>
          rw [htr] at he
          replace he : some (Attr.l as) = some a := he
          cases he
          rfl
    all_goals exact nomatch he

/-- Core set: the member-uniformity that (MP) supplied comes from (W) instead, so the
    element's named member is a hypothesis — exactly the `(set)` rule's premise. -/
theorem lawfulCore_setCodec {c : Codec} {μ₀ μS : Member} (h : LawfulCore c)
    (hμ : c.μ = some μ₀) (hsm : setMember μ₀ = some μS) :
    LawfulCore (setCodec c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t a he
    cases t
    case set vs =>
      replace he : (traverse c.e vs).bind asWireSet = some a := he
      cases htr : traverse c.e vs with
      | none => rw [htr] at he; exact nomatch he
      | some as =>
        rw [htr] at he
        replace he : asWireSet as = some a := he
        obtain ⟨hne, hcase⟩ := asWireSet_cases he
        rcases hcase with ⟨ss, rfl, rfl⟩ | ⟨ns, rfl, rfl⟩ | ⟨bs, rfl, rfl⟩
        · have h1 := traverse_roundTrip (fun _ _ hxy => h.retract hxy)
            vs (ss.map Attr.s) htr
          rw [traverse_map] at h1
          cases ss with
          | nil => exact absurd rfl hne
          | cons s ss' =>
            show (traverse (fun s => c.p (.s s)) (s :: ss')).map Value.set =
              some (.set vs)
            rw [h1]
            rfl
        · have h1 := traverse_roundTrip (fun _ _ hxy => h.retract hxy)
            vs (ns.map Attr.n) htr
          rw [traverse_map] at h1
          cases ns with
          | nil => exact absurd rfl hne
          | cons n ns' =>
            show (traverse (fun x => c.p (.n x)) (n :: ns')).map Value.set =
              some (.set vs)
            rw [h1]
            rfl
        · have h1 := traverse_roundTrip (fun _ _ hxy => h.retract hxy)
            vs (bs.map Attr.b) htr
          rw [traverse_map] at h1
          cases bs with
          | nil => exact absurd rfl hne
          | cons b bs' =>
            show (traverse (fun x => c.p (.b x)) (b :: bs')).map Value.set =
              some (.set vs)
            rw [h1]
            rfl
    all_goals exact nomatch he
  · intro a t hp
    have hbranch : ∀ (ws : List Value), traverse c.e ws ≠ none →
        ∀ as', traverse c.e ws = some as' → ws ≠ [] →
        ((traverse c.e ws).bind asWireSet).isSome = true := by
      intro ws _ as' has' hws
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
          simp only [asWireSet]
          rw [hss']
          rfl
        case N =>
          obtain ⟨ns', hns'⟩ := numPayloads_isSome hmem
          cases x
          case n v =>
            simp only [asWireSet, strPayloads]
            rw [hns']
            rfl
          all_goals exact nomatch hx
        case B =>
          obtain ⟨bs', hbs'⟩ := binPayloads_isSome hmem
          cases x
          case b v =>
            simp only [asWireSet, strPayloads, numPayloads]
            rw [hbs']
            rfl
          all_goals exact nomatch hx
        all_goals exact nomatch hsm
    cases a
    case ss vs' =>
      cases vs' with
      | nil => exact nomatch hp
      | cons s rest =>
        replace hp : (traverse (fun s => c.p (.s s)) (s :: rest)).map Value.set =
          some t := hp
        cases htr : traverse (fun s => c.p (Attr.s s)) (s :: rest) with
        | none => rw [htr] at hp; exact nomatch hp
        | some ws =>
          rw [htr] at hp
          replace hp : some (Value.set ws) = some t := hp
          cases hp
          obtain ⟨as', has'⟩ := Option.isSome_iff_exists.mp
            (traverse_isSome (f := c.e) (fun _ _ hyx => h.canon hyx)
              (s :: rest) ws htr)
          have hws : ws ≠ [] := by
            intro h0
            have hlen := traverse_length (s :: rest) ws htr
            rw [h0] at hlen
            exact nomatch hlen
          exact hbranch ws (by rw [has']; exact nofun) as' has' hws
    case ns vs' =>
      cases vs' with
      | nil => exact nomatch hp
      | cons n rest =>
        replace hp : (traverse (fun x => c.p (.n x)) (n :: rest)).map Value.set =
          some t := hp
        cases htr : traverse (fun x => c.p (Attr.n x)) (n :: rest) with
        | none => rw [htr] at hp; exact nomatch hp
        | some ws =>
          rw [htr] at hp
          replace hp : some (Value.set ws) = some t := hp
          cases hp
          obtain ⟨as', has'⟩ := Option.isSome_iff_exists.mp
            (traverse_isSome (f := c.e) (fun _ _ hyx => h.canon hyx)
              (n :: rest) ws htr)
          have hws : ws ≠ [] := by
            intro h0
            have hlen := traverse_length (n :: rest) ws htr
            rw [h0] at hlen
            exact nomatch hlen
          exact hbranch ws (by rw [has']; exact nofun) as' has' hws
    case bs vs' =>
      cases vs' with
      | nil => exact nomatch hp
      | cons b rest =>
        replace hp : (traverse (fun x => c.p (.b x)) (b :: rest)).map Value.set =
          some t := hp
        cases htr : traverse (fun x => c.p (Attr.b x)) (b :: rest) with
        | none => rw [htr] at hp; exact nomatch hp
        | some ws =>
          rw [htr] at hp
          replace hp : some (Value.set ws) = some t := hp
          cases hp
          obtain ⟨as', has'⟩ := Option.isSome_iff_exists.mp
            (traverse_isSome (f := c.e) (fun _ _ hyx => h.canon hyx)
              (b :: rest) ws htr)
          have hws : ws ≠ [] := by
            intro h0
            have hlen := traverse_length (b :: rest) ws htr
            rw [h0] at hlen
            exact nomatch hlen
          exact hbranch ws (by rw [has']; exact nofun) as' has' hws
    all_goals exact nomatch hp
  · intro μ hμ' t a he
    replace hμ' : (c.μ.bind setMember) = some μ := hμ'
    rw [hμ] at hμ'
    replace hμ' : setMember μ₀ = some μ := hμ'
    cases t
    case set vs =>
      replace he : (traverse c.e vs).bind asWireSet = some a := he
      cases htr : traverse c.e vs with
      | none => rw [htr] at he; exact nomatch he
      | some as =>
        rw [htr] at he
        replace he : asWireSet as = some a := he
        obtain ⟨hne, hcase⟩ := asWireSet_cases he
        have hmem := traverse_mem (P := fun y => y.member = μ₀)
          (fun _ y hxy => h.writes hμ hxy) htr
        rcases hcase with ⟨ss, rfl, rfl⟩ | ⟨ns, rfl, rfl⟩ | ⟨bs, rfl, rfl⟩
        · cases ss with
          | nil => exact absurd rfl hne
          | cons s ss' =>
            have hm := hmem (Attr.s s) (List.mem_cons_self _ _)
            replace hm : Member.S = μ₀ := hm
            cases hm
            replace hμ' : some Member.SS = some μ := hμ'
            cases hμ'
            rfl
        · cases ns with
          | nil => exact absurd rfl hne
          | cons n ns' =>
            have hm := hmem (Attr.n n) (List.mem_cons_self _ _)
            replace hm : Member.N = μ₀ := hm
            cases hm
            replace hμ' : some Member.NS = some μ := hμ'
            cases hμ'
            rfl
        · cases bs with
          | nil => exact absurd rfl hne
          | cons b bs' =>
            have hm := hmem (Attr.b b) (List.mem_cons_self _ _)
            replace hm : Member.B = μ₀ := hm
            cases hm
            replace hμ' : some Member.BS = some μ := hμ'
            cases hμ'
            rfl
    all_goals exact nomatch he

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
    LawfulCore (objectCodecCore sems rc? kn) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t a he
    obtain ⟨kvs, ds, rfl, rfl, hval, htr⟩ := objectCodecCore_e_inv he
    have hnames : ds.map (·.1) = kvs.map (·.1) := traverse_fst encEntry_fst htr
    have hreq : reqPresentB sems (ds.map (·.1)) = true := by
      rw [hnames]
      exact reqPresentB_of fun k c hm =>
        valPresentB_spec hval hm (fun _ h' => nomatch h')
    have hkeep : ds.filter (fun kv => kn kv.1) = ds :=
      filter_eq_self_of_all fun d hd => by
        obtain ⟨kv, _, hkv⟩ := traverse_mem₂ htr d hd
        exact hknE kv d hkv
    have hfbnil : fbDefaults (ds.map (·.1)) sems = [] := by
      rw [hnames]
      exact fbDefaults_nil fun k c v hm =>
        valPresentB_spec hval hm (fun _ h' => nomatch h')
    have hdec := traverse_roundTrip (objStep_rt hf hrc) kvs ds htr
    show (if reqPresentB sems (ds.map (·.1)) = true then
        (traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
          (ds.filter fun kv => kn kv.1)).map fun ds' =>
            Value.map (ds' ++ fbDefaults (ds.map (·.1)) sems)
      else none) = some (.map kvs)
    rw [hreq, hkeep, hdec, hfbnil]
    simp only [List.append_nil]
    rfl
  · intro a t hp
    cases a
    case m kvs =>
      replace hp : (if reqPresentB sems (kvs.map (·.1)) = true then
          (traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
            (kvs.filter fun kv => kn kv.1)).map fun ds =>
              Value.map (ds ++ fbDefaults (kvs.map (·.1)) sems)
        else none) = some t := hp
      cases hreq : reqPresentB sems (kvs.map (·.1)) with
      | false => rw [hreq] at hp; exact nomatch hp
      | true =>
        rw [hreq] at hp
        replace hp : (traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
            (kvs.filter fun kv => kn kv.1)).map (fun ds =>
              Value.map (ds ++ fbDefaults (kvs.map (·.1)) sems)) = some t := hp
        cases htr : traverse (decEntry (fun k => sems.lookup k) (rc?.map (·.p)))
            (kvs.filter fun kv => kn kv.1) with
        | none => rw [htr] at hp; exact nomatch hp
        | some ds =>
          rw [htr] at hp
          replace hp : some (Value.map (ds ++ fbDefaults (kvs.map (·.1)) sems)) =
            some t := hp
          cases hp
          have hds := traverse_isSome
            (f := encEntry (fun k => sems.lookup k) (rc?.map (·.e)))
            (objStep_canon hf hrc) (kvs.filter fun kv => kn kv.1) ds htr
          obtain ⟨es₁, hes₁⟩ := Option.isSome_iff_exists.mp hds
          have hdefs : ∀ x ∈ fbDefaults (kvs.map (·.1)) sems,
              ((encEntry (fun k => sems.lookup k) (rc?.map (·.e))) x).isSome = true := by
            intro ⟨k', v'⟩ hx
            obtain ⟨c, hmem, hcf⟩ := fbDefaults_spec hx
            have hlk : sems.lookup k' = some (.fb c v') := lookup_eq_of_mem_nodup hnd hmem
            simp only [encEntry]
            rw [hlk]
            show ((c.e v').map ((k', ·))).isSome = true
            obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
              (hfb (k', .fb c v') hmem c v' rfl)
            rw [ha']
            rfl
          obtain ⟨es₂, hes₂⟩ := Option.isSome_iff_exists.mp
            (traverse_isSome_of_all hdefs)
          have hall := traverse_append hes₁ hes₂
          have hnames : ds.map (·.1) = (kvs.filter fun kv => kn kv.1).map (·.1) :=
            traverse_fst decEntry_fst htr
          have hval : valPresentB sems
              ((ds ++ fbDefaults (kvs.map (·.1)) sems).map (·.1)) = true := by
            refine valPresentB_of fun k fs hm hno => ?_
            rw [List.map_append]
            cases hck : (kvs.map (·.1)).contains k with
            | true =>
              have hkmem : k ∈ kvs.map (·.1) := mem_of_contains hck
              obtain ⟨ax, haxm⟩ := exists_of_mem_fst hkmem
              have hknk : kn k = true := hknDecl k (lookup_isSome_of_mem_fst
                (List.mem_map.mpr ⟨(k, fs), hm, rfl⟩))
              have hkeepm : (k, ax) ∈ kvs.filter fun kv => kn kv.1 :=
                List.mem_filter.mpr ⟨haxm, hknk⟩
              have hkfl : k ∈ (kvs.filter fun kv => kn kv.1).map (·.1) :=
                List.mem_map.mpr ⟨(k, ax), hkeepm, rfl⟩
              rw [← hnames] at hkfl
              exact contains_of_mem (List.mem_append.mpr (Or.inl hkfl))
            | false =>
              cases fs with
              | opt c => exact absurd rfl (hno c)
              | req c => rw [reqPresentB_spec hreq hm] at hck; exact nomatch hck
              | fb c v =>
                have hin := mem_fbDefaults hm hck
                exact contains_of_mem (List.mem_append.mpr (Or.inr
                  (List.mem_map.mpr ⟨(k, v), hin, rfl⟩)))
          show (if valPresentB sems
              ((ds ++ fbDefaults (kvs.map (·.1)) sems).map (·.1)) = true then
              (traverse (encEntry (fun k => sems.lookup k) (rc?.map (·.e)))
                (ds ++ fbDefaults (kvs.map (·.1)) sems)).map Attr.m
            else none).isSome = true
          rw [hval, hall]
          rfl
    all_goals exact nomatch hp
  · intro μ hμ t a he
    replace hμ : some Member.M = some μ := hμ
    cases hμ
    obtain ⟨kvs, ds, rfl, rfl, hval, htr⟩ := objectCodecCore_e_inv he
    rfl

theorem lawfulCore_objectCodec {sems : List (Name × FieldSem)} {rest : RestSem}
    (hf : ∀ kf ∈ sems, LawfulCore kf.2.codec)
    (hfb : ∀ kf ∈ sems, ∀ c v, kf.2 = .fb c v → (c.e v).isSome)
    (hnd : (sems.map (·.1)).Nodup)
    (hrest : ∀ c, rest = .codec c → LawfulCore c) :
    LawfulCore (objectCodec sems rest) :=
  lawfulCore_objectCore sems (rcOf rest) (keepB rest sems) hf hfb hnd
    (rcOf_forall hrest) keepB_of_encEntry keepB_of_declared

/-- Core `(dunion)`: the same corollary, with core options. -/
theorem lawfulCore_dunionCodec {d : Name} {os : List (List String × Codec)}
    (h : ∀ o ∈ os, LawfulCore o.2)
    (hstamp : ∀ o ∈ os, ∀ t a, o.2.e t = some a →
      ∃ tag ∈ o.1, (∃ kvs, a = .m kvs ∧ kvs.lookup d = some (.s tag)) ∧
        (∃ kvs, t = .map kvs ∧ kvs.lookup d = some (.str tag)))
    (hdisj : List.Pairwise (fun x y => ∀ tag ∈ x.1, tag ∉ y.1) os) :
    LawfulCore (dunionCodec d os) := by
  refine lawfulCore_altCodec ?_ (uniqueAdmission_byTag hstamp hdisj) ?_
  · intro o ho
    simp only [List.mem_map] at ho
    obtain ⟨x, hx, rfl⟩ := ho
    exact h x hx
  · intro m hm o ho t a he
    cases hm
    simp only [List.mem_map] at ho
    obtain ⟨x, hx, rfl⟩ := ho
    replace he : x.2.e t = some a := he
    obtain ⟨tag, htag, ⟨kvs, rfl, hlook⟩, -⟩ := hstamp x hx t a he
    rfl

end

end Calculus
