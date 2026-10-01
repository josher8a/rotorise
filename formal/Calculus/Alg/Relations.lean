import Calculus.Alg.Combinators

/-!
# The order, the equivalence and compatibility, over any carriers

Three relations between two codecs: graph inclusion `Sub`, which is also the information order,
§6's `Codec.Equiv`, and the compatibility `Compat` that makes a union of lawful options lawful.
Each relation reads only the pair, the held set and the member, so each one takes the carrier `V`
and the members `M` as parameters.
-/

namespace Calculus.Alg

variable {V M : Type} {member : V → M}

/-! ## The order -/

/-- Graph inclusion of two codecs at each orientation: a restriction of `d` to the domains of
    `c`. -/
def Sub (c d : Codec V M) : Prop :=
  ∀ (o : Orient) (x : V) (y : V), c.f o x = some y → d.f o x = some y

/-- Inclusion from its two orientations. A proof that reads the asymmetric write and read of a
    combinator gives the two orientations apart. -/
theorem Sub.ofEP {c d : Codec V M} (he : ∀ v a, c.e v = some a → d.e v = some a)
    (hp : ∀ a v, c.p a = some v → d.p a = some v) : Sub c d :=
  Orient.both (P := fun o => ∀ x y, c.f o x = some y → d.f o x = some y) he hp

/-- **A two-sided restriction is below the codec that it restricts.** -/
theorem sub_refine2_self (c : Codec V M) (qV : V → Bool) (qA : V → Bool) :
    Sub (refine2 c qV qA) c :=
  fun _ _ _ h => (refine2_f.mp h).2.1

/-- **A restriction is below the codec that it restricts.** -/
theorem sub_restrict_self (c : Codec V M) (q : V → Bool) : Sub (c.restrict q) c :=
  sub_refine2_self c q _

/-- **Below one bound, the read domains decide the reads.** Three codecs below `u`, where the
    third reads exactly where both others read: there the three read the value of `u`. -/
theorem readAgree_of_sub {x y z u : Codec V M} (hx : Sub x u) (hy : Sub y u) (hz : Sub z u)
    (h1 : ∀ a, (z.p a).isSome = ((x.p a).isSome && (y.p a).isSome)) {a : V}
    (ha : (x.p a).isSome = true) (hb : (y.p a).isSome = true) :
    z.p a = x.p a ∧ z.p a = y.p a := by
  have hc : (z.p a).isSome = true := by rw [h1, ha, hb]; rfl
  have ez := (Option.some_get hc).symm.trans (hz .dual _ _ (Option.some_get hc).symm).symm
  exact ⟨ez.trans ((hx .dual _ _ (Option.some_get ha).symm).trans (Option.some_get ha)),
    ez.trans ((hy .dual _ _ (Option.some_get hb).symm).trans (Option.some_get hb))⟩

/-! ### The information order

`Sub` is the information order: the minimal requirement that any ccpo on codecs meets. The map
at each orientation grows from undefined, with `Codec.empty` at the bottom. -/

/-- A codec is below itself. -/
theorem sub_refl (c : Codec V M) : Sub c c := fun _ _ _ h => h

/-- The empty codec is below every codec: the bottom of the order, and what a staged definition
    starts from. -/
theorem sub_empty {u : Codec V M} : Sub Codec.empty u :=
  fun _ _ _ h => nomatch h

/-- The growing option, before unfolding: undefined everywhere. -/
def optBot : Codec V M := Codec.empty

/-- The stage `n` of the body `B`: `n` applications of `B` to `Codec.empty`. A structural
    recursion on `n`, so a stage at a numeral reduces by `rfl`. -/
def muStage (B : Codec V M → Codec V M) : Nat → Codec V M
  | 0 => .empty
  | n + 1 => B (muStage B n)

/-- A property that `Codec.empty` has and that each application of the body keeps holds at
    every stage. -/
theorem muStage_induct {B : Codec V M → Codec V M} {P : Codec V M → Prop} (h0 : P .empty)
    (hs : ∀ c, P c → P (B c)) : ∀ n, P (muStage B n)
  | 0 => h0
  | n + 1 => hs _ (muStage_induct h0 hs n)

/-- **`alternate reader` is a step up.** `extendRead` only ever adds readings — everything `c`
    decodes, the migration decodes the same way, and the writing half is untouched. §3's
    `(alternate reader)` coherence premise is what makes this an *extension* rather than a
    replacement, and this is that fact in the information order. -/
theorem sub_extendRead (c : Codec V M) (r : V → Option V) : Sub c (c.extendRead r) :=
  .ofEP (fun _ _ h => h) (fun _ _ h => by simp only [Codec.extendRead, Codec.ofEP_p, h])

/-! ### First-match resolution under the obligation

The definition takes the first admitter and never compares attributes, so no `DecidableEq`
on the attributes is needed. The obligation says that the choice did not matter, and
order-independence is recovered as a theorem. -/

/-- First-match resolution, value side. Total on the union of the options' domains. -/
def selectF (os : List (Codec V M)) (v : V) : Option V :=
  select os (·.e) v

/-- The obligation at one input: every admitter writes the same attribute. -/
def ConfluentAt (os : List (Codec V M)) (v : V) : Prop :=
  ∀ o ∈ os, ∀ o' ∈ os, (o.e v).isSome = true → (o'.e v).isSome = true → o.e v = o'.e v

/-- `selectF`, reduced at an admitting head. -/
theorem selectF_admit {o : Codec V M} {os : List (Codec V M)} {v : V}
    (h : (o.e v).isSome = true) : selectF (o :: os) v = o.e v := by
  simp [selectF, select, List.find?, h]

/-- …and at a non-admitting one. -/
theorem selectF_skip {o : Codec V M} {os : List (Codec V M)} {v : V}
    (h : (o.e v).isSome = false) : selectF (o :: os) v = selectF os v := by
  simp [selectF, select, List.find?, h]

/-- **Monotonicity.** Stated with the growing option first — the
    only position where growth can change the answer, since grown second the earlier admitter
    answers throughout. Confluence is used in exactly one of the three cases: where growth newly
    admits at a value another option was already answering. -/
theorem selectF_mono {o₁ o₁' o₂ : Codec V M} {v : V} {a : V}
    (hap : Sub o₁ o₁')
    (hc : ConfluentAt [o₁', o₂] v)
    (h : selectF [o₁, o₂] v = some a) : selectF [o₁', o₂] v = some a := by
  have hadm : (o₁.e v).isSome = true → (o₁'.e v).isSome = true := fun h1 =>
    let ⟨b, hb⟩ := Option.isSome_iff_exists.mp h1
    Option.isSome_iff_exists.mpr ⟨b, hap .host _ _ hb⟩
  cases h1' : (o₁'.e v).isSome with
  | false =>
    have h1 : (o₁.e v).isSome = false := by
      cases h1 : (o₁.e v).isSome with
      | true => rw [hadm h1] at h1'; exact nomatch h1'
      | false => rfl
    rw [selectF_skip h1']; rw [selectF_skip h1] at h; exact h
  | true =>
    cases h1 : (o₁.e v).isSome with
    | true => rw [selectF_admit h1']; rw [selectF_admit h1] at h; exact hap .host _ _ h
    | false =>
      rw [selectF_admit h1']; rw [selectF_skip h1] at h
      cases h2 : (o₂.e v).isSome with
      | false => rw [selectF_skip h2] at h; exact nomatch h
      | true =>
        rw [selectF_admit h2] at h
        rw [hc o₁' (by simp) o₂ (by simp) h1' h2]; exact h

/-- Directed continuity, stated **without constructing sups**: this file defines the order `Sub`
    and deliberately no ccpo. `oω` is an upper bound that is *least at `v`*: every answer
    it gives, some finite stage already gave. In the flat `Option` order that is the whole sup
    condition. -/
structure IsSupAt (f : Nat → Codec V M) (oω : Codec V M) (v : V) : Prop where
  /-- an upper bound of the chain -/
  ub : ∀ i, Sub (f i) oω
  /-- …and least at `v`: the limit adds no answer the chain did not have -/
  least : ∀ a, oω.e v = some a → ∃ i, (f i).e v = some a

/-- **Continuity — with the growing option first, needing no confluence.** That arrangement is
    load-bearing and the general case does not share it: see `selectF_continuous_list`, which
    takes the obligation at each stage. Growth-first is automatically the first admitter, so no
    other option can answer; elsewhere in the list the obligation is what says they agree. -/
theorem selectF_continuous {f : Nat → Codec V M} {oω o₂ : Codec V M} {v : V} {a : V}
    (hs : IsSupAt f oω v)
    (h : selectF [oω, o₂] v = some a) : ∃ i, selectF [f i, o₂] v = some a := by
  have hadm : ∀ i, ((f i).e v).isSome = true → (oω.e v).isSome = true := fun i h1 =>
    let ⟨b, hb⟩ := Option.isSome_iff_exists.mp h1
    Option.isSome_iff_exists.mpr ⟨b, hs.ub i .host _ _ hb⟩
  cases hω : (oω.e v).isSome with
  | true =>
    rw [selectF_admit hω] at h
    obtain ⟨i, hi⟩ := hs.least a h
    exact ⟨i, by rw [selectF_admit (by rw [hi]; rfl)]; exact hi⟩
  | false =>
    refine ⟨0, ?_⟩
    have h0 : ((f 0).e v).isSome = false := by
      cases h0 : ((f 0).e v).isSome with
      | true => rw [hadm 0 h0] at hω; exact nomatch hω
      | false => rfl
    rw [selectF_skip h0]; rw [selectF_skip hω] at h; exact h

/-- Confluence is inherited by a tail. -/
theorem ConfluentAt.tail {o : Codec V M} {os : List (Codec V M)} {v : V}
    (h : ConfluentAt (o :: os) v) : ConfluentAt os v :=
  fun a ha b hb => h a (by simp [ha]) b (by simp [hb])

/-- The answer `selectF` gives comes from a member that admits. -/
theorem selectF_mem : ∀ {os : List (Codec V M)} {v : V} {a : V},
    selectF os v = some a → ∃ o ∈ os, (o.e v).isSome = true ∧ o.e v = some a
  | [], _, _, h => absurd h (by simp [selectF, select])
  | o :: os, v, a, h => by
      cases ho : (o.e v).isSome with
      | true => exact ⟨o, by simp, ho, by rw [selectF_admit ho] at h; exact h⟩
      | false =>
        rw [selectF_skip ho] at h
        obtain ⟨o', ho', hadm, he⟩ := selectF_mem h
        exact ⟨o', by simp [ho'], hadm, he⟩

/-- **Order-independence as a theorem.** Under the obligation, *any* admitter's answer is the
    answer — so the first-match definition does not depend on the order after all. -/
theorem selectF_of_mem : ∀ {os : List (Codec V M)} {v : V} {o : Codec V M},
    ConfluentAt os v → o ∈ os → (o.e v).isSome = true → selectF os v = o.e v
  | [], _, _, _, ho, _ => absurd ho (by simp)
  | hd :: tl, v, o, hc, ho, hadm => by
      cases hhd : (hd.e v).isSome with
      | true =>
        rw [selectF_admit hhd]
        exact hc hd (by simp) o (by simp [ho]) hhd hadm
      | false =>
        rw [selectF_skip hhd]
        have hne : o ≠ hd := fun h => by rw [h, hhd] at hadm; exact nomatch hadm
        exact selectF_of_mem (ConfluentAt.tail hc) (by
          rcases List.mem_cons.mp ho with rfl | h'
          · exact absurd rfl hne
          · exact h') hadm

/-- **Monotonicity over an arbitrary option list**, with the growth as a map. Cleaner than the
    two-option case, because `selectF_of_mem` does the work: the answer comes from *some*
    admitting member (`selectF_mem`), that member grows to an admitter with the same answer, and
    under the obligation any admitter's answer is the answer. -/
theorem selectF_mono_list {os : List (Codec V M)} {g : Codec V M → Codec V M}
    {v : V} {a : V}
    (hap : ∀ o ∈ os, Sub o (g o))
    (hc : ConfluentAt (os.map g) v)
    (h : selectF os v = some a) : selectF (os.map g) v = some a := by
  obtain ⟨o, ho, -, hoe⟩ := selectF_mem h
  have hmem : g o ∈ os.map g := List.mem_map_of_mem ho
  rw [selectF_of_mem hc hmem (Option.isSome_iff_exists.mpr ⟨a, hap o ho .host _ _ hoe⟩)]
  exact hap o ho .host _ _ hoe

/-- **Continuity, in general — and it does need the obligation at each stage.** See the note
    above: `selectF_continuous` escaped it by putting the growing option first. -/
theorem selectF_continuous_list {os : List (Codec V M)} {F : Nat → Codec V M → Codec V M}
    {v : V} {a : V}
    (hleast : ∀ o ∈ os, ∀ b, o.e v = some b → ∃ i, (F i o).e v = some b)
    (hc : ∀ i, ConfluentAt (os.map (F i)) v)
    (h : selectF os v = some a) : ∃ i, selectF (os.map (F i)) v = some a := by
  obtain ⟨o, ho, hoadm, hoe⟩ := selectF_mem h
  obtain ⟨i, hi⟩ := hleast o ho a hoe
  refine ⟨i, ?_⟩
  have hmem : F i o ∈ os.map (F i) := List.mem_map_of_mem ho
  rw [selectF_of_mem (hc i) hmem (by rw [hi]; rfl)]
  exact hi

/-! ## Compatibility -/

/-- **Compatibility**: `c` reads `a` as `t`. If `d` acts at `a` or at `t`, then `d` reads `a` as
    `t`. The relation is one-sided. `PairwiseCompat` asks it of each pair in both orders, so
    the obligation of a union is symmetric, as Lawson's compatibility of partial bijections is.
    That obligation is the condition under which a union of lawful options is lawful. -/
def Compat (c d : Codec V M) : Prop :=
  ∀ a t, c.p a = some t → ((d.p a).isSome = true ∨ (d.e t).isSome = true) → d.p a = some t

/-- **Read agreement**: two compatible readings of one attribute give one value. -/
theorem Compat.p_agree {c d : Codec V M} (h : Compat c d) {a t w}
    (hc : c.p a = some t) (hd : d.p a = some w) : w = t := by
  have := h a t hc (Or.inl (by rw [hd]; rfl))
  rw [hd] at this; exact Option.some.inj this

/-- A family has a first option that answers at the orientation `o`, wherever one of its options
    answers there. -/
theorem find?_attempt (o : Orient) {os : List (Codec V M)} {c : Codec V M} {x y}
    (hc : c ∈ os) (h : c.f o x = some y) :
    ∃ c', os.find? (fun d => (d.f o x).isSome) = some c' :=
  Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨c, hc, by simp [h]⟩)

/-- The first option that answers at the orientation `o` answers. -/
theorem acts_of_find? (o : Orient) {os : List (Codec V M)} {c : Codec V M} {x}
    (hf : os.find? (fun d => (d.f o x).isSome) = some c) : (c.f o x).isSome = true :=
  List.find?_some (p := fun d : Codec V M => (d.f o x).isSome) hf

/-- Canonical reads: the codec writes each value that the codec reads at the attribute that
    the codec read. -/
def Canon (u : Codec V M) : Prop := ∀ a t, u.p a = some t → u.e t = some a

/-- The identity codec reads canonically. -/
theorem canon_idCodec : Canon (idCodec : Codec V M) := fun _ _ h => by cases h; rfl

/-- **Write agreement**: two compatible options that both write `v` write one attribute. -/
theorem Compat.e_agree {c d : Codec V M} (h : Compat c d) (hc : LawfulCore member c)
    (hd : Canon d) {v a b}
    (ha : c.e v = some a) (hb : d.e v = some b) : b = a := by
  have hp : d.p a = some v := h a v (hc.retract ha) (Or.inr (by rw [hb]; rfl))
  have := hd a v hp
  rw [hb] at this; exact Option.some.inj this

/-- **A union sends what any option sends**, over lawful, pairwise compatible options. `Compat`
    is stated at the read, so the write and the read take two proofs: the write reads back
    through the canonical reads of the first writer. -/
theorem altCodec_of_mem {os : List (Codec V M)} {μA : Option M}
    (hl : ∀ o ∈ os, Lawful member o)
    (hC : ∀ o ∈ os, ∀ o' ∈ os, Compat o o') {c : Codec V M} (hc : c ∈ os) :
    ∀ (o : Orient) {x : V} {y : V},
      c.f o x = some y → (altCodec os μA).f o x = some y :=
  Orient.both
    (fun {v a} he => by
      obtain ⟨o', hf⟩ := find?_attempt .host hc he
      have ho' := List.mem_of_find?_eq_some hf
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (acts_of_find? .host hf)
      rw [(hC c hc o' ho').e_agree (hl c hc).core (fun _ _ hp => (hl o' ho').canon hp) he hb]
        at hb
      exact altCodec_f.mpr ⟨o', hf, hb⟩)
    (fun {a v} hp => by
      obtain ⟨o', hf⟩ := find?_attempt .dual hc hp
      have ho' := List.mem_of_find?_eq_some hf
      exact altCodec_f.mpr ⟨o', hf, hC c hc o' ho' _ _ hp (Or.inl (acts_of_find? .dual hf))⟩)

/-- The sum's core laws. Compatibility is what makes them hold: the option that reads the
    attribute of a write reads the value back, whichever option wrote. -/
theorem lawfulCore_altCodec {os : List (Codec V M)} {μA : Option M}
    (h : ∀ o ∈ os, LawfulCore member o)
    (hC : ∀ o ∈ os, ∀ o' ∈ os, Compat o o')
    (hW : ∀ m, μA = some m → ∀ o ∈ os, ∀ t a, o.e t = some a → member a = m) :
    LawfulCore member (altCodec os μA) where
  retract he := by
    obtain ⟨o, ho, -, hoe⟩ := altCodec_admits he
    have hop := (h o ho).retract hoe
    obtain ⟨o', hf'⟩ := find?_attempt .dual ho hop
    have ho' := List.mem_of_find?_eq_some hf'
    exact altCodec_f.mpr ⟨o', hf', hC o ho o' ho' _ _ hop (Or.inl (acts_of_find? .dual hf'))⟩
  canon hp := by
    obtain ⟨o, ho, -, hop⟩ := altCodec_admits hp
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ((h o ho).canon hop)
    obtain ⟨o', hf'⟩ := find?_attempt .host ho ha'
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (acts_of_find? .host hf')
    exact Option.isSome_iff_exists.mpr ⟨b, altCodec_f.mpr ⟨o', hf', hb⟩⟩
  writes := by
    intro μ hμ t a he
    obtain ⟨o, ho, -, hoe⟩ := altCodec_admits he
    exact hW μ hμ o ho t a hoe

/-- …and the laws: the option that sends the input inverts the output, and the union sends
    what any option sends. One proof serves each orientation. -/
theorem lawful_altCodec {os : List (Codec V M)} {μA : Option M}
    (h : ∀ o ∈ os, Lawful member o)
    (hC : ∀ o ∈ os, ∀ o' ∈ os, Compat o o')
    (hW : ∀ m, μA = some m → ∀ o ∈ os, ∀ t a, o.e t = some a → member a = m) :
    Lawful member (altCodec os μA) where
  inv hxy :=
    let ⟨c, hc, _, hcy⟩ := altCodec_admits hxy
    altCodec_of_mem h hC hc _ ((h c hc).inv hcy)
  writes hμ _ _ he := let ⟨c, hc, _, hce⟩ := altCodec_admits he; hW _ hμ c hc _ _ hce

/-- **Exclusive admission gives compatibility.** Where the option that admits an input is the
    only one, the other option never acts where the first reads. -/
theorem compat_of_exclusive {os : List (Codec V M)}
    (hl : ∀ o ∈ os, LawfulCore member o)
    (hxV : ∀ o ∈ os, ∀ v, (o.e v).isSome = true → os.filter (fun c => (c.e v).isSome) = [o])
    (hxA : ∀ o ∈ os, ∀ a, (o.p a).isSome = true → os.filter (fun c => (c.p a).isSome) = [o]) :
    ∀ o ∈ os, ∀ o' ∈ os, Compat o o' := by
  intro o ho o' ho' a t hp hact
  have hsame : o' = o := by
    rcases hact with hq | he
    · have hoA : (o.p a).isSome = true := by simp [hp]
      have ho'A : (o'.p a).isSome = true := hq
      have := (List.mem_filter (p := (fun c => (c.p a).isSome))).mpr ⟨ho', ho'A⟩
      rw [hxA o ho a hoA] at this; exact List.mem_singleton.mp this
    · have hoV : (o.e t).isSome = true := (hl o ho).canon hp
      have ho'V : (o'.e t).isSome = true := he
      have := (List.mem_filter (p := (fun c => (c.e t).isSome))).mpr ⟨ho', ho'V⟩
      rw [hxV o ho t hoV] at this; exact List.mem_singleton.mp this
  subst hsame; exact hp

/-- **The cross half**: `d` reads back from the attribute of `c` a value that both write. -/
theorem Compat.cross {c d : Codec V M} (hc : Lawful member c) (h : Compat c d) {v a}
    (he : c.e v = some a) (hd : (d.e v).isSome = true) : d.p a = some v :=
  h a v (hc.retract he) (Or.inr hd)

/-- **Write agreement and read agreement give `Compat`** under canonical reads of `c`. So
    `Compat` is the classical compatibility on partial bijections. -/
theorem compat_of_agree {c d : Codec V M} (hcan : ∀ a t, c.p a = some t → c.e t = some a)
    (hd : Lawful member d)
    (hE : ∀ v a b, c.e v = some a → d.e v = some b → a = b)
    (hP : ∀ a t w, c.p a = some t → d.p a = some w → w = t) : Compat c d := by
  intro a t hct hact
  rcases hact with hq | he
  · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hq
    rw [hw, hP a t w hct hw]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp he
    cases hE t a b (hcan a t hct) hb
    exact hd.retract hb

/-- **Two codecs below one canonical bound are `Compat`.** The premises are minimal: the read
    half of `Sub c u`, both halves of `Sub d u`, `Canon u`, and `retract` of `d`. -/
theorem compat_of_common_bound {c d u : Codec V M}
    (hcp : ∀ a v, c.p a = some v → u.p a = some v) (hd : Sub d u) (hu : Canon u)
    (hdr : ∀ {t a}, d.e t = some a → d.p a = some t) : Compat c d := by
  intro a t hp hact
  have hup : u.p a = some t := hcp _ _ hp
  rcases hact with hq | he
  · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hq
    have : u.p a = some w := hd .dual _ _ hw
    rw [hup] at this; cases this; exact hw
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp he
    have : u.e t = some b := hd .host _ _ hb
    rw [hu a t hup] at this; cases this
    exact hdr hb

/-- **`compat_of_common_bound` with `Sub` on both sides and a lawful `d`.** -/
theorem compat_of_common_bound' {c d u : Codec V M} (hc : Sub c u) (hd : Sub d u)
    (hu : Canon u) (hdl : Lawful member d) : Compat c d :=
  compat_of_common_bound (hc .dual) hd hu hdl.retract

/-! ## §6's `≡` -/

/-- §6's `≡`. Note it is *not* equality of the pair: `e` and `p` need only agree where
    both are defined, which is what lets a rewrite shrink a domain. -/
structure Codec.Equiv (c d : Codec V M) : Prop where
  /-- The same held set. -/
  heldSet : ∀ v, c.T v ↔ d.T v
  /-- The same member. -/
  member : c.μ = d.μ
  /-- `e` agrees wherever both are defined. -/
  writes : ∀ {v a a'}, c.e v = some a → d.e v = some a' → a = a'
  /-- `p` agrees wherever both are defined. -/
  reads : ∀ {a v v'}, c.p a = some v → d.p a = some v' → v = v'

theorem Codec.Equiv.refl (c : Codec V M) : Codec.Equiv c c :=
  ⟨fun _ => Iff.rfl, rfl, fun h h' => Option.some.inj (h.symm.trans h'),
    fun h h' => Option.some.inj (h.symm.trans h')⟩

/-- There is no `Codec.Equiv.trans`, and the omission is not an oversight: `≡` compares
    `e` and `p` only *where both are defined*, so a codec that writes and reads nowhere is
    `≡` to everything and chains two codecs that disagree outright. Refuted as
    `Refutations.not_equiv_trans`, with all three codecs `Lawful` and on their `Carrier`.
    §6 is a table of rewrites, each proved on its own; it is not a congruence to reason
    in transitively. -/
theorem Codec.Equiv.symm {c d : Codec V M} (h : Codec.Equiv c d) : Codec.Equiv d c :=
  ⟨fun v => (h.heldSet v).symm, h.member.symm,
    fun hd hc => (h.writes hc hd).symm, fun hd hc => (h.reads hc hd).symm⟩

/-! ### `union` is commutative, at every permutation

    Resolution takes the first admitter. Where the options are lawful and pairwise
    compatible, every admitter writes and reads alike, so reordering the options changes
    nothing. The general case is proved directly, and the adjacent one falls out of it at
    `List.Perm.swap`: `≡` does not compose (`Refutations.not_equiv_trans`), and an equality
    does. The two codecs are **equal**, not only equivalent. -/

/-- Two options that are defined at the same answers are equal. -/
theorem option_eq_of_some_iff {β : Type} {x y : Option β} (h : ∀ b, x = some b ↔ y = some b) :
    x = y := by
  cases hx : x with
  | none =>
    cases hy : y with
    | none => rfl
    | some b => rw [hx] at h; exact nomatch (h b).mpr hy
  | some b => exact ((h b).mp hx).symm

/-- §6: `union(c₁ … cₙ) ≡ union(c_σ(1) … c_σ(n))`, **on the nose**, over options that are
    lawful and pairwise compatible. -/
theorem altCodec_perm {os os' : List (Codec V M)} (h : os.Perm os') (μA : Option M)
    (hl : ∀ o ∈ os, Lawful member o)
    (hC : ∀ o ∈ os, ∀ o' ∈ os, Compat o o') :
    altCodec os μA = altCodec os' μA := by
  have m := fun o => h.mem_iff (a := o)
  have hl' : ∀ o ∈ os', Lawful member o := fun o ho => hl o ((m o).mpr ho)
  have hC' : ∀ o ∈ os', ∀ o' ∈ os', Compat o o' :=
    fun o ho o' ho' => hC o ((m o).mpr ho) o' ((m o').mpr ho')
  have hf : ∀ (o : Orient) x, (altCodec os μA).f o x = (altCodec os' μA).f o x := fun o x =>
    option_eq_of_some_iff fun b => ⟨fun h => ?_, fun h => ?_⟩
  refine Codec.ext ?_ rfl (funext (hf .host)) (funext (hf .dual))
  · funext v
    exact propext ⟨fun ⟨o, ho, hT⟩ => ⟨o, (m o).mp ho, hT⟩,
      fun ⟨o, ho, hT⟩ => ⟨o, (m o).mpr ho, hT⟩⟩
  · obtain ⟨c, hc, -, hcb⟩ := altCodec_admits h
    exact altCodec_of_mem hl' hC' ((m c).mp hc) o hcb
  · obtain ⟨c, hc, -, hcb⟩ := altCodec_admits h
    exact altCodec_of_mem hl hC ((m c).mpr hc) o hcb

/-- The row as §6 states it, in `≡`: `Codec.Equiv.refl` transported along the equality. -/
theorem equiv_altCodec_perm {os os' : List (Codec V M)} (h : os.Perm os') (μA : Option M)
    (hl : ∀ o ∈ os, Lawful member o)
    (hC : ∀ o ∈ os, ∀ o' ∈ os, Compat o o') :
    Codec.Equiv (altCodec os μA) (altCodec os' μA) :=
  altCodec_perm h μA hl hC ▸ Codec.Equiv.refl _

/-- §6: `union(c₁, c₂, …) ≡ union(c₂, c₁, …)`, the general theorem at `List.Perm.swap`. -/
theorem equiv_altCodec_swap (o₁ o₂ : Codec V M) (os : List (Codec V M)) (μA : Option M)
    (hl : ∀ o ∈ o₁ :: o₂ :: os, Lawful member o)
    (hC : ∀ o ∈ o₁ :: o₂ :: os, ∀ o' ∈ o₁ :: o₂ :: os, Compat o o') :
    Codec.Equiv (altCodec (o₁ :: o₂ :: os) μA) (altCodec (o₂ :: o₁ :: os) μA) :=
  equiv_altCodec_perm (List.Perm.swap o₂ o₁ os) μA hl hC

/-! ### `held` is an identity, and composes

§6's first two rows. The second is the one worth stating carefully: the writing halves
compose in the order written and the reading halves compose *reversed*, which is what
"note the reversal on the reading half" means and what the model makes literal. -/

/-- §6: `held(c, id, id) ≡ c`. -/
theorem equiv_through_id (c : Codec V M) : Codec.Equiv (c.through id id) c := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩
  · exact fun h h' => Option.some.inj ((through_e.mp h).symm.trans h')
  · intro a v v' h h'
    obtain ⟨w, hw, rfl⟩ := through_p.mp h
    exact Option.some.inj (hw.symm.trans h')

/-- §6: `held(held(c, f, g), f′, g′) ≡ held(c, f ∘ f′, g′ ∘ g)`. -/
theorem equiv_through_comp (c : Codec V M) (f g f' g' : V → V) :
    Codec.Equiv ((c.through f g).through f' g') (c.through (f ∘ f') (g' ∘ g)) := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩
  · exact fun h h' => Option.some.inj (h.symm.trans h')
  · intro a v v' h h'
    obtain ⟨w, hw, rfl⟩ := through_p.mp h
    obtain ⟨x, hx, rfl⟩ := through_p.mp hw
    obtain ⟨y, hy, rfl⟩ := through_p.mp h'
    rw [hx] at hy
    cases hy
    rfl

/-! ### `refine` — prisms meet, and a full one is no refinement -/

/-- §6: `refine(refine(c, q), q′) ≡ refine(c, q ∩ q′)`. -/
theorem equiv_restrict_meet (c : Codec V M) (q q' : V → Bool) :
    Codec.Equiv ((c.restrict q).restrict q') (c.restrict (fun v => q v && q' v)) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro v
    constructor
    · rintro ⟨⟨hT, hq⟩, hq'⟩
      exact ⟨hT, by simp [hq, hq']⟩
    · rintro ⟨hT, hqq⟩
      simp only [Bool.and_eq_true] at hqq
      exact ⟨⟨hT, hqq.1⟩, hqq.2⟩
  · intro v a a' h h'
    obtain ⟨-, hin, -⟩ := refine2_f.mp h
    exact Option.some.inj ((refine2_f.mp hin).2.1.symm.trans (refine2_f.mp h').2.1)
  · intro a v v' h h'
    obtain ⟨-, hin, -⟩ := refine2_f.mp h
    exact Option.some.inj ((refine2_f.mp hin).2.1.symm.trans (refine2_f.mp h').2.1)

/-- §6: `refine(c, T) ≡ c` for `⊢ c : T ⇝ μ`. A refinement admitting everything the codec
    holds is no refinement — and note the premise needed is only that `q` agrees with `T`,
    not that the pair is on its carrier: `≡` compares `e` and `p` where *both* are defined,
    so a `q` that rejects something outside `T` costs nothing. -/
theorem equiv_restrict_full (c : Codec V M) (q : V → Bool)
    (hq : ∀ v, c.T v ↔ q v = true) : Codec.Equiv (c.restrict q) c := by
  refine ⟨fun v => ⟨fun h => h.1, fun h => ⟨h, (hq v).mp h⟩⟩, rfl, ?_, ?_⟩
  · exact fun h h' => Option.some.inj ((refine2_f.mp h).2.1.symm.trans h')
  · exact fun h h' => Option.some.inj ((refine2_f.mp h).2.1.symm.trans h')

/-! ### `alternate reader` with its own reading -/

/-- The pair is not merely `≡` but equal: both branches of `extendRead`'s match give
    `c.p a`, so re-reading through `c`'s own `p` adds nothing at all. -/
theorem extendRead_self_p (c : Codec V M) : (c.extendRead c.p).p = c.p := by
  funext a
  simp only [Codec.extendRead, Codec.ofEP_p]
  cases c.p a <;> rfl

/-- §6: `legacy(c, p_c) ≡ c`. -/
theorem equiv_extendRead_self (c : Codec V M) : Codec.Equiv (c.extendRead c.p) c := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩
  · intro v a a' h h'
    exact Option.some.inj (h.symm.trans h')
  · intro a v v' h h'
    rw [extendRead_self_p] at h
    exact Option.some.inj (h.symm.trans h')

/-- §6: `legacy(c, r) ≈ c` on `Can(c)`. A migration differs from the current encoding only
    *off* the canonical set — on it, `(R)` has already made `c.p` succeed, so `r` is never
    consulted. The premise is exactly `(R)`, which is why this row is about lawful codecs
    and not about `extendRead` in general. -/
theorem extendRead_eq_on_can (c : Codec V M) (r : V → Option V) (hc : Lawful member c)
    {a : V} (ha : Can c a) : (c.extendRead r).p a = c.p a := by
  obtain ⟨v, hv⟩ := ha
  have hp : c.p a = some v := hc.retract hv
  simp only [Codec.extendRead, Codec.ofEP_p, hp]

/-! ### `union` of one -/

/-- §6: `union(c) ≡ c`. Choice of one: `o` is the first option that acts exactly when `o`
    acts, and `altCodec` then reads `o`'s own pair. -/
theorem equiv_altCodec_single (o : Codec V M) :
    Codec.Equiv (altCodec [o] o.μ) o := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro v
    constructor
    · rintro ⟨x, hx, hT⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hT
      · exact absurd hx' (by simp)
    · exact fun h => ⟨o, List.mem_cons_self, h⟩
  · intro v a a' h h'
    obtain ⟨x, hx, -, hxe⟩ := altCodec_admits h
    obtain rfl : x = o := by simpa using hx
    exact Option.some.inj (hxe.symm.trans h')
  · intro a v v' h h'
    obtain ⟨x, hx, -, hxp⟩ := altCodec_admits h
    obtain rfl : x = o := by simpa using hx
    exact Option.some.inj (hxp.symm.trans h')

/-! ### The codec wrappers preserve the member -/

theorem through_μ (c : Codec V M) (f g : V → V) : (c.through f g).μ = c.μ := rfl

theorem restrict_μ (c : Codec V M) (q : V → Bool) : (c.restrict q).μ = c.μ := rfl

theorem extendRead_μ (c : Codec V M) (r : V → Option V) :
    (c.extendRead r).μ = c.μ := rfl

/-! ### Nesting is flattening

A nested union consults the head, then the inner union's first admitter; the flat union
consults the same options in the same order. So both halves are equal, with no side
condition. -/

/-- `select` over no option answers nothing. -/
theorem select_nil_eq {X Y : Type} (run : Codec V M → X → Option Y) (x : X) :
    select [] run x = none := rfl

/-- `select` at a cons: the head answers where it acts. -/
theorem select_cons {X Y : Type} (o : Codec V M) (os : List (Codec V M))
    (run : Codec V M → X → Option Y) (x : X) :
    select (o :: os) run x = if (run o x).isSome then run o x else select os run x := by
  unfold select; cases h : (run o x).isSome <;> simp [List.find?, h]

/-- A nested union sends as the flat union, at each orientation. -/
theorem altCodec_nest (o₁ o₂ o₃ : Codec V M) (μ μ' μf : Option M) {o : Orient}
    (x : V) :
    (altCodec [o₁, (altCodec [o₂, o₃] μ')] μ).f o x = (altCodec [o₁, o₂, o₃] μf).f o x := by
  show select _ _ x = select _ _ x
  rw [select_cons, select_cons, select_cons, select_nil_eq]
  show (if _ then _ else if ((select [o₂, o₃] (·.f o) x).isSome) then
    select [o₂, o₃] (·.f o) x else none) = _
  cases select [o₂, o₃] (·.f o) x <;> simp

/-- The held sets coincide. Nesting a union changes how it *resolves*, never what it
    holds — which is why this half needs no side condition at all. -/
theorem altCodec_assoc_heldSet (o₁ o₂ o₃ : Codec V M) (μa μb : Option M) (v : V) :
    (altCodec [o₁, (altCodec [o₂, o₃] μb)] μa).T v
      ↔ (altCodec [o₁, o₂, o₃] μa).T v := by
  constructor
  · rintro ⟨x, hx, hT⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨x, List.mem_cons_self, hT⟩
    · rcases List.mem_cons.mp hx' with rfl | hx''
      · obtain ⟨y, hy, hTy⟩ := hT
        exact ⟨y, List.mem_cons_of_mem _ hy, hTy⟩
      · exact absurd hx'' (by simp)
  · rintro ⟨x, hx, hT⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨x, List.mem_cons_self, hT⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self), ⟨x, hx', hT⟩⟩

end Calculus.Alg
