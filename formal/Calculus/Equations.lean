import Calculus.Soundness
import Calculus.Denote
import Calculus.Opaque

/-!
# §6 — Equations

Which rewrites preserve the pair. `≡` is §6's own reading: the same held set, the same
member, and `e` and `p` agreeing everywhere both are defined.

All eleven of §6's "Hold" rows are proved here. Two of them are cited elsewhere as
load-bearing and came first:

* `union(c₁ … cₙ) ≡ union(c_σ(1) … c_σ(n))` — §5 leans on this for "declaration order is
  never consulted". Proved at *every* permutation and as an **equality** of the pair
  (`altCodec_perm`), not merely `≡`. Deriving the general case from the adjacent one would
  need `≡` to compose, and `Refutations.not_equiv_trans` says it does not.

The remaining rows: `held`'s identity and composition, `refine`'s meet and its full case,
`alternate reader` with its own reading (and `≈` on `Can(c)`), `union` of one, and the member
preservation of the three codec wrappers.

The last row, `union` associativity, is the table's only *conditional* one — and it turns
out not to need its conditions. See the section below for why, and
`Refutations.not_eq_altCodec_assoc` for the behavioural difference `≡` is blind to.

The "Do not hold" table is settled in `Refutations.lean`. §6 is complete.
-/

namespace Calculus

/-- §6's `≡`. Note it is *not* equality of the pair: `e` and `p` need only agree where
    both are defined, which is what lets a rewrite shrink a domain. -/
structure Codec.Equiv (c d : Codec) : Prop where
  /-- The same held set. -/
  heldSet : ∀ v, c.T v ↔ d.T v
  /-- The same member. -/
  member : c.μ = d.μ
  /-- `e` agrees wherever both are defined. -/
  writes : ∀ {v a a'}, c.e v = some a → d.e v = some a' → a = a'
  /-- `p` agrees wherever both are defined. -/
  reads : ∀ {a v v'}, c.p a = some v → d.p a = some v' → v = v'

theorem Codec.Equiv.refl (c : Codec) : Codec.Equiv c c :=
  ⟨fun _ => Iff.rfl, rfl, fun h h' => Option.some.inj (h.symm.trans h'),
    fun h h' => Option.some.inj (h.symm.trans h')⟩

/-- There is no `Codec.Equiv.trans`, and the omission is not an oversight: `≡` compares
    `e` and `p` only *where both are defined*, so a codec that writes and reads nowhere is
    `≡` to everything and chains two codecs that disagree outright. Refuted as
    `Refutations.not_equiv_trans`, with all three codecs `Lawful` and on their `Carrier`.
    §6 is a table of rewrites, each proved on its own; it is not a congruence to reason
    in transitively. -/
theorem Codec.Equiv.symm {c d : Codec} (h : Codec.Equiv c d) : Codec.Equiv d c :=
  ⟨fun v => (h.heldSet v).symm, h.member.symm,
    fun hd hc => (h.writes hc hd).symm, fun hd hc => (h.reads hc hd).symm⟩



/-! ## `union` is commutative, at every permutation

    Resolution is unique admission, never declaration order (§5) — so reordering the
    options changes nothing.

    The direction of the argument is the point. §6 justifies the row by the adjacent swap
    plus "transpositions generate every permutation", and that argument is unavailable: it
    composes rewrites, and `≡` does not compose — `Refutations.not_equiv_trans` exhibits
    three lawful codecs on their carriers where it fails. So the general case is proved
    first and directly, and the adjacent one falls out of it at `List.Perm.swap`. What the
    general case proves is stronger than the row asks: the two codecs are **equal**, not
    equivalent. `select` reads its option list
    only through the filter; a permutation permutes the filter; and the only two lengths at
    which `select` answers at all — none and one — are the two a permutation pins. The held
    set follows by `propext` from `Perm.mem_iff`.

    That is why nothing here needs transitivity: an equality composes whether or not `≡`
    does. -/


/-- **`select` does not read its list's order.** The one lemma behind the permutation
    lift, and it is about `select` rather than about `union`: both halves of `altCodec`
    are instances, so the write and read sides are this theorem twice rather than two
    proofs. `select` answers only when the filter is a singleton and is `none` at every
    other length — and a permutation preserves both the singleton and its element. -/
theorem select_perm {A B : Type} {os os' : List OptionSem} (h : os.Perm os')
    (adm : OptionSem → A → Bool) (run : OptionSem → A → Option B) (x : A) :
    select os adm run x = select os' adm run x := by
  simp only [select]
  have hp : (os.filter (adm · x)).Perm (os'.filter (adm · x)) := h.filter _
  generalize os.filter (adm · x) = l at hp ⊢
  generalize os'.filter (adm · x) = l' at hp ⊢
  match l, l', hp with
  | [], l', hp => rw [List.nil_perm] at hp; subst hp; rfl
  | [o], l', hp => rw [List.singleton_perm] at hp; subst hp; rfl
  | _ :: _ :: _, l', hp =>
      -- neither side answers; that the two `none`s agree is all the row needs
      have hlen := hp.length_eq
      match l', hlen with
      | [], hlen => simp at hlen
      | [_], hlen => simp at hlen
      | _ :: _ :: _, _ => rfl

/-- §6: `union(c₁ … cₙ) ≡ union(c_σ(1) … c_σ(n))`, **on the nose**. Reordering the options
    does not produce an equivalent codec, it produces the same one — the held set by
    `propext`, the member by hypothesis, and the pair by `select_perm`. -/
theorem altCodec_perm {os os' : List OptionSem} (h : os.Perm os') (μA : Option Member) :
    altCodec os μA = altCodec os' μA := by
  refine Codec.ext ?_ rfl ?_ ?_
  · funext v
    exact propext ⟨fun ⟨o, ho, hT⟩ => ⟨o, h.mem_iff.mp ho, hT⟩,
      fun ⟨o, ho, hT⟩ => ⟨o, h.mem_iff.mpr ho, hT⟩⟩
  · funext v; exact select_perm h _ _ v
  · funext a; exact select_perm h _ _ a

/-- The row as §6 states it, in `≡`. It is `Codec.Equiv.refl` transported along an
    equality, which is the whole content of the remark above: the general case never
    enters the equivalence, so it never meets the failure of transitivity that would sink
    the generating argument. -/
theorem equiv_altCodec_perm {os os' : List OptionSem} (h : os.Perm os') (μA : Option Member) :
    Codec.Equiv (altCodec os μA) (altCodec os' μA) :=
  altCodec_perm h μA ▸ Codec.Equiv.refl _

/-- §6: `union(c₁, c₂, …) ≡ union(c₂, c₁, …)`, the adjacent case §6's own justification
    names. It is the general theorem at `List.Perm.swap` — the transposition was never a
    separate fact, only the one the table's argument happened to reach for. -/
theorem equiv_altCodec_swap (o₁ o₂ : OptionSem) (os : List OptionSem)
    (μA : Option Member) :
    Codec.Equiv (altCodec (o₁ :: o₂ :: os) μA) (altCodec (o₂ :: o₁ :: os) μA) :=
  equiv_altCodec_perm (List.Perm.swap o₂ o₁ os) μA

/-! ## `held` is an identity, and composes

§6's first two rows. The second is the one worth stating carefully: the writing halves
compose in the order written and the reading halves compose *reversed*, which is what
"note the reversal on the reading half" means and what the model makes literal. -/

/-- §6: `held(c, id, id) ≡ c`. -/
theorem equiv_through_id (c : Codec) : Codec.Equiv (c.through id id) c := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩
  · exact fun h h' => Option.some.inj ((through_e.mp h).symm.trans h')
  · intro a v v' h h'
    obtain ⟨w, hw, rfl⟩ := through_p.mp h
    exact Option.some.inj (hw.symm.trans h')

/-- §6: `held(held(c, f, g), f′, g′) ≡ held(c, f ∘ f′, g′ ∘ g)`. -/
theorem equiv_through_comp (c : Codec) (f g f' g' : Value → Value) :
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

/-! ## `refine` — prisms meet, and a full one is no refinement -/

/-- §6: `refine(refine(c, q), q′) ≡ refine(c, q ∩ q′)`. -/
theorem equiv_restrict_meet (c : Codec) (q q' : Value → Bool) :
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
    obtain ⟨-, hin⟩ := restrict_e.mp h
    exact Option.some.inj ((restrict_e.mp hin).2.symm.trans (restrict_e.mp h').2)
  · intro a v v' h h'
    obtain ⟨hin, -⟩ := restrict_p.mp h
    exact Option.some.inj ((restrict_p.mp hin).1.symm.trans (restrict_p.mp h').1)

/-- §6: `refine(c, T) ≡ c` for `⊢ c : T ⇝ μ`. A refinement admitting everything the codec
    holds is no refinement — and note the premise needed is only that `q` agrees with `T`,
    not that the pair is on its carrier: `≡` compares `e` and `p` where *both* are defined,
    so a `q` that rejects something outside `T` costs nothing. -/
theorem equiv_restrict_full (c : Codec) (q : Value → Bool)
    (hq : ∀ v, c.T v ↔ q v = true) : Codec.Equiv (c.restrict q) c := by
  refine ⟨fun v => ⟨fun h => h.1, fun h => ⟨h, (hq v).mp h⟩⟩, rfl, ?_, ?_⟩
  · exact fun h h' => Option.some.inj ((restrict_e.mp h).2.symm.trans h')
  · exact fun h h' => Option.some.inj ((restrict_p.mp h).1.symm.trans h')

/-! ## `alternate reader` with its own reading -/

/-- The pair is not merely `≡` but equal: both branches of `extendRead`'s match give
    `c.p a`, so re-reading through `c`'s own `p` adds nothing at all. -/
theorem extendRead_self_p (c : Codec) : (c.extendRead c.p).p = c.p := by
  funext a
  show (match c.p a with | some v => some v | none => c.p a) = c.p a
  cases c.p a <;> rfl

/-- §6: `legacy(c, p_c) ≡ c`. -/
theorem equiv_extendRead_self (c : Codec) : Codec.Equiv (c.extendRead c.p) c := by
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
theorem extendRead_eq_on_can (c : Codec) (r : Attr → Option Value) (hc : Lawful c)
    {a : Attr} (ha : Can c a) : (c.extendRead r).p a = c.p a := by
  obtain ⟨v, hv⟩ := ha
  have hp : c.p a = some v := hc.retract hv
  show (match c.p a with | some v => some v | none => r a) = c.p a
  rw [hp]

/-! ## `union` of one -/

/-- §6: `union(c) ≡ c`. Choice of one: the filter is `[o]` exactly when `o` admits, and
    `altCodec` then reads `o`'s own pair. Where `o` does not admit, the union is undefined
    and `≡` asks nothing — which is the clause that makes this row true for a `byStructure`
    option as well as a `byAttempt` one. -/
theorem equiv_altCodec_single (o : OptionSem) :
    Codec.Equiv (altCodec [o] o.c.μ) o.c := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro v
    constructor
    · rintro ⟨x, hx, hT⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hT
      · exact absurd hx' (by simp)
    · exact fun h => ⟨o, List.mem_cons_self, h⟩
  · intro v a a' h h'
    obtain ⟨x, hf, hxe⟩ := altCodec_e.mp h
    obtain rfl : x = o := by simpa using (mem_of_filter_eq_singleton hf).1
    exact Option.some.inj (hxe.symm.trans h')
  · intro a v v' h h'
    obtain ⟨x, hf, hxp⟩ := altCodec_p.mp h
    obtain rfl : x = o := by simpa using (mem_of_filter_eq_singleton hf).1
    exact Option.some.inj (hxp.symm.trans h')

/-! ## Wrappers preserve the member

§6's last "Hold" row, `μ(w(c)) = μ(c)` for `w ∈ {held, refine, legacy, optional,

Three of the five are codec wrappers. The other two are **fields**, and this file used to
say their half of the row was "the stratification of §4 and not a statement about
`Codec.μ` at all". That was an evasion: §4 says in as many words that *a field carries a
member like anything else*, and `FieldSem.codec` is where the model puts it. Stated
through that accessor the two rows are `rfl` — which is the honest form of the claim
rather than a reason to skip it, and it is what makes the row five of five. -/

theorem through_μ (c : Codec) (f g : Value → Value) : (c.through f g).μ = c.μ := rfl

theorem restrict_μ (c : Codec) (q : Value → Bool) : (c.restrict q).μ = c.μ := rfl

theorem extendRead_μ (c : Codec) (r : Attr → Option Value) :
    (c.extendRead r).μ = c.μ := rfl

/-- §4 `(opt)`: an optional attribute is still stored somewhere, and where is the
    subterm's member. -/
theorem optional_μ (t : Term) : (fieldSem (.optional t)).codec.μ = (denote t).μ := rfl

/-! ## `union` is associative

§6's row, stated outright: "Associative. An ambiguity *inside* the nested option fails
locally on the left and leaves the right side undefined, and `≡` compares `e` and `p` only
where both are defined, so the two sides cannot disagree there."

A condition on this row would be vacuous under `≡`, which is why it carries none: the case a
condition would exclude is the case the right side leaves undefined, and `≡` does not reach
it. The two forms are still not interchangeable, and `Refutations.not_eq_altCodec_assoc`
exhibits the difference `≡` cannot see: one writes where the other refuses. -/

/-- The member index nests the same way it flattens. Both sides conclude the head member
    or `⊤`, so the content is entirely in whether the condition agrees. -/
theorem unanimous_pair_assoc (a b c : Option Member) :
    unanimous [a, unanimous [b, c]] = unanimous [a, b, c] := by
  show (if ([unanimous [b, c]].all (· == a)) = true then a else none)
      = (if ([b, c].all (· == a)) = true then a else none)
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  by_cases hcb : (c == b) = true
  · have hu : unanimous [b, c] = b := by
      show (if ([c].all (· == b)) = true then b else none) = b
      simp only [List.all_cons, List.all_nil, Bool.and_true, if_pos hcb]
    rw [hu, eq_of_beq hcb, Bool.and_self]
  · have hu : unanimous [b, c] = none := by
      show (if ([c].all (· == b)) = true then b else none) = none
      simp only [List.all_cons, List.all_nil, Bool.and_true, if_neg hcb]
    rw [hu]
    cases a with
    | none => simp
    | some x =>
      have hne : ((b == some x) && (c == some x)) = false := by
        cases hbx : (b == some x) with
        | false => simp
        | true =>
          cases hcx : (c == some x) with
          | false => simp
          | true =>
            exact absurd (by rw [eq_of_beq hbx, eq_of_beq hcx]; simp) hcb
      simp [hne]

/-! ### Resolution, named

`altCodec` reads its option list only through "exactly one admits", so at two and three
options its pair has a small closed form. Naming those forms is what lets the
associativity argument be stated about *resolution* rather than about codecs. -/

/-- Resolving two options: the one that admits, or nothing. -/
def resolve₂ {β : Type} (B C : Bool) (E₂ E₃ : Option β) : Option β :=
  match B, C with
  | true, false => E₂
  | false, true => E₃
  | _, _ => none

/-- Resolving a *nested* union: the inner pair resolves first, and the head is consulted
    only where the inner failed. This asymmetry is the whole of §6's hedge. -/
def resolveNested {β : Type} (A : Bool) (inner E₁ : Option β) : Option β :=
  match A, inner with
  | true, none => E₁
  | false, some b => some b
  | _, _ => none

/-- Resolving three options *flat*: all three compete at once. -/
def resolve₃ {β : Type} (A B C : Bool) (E₁ E₂ E₃ : Option β) : Option β :=
  match A, B, C with
  | true, false, false => E₁
  | false, true, false => E₂
  | false, false, true => E₃
  | _, _, _ => none

theorem altCodec_pair_e (o₂ o₃ : OptionSem) (μ' : Option Member) (v : Value) :
    (altCodec [o₂, o₃] μ').e v =
      resolve₂ (o₂.admitV v) (o₃.admitV v) (o₂.c.e v) (o₃.c.e v) := by
  cases hB : o₂.admitV v <;> cases hC : o₃.admitV v <;>
    simp [altCodec, select, List.filter, resolve₂, hB, hC]

theorem altCodec_pair_p (o₂ o₃ : OptionSem) (μ' : Option Member) (a : Attr) :
    (altCodec [o₂, o₃] μ').p a =
      resolve₂ (o₂.admitA a) (o₃.admitA a) (o₂.c.p a) (o₃.c.p a) := by
  cases hB : o₂.admitA a <;> cases hC : o₃.admitA a <;>
    simp [altCodec, select, List.filter, resolve₂, hB, hC]

theorem altCodec_triple_e (o₁ o₂ o₃ : OptionSem) (μ : Option Member) (v : Value) :
    (altCodec [o₁, o₂, o₃] μ).e v =
      resolve₃ (o₁.admitV v) (o₂.admitV v) (o₃.admitV v)
        (o₁.c.e v) (o₂.c.e v) (o₃.c.e v) := by
  cases hA : o₁.admitV v <;> cases hB : o₂.admitV v <;> cases hC : o₃.admitV v <;>
    simp [altCodec, select, List.filter, resolve₃, hA, hB, hC]

theorem altCodec_triple_p (o₁ o₂ o₃ : OptionSem) (μ : Option Member) (a : Attr) :
    (altCodec [o₁, o₂, o₃] μ).p a =
      resolve₃ (o₁.admitA a) (o₂.admitA a) (o₃.admitA a)
        (o₁.c.p a) (o₂.c.p a) (o₃.c.p a) := by
  cases hA : o₁.admitA a <;> cases hB : o₂.admitA a <;> cases hC : o₃.admitA a <;>
    simp [altCodec, select, List.filter, resolve₃, hA, hB, hC]

theorem altCodec_nest_e (o₁ o₂ o₃ : OptionSem) (μ μ' : Option Member) (v : Value) :
    (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] μ')] μ).e v =
      resolveNested (o₁.admitV v) ((altCodec [o₂, o₃] μ').e v) (o₁.c.e v) := by
  have key : (OptionSem.byAttempt (altCodec [o₂, o₃] μ')).admitV v
      = ((altCodec [o₂, o₃] μ').e v).isSome := rfl
  have hc : (OptionSem.byAttempt (altCodec [o₂, o₃] μ')).c = altCodec [o₂, o₃] μ' := rfl
  show (match [o₁, OptionSem.byAttempt (altCodec [o₂, o₃] μ')].filter (·.admitV v) with
        | [o] => o.c.e v | _ => none) = _
  cases hA : o₁.admitV v <;> cases hI : (altCodec [o₂, o₃] μ').e v <;>
    simp only [List.filter, hA, key, hI, hc, Option.isSome, resolveNested]

theorem altCodec_nest_p (o₁ o₂ o₃ : OptionSem) (μ μ' : Option Member) (a : Attr) :
    (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] μ')] μ).p a =
      resolveNested (o₁.admitA a) ((altCodec [o₂, o₃] μ').p a) (o₁.c.p a) := by
  have key : (OptionSem.byAttempt (altCodec [o₂, o₃] μ')).admitA a
      = ((altCodec [o₂, o₃] μ').p a).isSome := rfl
  have hc : (OptionSem.byAttempt (altCodec [o₂, o₃] μ')).c = altCodec [o₂, o₃] μ' := rfl
  show (match [o₁, OptionSem.byAttempt (altCodec [o₂, o₃] μ')].filter (·.admitA a) with
        | [o] => o.c.p a | _ => none) = _
  cases hA : o₁.admitA a <;> cases hI : (altCodec [o₂, o₃] μ').p a <;>
    simp only [List.filter, hA, key, hI, hc, Option.isSome, resolveNested]

/-- The held sets coincide. Nesting a union changes how it *resolves*, never what it
    holds — which is why this half needs no side condition at all. -/
theorem altCodec_assoc_heldSet (o₁ o₂ o₃ : OptionSem) (μa μb : Option Member) (v : Value) :
    (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] μb)] μa).T v
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

/-- **Associativity, with the codecs abstracted away.** Three admission flags, three
    per-option results, and the two ways of resolving them. Whenever both resolve, they
    resolve alike.

    Reading down the eight cases — `A`, `B`, `C` being which option admits — is reading
    §6's hedge:

    * `f f f`, `f t t` — neither side resolves; the inner pair is empty or ambiguous.
    * `f f t`, `f t f`, `t f f` — exactly one option admits; both sides return it.
    * `t f t`, `t t f` — the head and one inner option both claim it; both sides refuse.
    * `t t t` — **§6's row.** The head admits and the inner pair is ambiguous, so the
      nested form's inner union fails and its outer union resolves to the head, while the
      flat form sees three claimants and refuses. One side defined, the other not, which
      is exactly why `≡` cannot see the difference and why the row needs no conditions.
      `Refutations.not_eq_altCodec_assoc` exhibits it concretely. -/
theorem nest_flat_resolve {β : Type} (A B C : Bool) (E₁ E₂ E₃ : Option β) {x y : β}
    (hn : resolveNested A (resolve₂ B C E₂ E₃) E₁ = some x)
    (hf : resolve₃ A B C E₁ E₂ E₃ = some y) : x = y := by
  cases A <;> cases B <;> cases C
  · exact nomatch hn
  · cases E₃ with
    | none => exact nomatch hn
    | some b => exact (Option.some.inj hn).symm.trans (Option.some.inj hf)
  · cases E₂ with
    | none => exact nomatch hn
    | some b => exact (Option.some.inj hn).symm.trans (Option.some.inj hf)
  · exact nomatch hn
  · exact Option.some.inj (hn.symm.trans hf)
  · cases E₃ with
    | none => exact nomatch hf
    | some b => exact nomatch hn
  · cases E₂ with
    | none => exact nomatch hf
    | some b => exact nomatch hn
  · exact nomatch hf

/-- §6: `union(c₁, union(c₂, c₃)) ≡ union(c₁, c₂, c₃)` — with no side condition.

    Each half is three steps: put both sides in closed form, then appeal to
    `nest_flat_resolve`. The write and read halves differ only in `e` versus `p`. -/
theorem equiv_altCodec_assoc (o₁ o₂ o₃ : OptionSem) :
    Codec.Equiv
      (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] (unanimous [o₂.c.μ, o₃.c.μ]))]
        (unanimous [o₁.c.μ, unanimous [o₂.c.μ, o₃.c.μ]]))
      (altCodec [o₁, o₂, o₃] (unanimous [o₁.c.μ, o₂.c.μ, o₃.c.μ])) := by
  refine ⟨altCodec_assoc_heldSet o₁ o₂ o₃ _ _, unanimous_pair_assoc _ _ _, ?_, ?_⟩
  · intro v a a' hn hf
    rw [altCodec_nest_e, altCodec_pair_e] at hn
    rw [altCodec_triple_e] at hf
    exact nest_flat_resolve (o₁.admitV v) (o₂.admitV v) (o₃.admitV v)
      (o₁.c.e v) (o₂.c.e v) (o₃.c.e v) hn hf
  · intro a v v' hn hf
    rw [altCodec_nest_p, altCodec_pair_p] at hn
    rw [altCodec_triple_p] at hf
    exact nest_flat_resolve (o₁.admitA a) (o₂.admitA a) (o₃.admitA a)
      (o₁.c.p a) (o₂.c.p a) (o₃.c.p a) hn hf

/-! ## §6's Hold rows, at term level

Each row's twin, stated where a reader of the specification's §6 would look for it: about a
`Term`, the way `Refutations.lean`'s "Do not hold" rows already are. Every one is its
combinator row through the bridge above, so they cost a line each and buy the property
the representation audit asked for — both halves of §6 in one language. -/

section Terms

/-- §6: `held(c, id, id) ≡ c`. -/
theorem equiv_denote_held_id (t : Term) :
    Codec.Equiv (denote (.held t id id)) (denote t) := equiv_through_id _

/-- §6: `held(held(c, f, g), f′, g′) ≡ held(c, f ∘ f′, g′ ∘ g)`. -/
theorem equiv_denote_held_comp (t : Term) (f g f' g' : Value → Value) :
    Codec.Equiv (denote (.held (.held t f g) f' g'))
      (denote (.held t (f ∘ f') (g' ∘ g))) := equiv_through_comp _ _ _ _ _

/-- §6: `refine(refine(c, q), q′) ≡ refine(c, q ∩ q′)`.

    **The meet is a `closure`, and that is what `Pred` costs.** The equation is about codecs
    and it holds: `equiv_restrict_meet` is unchanged, because `restrict` still takes a
    `Value → Bool` and `denote` hands it `p.eval`. What the reified predicate cannot do is
    keep the *shape*. Two `members` meet in a term the classifier no longer reads, so `Orth`
    declines the right-hand side where it certifies the left. That is the sound direction: a
    declined certificate is a missing proof, never a wrong one.

    For the reader who reaches for a fourth constructor: two `members` at one base meet in a
    `members` over the intersection, where the intersection is nonempty. A discharger that
    needs that reduction states it as a lemma about `Pred`, and `Pred` stays one to one with
    the host's three cases, which is the whole reason it has three. -/
theorem equiv_denote_refine_meet (t : Term) (p p' : Pred) :
    Codec.Equiv (denote (.refine (.refine t p) p'))
      (denote (.refine t (.closure (fun v => p.eval v && p'.eval v)))) :=
  equiv_restrict_meet _ _ _

/-- §6: `refine(c, T) ≡ c` for `⊢ c : T ⇝ μ`. The premise is the row's, read off the
    denotation rather than the judgement — `typed_TSub` is what connects the two. -/
theorem equiv_denote_refine_full (t : Term) (p : Pred)
    (hq : ∀ v, (denote t).T v ↔ p.eval v = true) :
    Codec.Equiv (denote (.refine t p)) (denote t) := equiv_restrict_full _ _ hq

/-- §6: `μ(w(c)) = μ(c)` for the three codec wrappers. The two field wrappers are
    `optional_μ` and `optional_μ`, which are already stated over a denotation. -/
theorem denote_held_μ (t : Term) (f g : Value → Value) :
    (denote (.held t f g)).μ = (denote t).μ := rfl

theorem denote_refine_μ (t : Term) (p : Pred) :
    (denote (.refine t p)).μ = (denote t).μ := rfl

end Terms

end Calculus
