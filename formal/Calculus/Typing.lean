import Calculus.Denote

/-!
# §3–§5 — The judgement

Mechanization choices, and where they diverge from the doc (each is routine to sharpen):

* **Two indices, as the doc has them**: `⊢ c : T ⇝ μ` is `Typed t T μ`, where `T : Held`
  is the held set built by the rule from its premises' held sets — `℘⁺fin(T)`, `T*`,
  `T₁ × … × Tₙ`, `Name ⇀fin T`, `T + 𝟙`, `⟨n :^π T⟩ ⊕ R(ρ)`, `⋃ Tᵢ` — spelled out as the
  set formers below. The index is determined by the term in every rule, exactly as a
  syntax-directed judgement should be; it is an index rather than a function so the rules
  read as §3 writes them.
* `Typed` keeps only one *syntactic* premise, `(union)`'s **(D)**. Every other side condition
  became a type — see each constructor's own docstring.
  The doc's *semantic* premises — `(held)`'s carrier-restricted iso, `(legacy)`'s
  `ran(r) ⊆ dom(e)` and coherence, and `(union)`'s residual (U) — live in
  `Obligations` (Soundness.lean), which is where they can mention the denotation.
* **`literal` is one rule in §3 and one constructor here.** §3's `(literal)` reads its member
  off a base, which in a naive transcription needs `ℓ : List Value` plus a premise that the
  values share a kind. `literal (k : GroundKind) (x : k.Carrier)` gets that from the *type*:
  with the base as an index, `ℓᵢ ∈ T` is the carrier and the member is a function of the index.
  A set of alternatives is a certified `union` of singletons. `GroundKind` covers all six
  bases, so nothing §3 admits is spelled `refine`.
* **§5's dischargers are in neither list, and that is the rule.** `(union)`'s premises are
  the option judgements and (D); a discharger settles the (U) obligation, and lives with
  `κ`/`ident`/`adm` in `Discharge.lean` — downstream of this file, which is why it could
  not be a premise here even if it were one. Failing to discharge is not refusing:
  `union(literal("A"), held(literal("A"), f, g))` holds disjoint sets, so (D) admits it, and
  `UAtCan` is false of it (`not_uAtCan_literal_held`), which is the calculus working as §5
  describes rather than a gap between them.
* Premises over lists are auxiliary judgements (`TypedList`, …): the kernel refuses
  recursive occurrences nested under `∃`/`∀ ∈` binders.
* `(union)` concludes the doc's unanimous μ, computed by `unanimous` from the option
  judgements (`TypedListμ` keeps their members alongside their held sets).
* `held`'s iso premises are carrier-restricted (`T ≃ I`, not `Value ≃ Value`) and so mention
  `e`, which is why they sit in `Obligations` with the other semantic premises.
  The *rule* carries none of them, and no longer carries the held set's half of the iso
  either: that half is not a premise but the conclusion's index, `fun v => I (f v)` cut by
  the admission of the caller-side term, which is what `through` and `restrict` build.
* `(refine)` concludes `T v ∧ q v` where the doc concludes `q` under the premise
  `q ⊆ T`. The same set, stated without a premise the conclusion can carry.
-/

namespace Calculus

/-! ## Held sets

    §3's `T` — a set of values, written as its characteristic predicate. Each former
    below is one of the doc's, at the rule that builds it. -/

/-- A held set: §3's `T`. -/
abbrev Held := Value → Prop

/-- `℘⁺fin(T)` — the nonempty finite subsets of `T` (§3 `(set)`). -/
def HSet (T : Held) : Held := fun v =>
  (∃ S : NEFinset String, v = .strSet S ∧ ∀ s ∈ S.1, T (.str s)) ∨
  (∃ S : NEFinset WFNumeral, v = .numSet S ∧ ∀ d ∈ S.1, T (.num d)) ∨
  (∃ S : NEFinset Bytes,  v = .binSet S ∧ ∀ b ∈ S.1, T (.bin b))

/-- The held set of a set's **base** — §3 `(set)`'s `T` premise, now a function of the
    index. Each is the ground rule's conclusion at that base, verbatim: `string` holds every
    string, `number` §1's `D`, which the carrier now IS, and `binary` every byte string. -/
def SetBase.held : SetBase → Held
  | .string  => fun v => ∃ s, v = .str s
  | .number  => fun v => ∃ x : WFNumeral, v = .num x
  | .binary  => fun v => ∃ b, v = .bin b

/-- The base's held set **is** its codec's, at every base — the three rows were transcribed
    from the three ground rules, and those rules' codecs carry the same condition. `rfl`, so
    `(set)`'s subset obligation reduces to nothing. -/
theorem SetBase.elem_T : ∀ b : SetBase, b.elem.T = b.held
  | .string | .number | .binary => rfl

/-- `T*` (§3 `(array)`). -/
def HStar (T : Held) : Held :=
  fun v => ∃ vs, v = .arr vs ∧ ∀ x ∈ vs, T x

/-- The positional part of `T₁ × … × Tₙ`, and of `… × T*` when a tail is present:
    the fixed head matched position by position, the tail uniformly. -/
def HTuple : List Held → Option Held → List Value → Prop
  | [], none, vs => vs = []
  | [], some T, vs => ∀ x ∈ vs, T x
  | _ :: _, _, [] => False
  | T :: Ts, tl, v :: vs => T v ∧ HTuple Ts tl vs

/-- `T₁ × … × Tₙ` (§3 `(tuple)`), and `T₁ × … × Tₙ × T*` (`(tuple-tail)`). -/
def HProd (Ts : List Held) (tail : Option Held) : Held :=
  fun v => ∃ vs, v = .arr vs ∧ HTuple Ts tail vs

/-- The positional part of a `list`'s held set: the suffix splits off the right end, and
    what is left is `HTuple`'s prefix-and-spread. `Forall₂` carries both the length of the
    suffix and the holding at each of its positions, so no length premise is owed. -/
def HTupleL (pre : List Held) (sp : Option Held) (suf : List Held) (vs : List Value) : Prop :=
  ∃ front back : List Value,
    vs = front ++ back ∧ List.Forall₂ (fun T v => T v) suf back ∧ HTuple pre sp front

/-- `T₁ × … × Tₚ × T* × U₁ × … × U_s` (§3 `(list)`): the one positional held set. -/
def HList (pre : List Held) (sp : Option Held) (suf : List Held) : Held :=
  fun v => ∃ vs, v = .arr vs ∧ HTupleL pre sp suf vs

/-- **`HProd` is the `HList` with no suffix.** `Forall₂` against `[]` forces the right
    part empty, so the split is trivial and the two say the same thing. -/
theorem HProd_eq_HList (Ts : List Held) (tail : Option Held) :
    HProd Ts tail = HList Ts tail [] := by
  funext v
  refine propext ⟨?_, ?_⟩
  · rintro ⟨vs, rfl, h⟩
    exact ⟨vs, rfl, vs, [], (List.append_nil vs).symm, List.Forall₂.nil, h⟩
  · rintro ⟨vs, rfl, front, back, rfl, hb, h⟩
    cases hb
    exact ⟨front ++ [], rfl, by rwa [List.append_nil]⟩

/-- **`HStar` is the `HList` with one spread and nothing else.** -/
theorem HStar_eq_HList (T : Held) : HStar T = HList [] (some T) [] := by
  rw [show HStar T = HProd [] (some T) from rfl, HProd_eq_HList]

/-- `Name ⇀fin T` (§3 `(record)`). The finite partial map is now literally that: a name
    set and a function on it, so "every value holds `T`" is a statement about the
    function's codomain and needs no membership hypothesis. -/
def HMap (T : Held) : Held :=
  fun v => ∃ keys f, v = .map keys f ∧ ∀ k, T (f k)

/-- `⋃ Tᵢ` (§5 `(union)`). -/
def HUnion (Ts : List Held) : Held :=
  fun v => ∃ T ∈ Ts, T v

/-- The bottom's held set: nothing. It is disjoint from every held set, so (D) admits it
    beside any option. -/
def HNever : Held := fun _ => False

/-- Two options share no value. Asked of every pair, this is (D): the count selector is total
    on the union's held set exactly when no value is held by two options. It is not a discharger
    of (U): `not_uAtCan_literal_held` holds disjoint sets and still fails (U). It is what a
    union's certificate provides. -/
def HDisj (Tx Ty : Held) : Prop := ∀ v, Tx v → ¬ Ty v

/-- §5's **(D)**, `(union)`'s well-formedness side condition: **the union's selector is total
    on the union's held set.** Each held value reaches one option, and that option writes the
    value. (D) is a property of the selector, not of a shape of the options.

    The selector of `altCodec` is the count: an option wins where it is the only option that
    admits the value. For the count, totality is pairwise disjointness of the held sets, and
    `countSel_total` (`Laminar.lean`) proves the codec form from this statement. A nested pair
    fails the count, and `not_TIsDomE_unionLiteralString` is the witness: `"A"` is held, and
    nothing is written. A crossing pair fails it too, and `not_countTotal_xOs` is the witness.
    The least-admitter selector `findSel` is total on a laminar family (`findSel_total`), so a
    union under `findSel` would carry laminarity here instead.

    **The condition is not free.** Every union that the meet builds owes it, and
    `dincomp_of_unionOk` reads it off the union's own certificate. `src/codec/lean.ts` cites it
    too, for the pairs where the host refuses a `never` option and the model permits it.

    **An empty option is the unit of the sum.** An empty option is disjoint from each held set,
    vacuously, so it contributes nothing to `HUnion` and cannot make a union ambiguous. The meet
    builds exactly that union: a `refine` whose predicate holds of nothing that the inner term
    holds is empty, and is not syntactically the bottom.

    **Disjointness is monotone.** A pairwise-disjoint family stays pairwise disjoint when each
    held set shrinks. The meet shrinks each option, so the meet keeps (D). -/
def DIncomp (Ts : List Held) : Prop :=
  Ts.Pairwise HDisj

/-- Pairwise disjointness is (D), and is the form a union's certificate gives. -/
theorem dincomp_of_disjoint {Ts : List Held} (h : Ts.Pairwise HDisj) : DIncomp Ts := h

/-- `⟨n₁ :^π₁ T₁ … nₙ :^πₙ Tₙ⟩ ⊕ R(ρ)` (§4 `(object)`). A binding is `(name, required?,
    held set)`; `R` is the open part — `none` for `drop`/`refuse`, the rest codec's held
    set otherwise. Every `req` name is present, and every present name is either
    declared (and holds its own set) or falls to the open part. -/
def HObject (names : Finset Name) (b : {k // k ∈ names} → Bool × Held) (R : Option Held) :
    Held :=
  fun v => ∃ keys f, v = .map keys f ∧
    (∀ k : {k // k ∈ names}, (b k).1 = true → k.1 ∈ keys) ∧
    (∀ k : {k // k ∈ keys},
      if h : k.1 ∈ names then (b ⟨k.1, h⟩).2 (f k)
      else ∃ T, R = some T ∧ T (f k))

/-- `HOpaque` (§3 `(opaque)`): `opaque`'s held set, the values whose member is recoverable
    from the value alone, as the doc's fixpoint — everything self-identifying, closed under the
    containers. Every `Value` is in `HOpaque`: the number option holds a numeral exactly. -/
inductive HOpaque : Value → Prop where
  | str  (s)  : HOpaque (.str s)
  | bool (b)  : HOpaque (.bool b)
  | bin  (b)  : HOpaque (.bin b)
  | null      : HOpaque .null
  /-- No premise: the carrier is the well-formed numerals, so there is no numeral
      `opaque` cannot write and nothing for a premise to exclude. -/
  | num  (d)  : HOpaque (.num d)
  /-- Non-emptiness carried no premise here any more, because `℘⁺fin` is the type. The
      argument for it stands and is worth keeping: an empty wire set is not writable, and
      its member would not be recoverable from the value anyway — you cannot tell `SS`
      from `NS` at `∅`. Both readings §3 gives of `opaque`'s held set exclude it. What
      changed is where the exclusion lives: `HeldSet.lean` used to exhibit `opaque` refusing
      `strSet ∅`, and that witness is now unstatable. -/
  | strSet (S : NEFinset String)
      (h : ∀ s ∈ S.1, HOpaque (.str s)) : HOpaque (.strSet S)
  | numSet (S : NEFinset WFNumeral)
      (h : ∀ d ∈ S.1, HOpaque (.num d)) : HOpaque (.numSet S)
  | binSet (S : NEFinset Bytes)
      (h : ∀ b ∈ S.1, HOpaque (.bin b)) : HOpaque (.binSet S)
  | arr  (vs) (h : ∀ x ∈ vs, HOpaque x) : HOpaque (.arr vs)
  | map  (keys) (f) (h : ∀ k, HOpaque (f k)) : HOpaque (.map keys f)

/-! ## The judgement -/

mutual

inductive Typed : Term → Held → Option Member → Prop where
  | string  : Typed .string  (fun v => ∃ s, v = .str s) (some .S)
  /-- `number` holds `D` — §1's numeral domain — and not every double. The rule always
      concluded `⊢ number : D ⇝ N`; until `numberCodec` gated, the model's judgement said
      something weaker than the rule it was transcribing. -/
  | number  : Typed .number (fun v => ∃ x : WFNumeral, v = .num x) (some .N)
  | boolean : Typed .boolean (fun v => ∃ b, v = .bool b) (some .BOOL)
  /-- §3 `(null)`: the point held set `{null}`, stored as `⟨NULL, ∗⟩`. -/
  | null : Typed .null (fun v => v = .null) (some .NULL)
  | binary  : Typed .binary  (fun v => ∃ b, v = .bin b) (some .B)
  /-- **§3 `(literal)`, with no premise line left.**

      §3 writes it `⊢ g : T ⇝ μ, g ground; ℓ₁ … ℓₙ ∈ T; n ≥ 1; pairwise distinct`. Every clause
      is a type here: `g ground` is the index `k`; `n ≥ 1` and distinctness are `NEFinset`'s;
      `ℓᵢ ∈ T` is `NEFinset k.Carrier`, which at `number` means the well-formed numerals and
      so carries §1's `ℓ ⊆ D` in the element. The member is `k.member`, a function of the index.

      **The one thing typing the carrier would have cost, and did not.** A transcription in
      `Refutations.lean` used to exhibit a literal that is *held* and unwritable, which is (B)
      failing, and the case against gating the carrier was that gating it deletes the witness.
      It did not, at the time: the witness was about §3's rule, which
      admits an ungated `ℓ` only if you drop `ℓᵢ ∈ T`, so it is stated on an ungated prism that
      is deliberately not a `Term`. What the gate does buy is that `inL` is the whole of
      admission, which makes `adm (.literal .number x)` exact.

      **One value.** Several alternatives are a certified `union` of singletons, and
      `Calculus/LiteralArity1.lean` derives that rule from this one and `Typed.union`. -/
  | literal (k : GroundKind) (x : k.Carrier) :
      Typed (.literal k x) (HLit k x) (some k.member)
  /-- §3 `(set)`, and there is nothing left of the premise line.

      The rule was `⊢ c : T ⇝ μ` plus `setMember μ = some μS`, and the second premise was
      the whole content: `setMember` is partial, so the constructor could be applied to
      element terms the rule then refused. The base is an index, so `T` is `b.held`, `μS` is
      `b.member`, and both are functions rather than premises — the same move `(literal)`
      made when `GroundKind` replaced its three constructors. -/
  | set (b : SetBase) : Typed (.set b) (HSet b.held) (some b.member)
  /-- `(list)`: one rule for the one positional container. `(array)`, `(tuple)` and
      `(tuple-tail)` were three rules of this one, and the theorems below recover each
      spelling. -/
  | list {pre Tpre sp Tsp suf Tsuf} (hp : TypedList pre Tpre) (hs : TypedOpt sp Tsp)
      (hf : TypedList suf Tsuf) :
      Typed (.list pre sp suf) (HList Tpre Tsp Tsuf) (some .L)
  /-- `(held)`: the held set **is** the premise's, pulled back along `f`, and cut by the
      admission of the caller-side term `P`; the cancellation laws are `Obligations`'.

      No premise relating `T` to `I`, because `Codec.through` — what `denote` maps a `held` to
      — *defines* `T := fun v => c.T (f v)`. Carrying the iff instead would leave this the one
      rule whose index its term does not determine. `P` carries no judgement, as the predicate
      of `refine` carries none: the rule reads only the domain of its codec. -/
  | held {t I μ P f g} (h : Typed t I μ) :
      Typed (.held t P f g) (fun v => I (f v) ∧ ((denote P).e v).isSome) μ
  | refine {t T μ p} (h : Typed t T μ) :
      Typed (.refine t p) (fun v => T v ∧ p.eval v) μ
  | lazy {t T μ} (h : Typed t T μ) : Typed (.lazy t) T none
  | opaq : Typed .opaq HOpaque none
  /-- §5's bottom. It writes no value, so it stores no member, and its held set is `False`. -/
  | never : Typed .never HNever none
  /-- §4 `(object)`. The field table is a key set with a function on it, so the
      judgement is **pointwise**: every declared name's field is typed at its binding,
      and the bindings are indexed by the same set — so "the same names, in the same
      order, without repeats" is not a premise, it is the type. `hnd` is gone with it. -/
  | object {body : Body} {bind R} {μs : {k // k ∈ body.fields} → Option Member}
      (hf : ∀ k, TypedField (body.at k) (bind k).2 (bind k).1 (μs k))
      (hr : TypedWild body.wild R) :
      Typed (.object body) (HObject body.fields bind R) (some .M)
  /-- `(union)`: the option judgements, and §5's **(D)** on their held sets. -/
  | union {opts Ts μs} (h : TypedListμ opts Ts μs) (hD : DIncomp Ts) :
      Typed (.union opts) (HUnion Ts) (unanimous μs)

inductive TypedList : List Term → List Held → Prop where
  | nil : TypedList [] []
  | cons {t ts T Ts μ} (h : Typed t T μ) (hs : TypedList ts Ts) :
      TypedList (t :: ts) (T :: Ts)

/-- The option judgements of a `(union)`, held sets and members kept: the rule's
    conclusion is computed from them (`HUnion`, `unanimous`), as in the doc. -/
inductive TypedListμ : List Term → List Held → List (Option Member) → Prop where
  | nil : TypedListμ [] [] []
  | cons {t ts T Ts μ μs} (h : Typed t T μ) (hs : TypedListμ ts Ts μs) :
      TypedListμ (t :: ts) (T :: Ts) (μ :: μs)

inductive TypedListM : List Term → List Held → Prop where
  | nil : TypedListM [] []
  | cons {t ts T Ts} (h : Typed t T (some .M)) (hs : TypedListM ts Ts) :
      TypedListM (t :: ts) (T :: Ts)

inductive TypedOpt : Option Term → Option Held → Prop where
  | none : TypedOpt none none
  | some {t T μ} (h : Typed t T μ) : TypedOpt (some t) (some T)

/-- §4's `⊢ f : T ⊗ π ⇝ μ`; the `Bool` is `π`, `true` for `req`. -/
inductive TypedField : ObjectSlot → Held → Bool → Option Member → Prop where
  | req {t T μ} (h : Typed t T μ) : TypedField (.req t) T true μ
  | optional {t T μ} (h : Typed t T μ) : TypedField (.optional t) T false μ

/-- §4's `⊢ ρ : wild`, carrying `R(ρ)` — `∅` (here `none`) where the body carries no open
    block, the open block's held set otherwise. -/
inductive TypedWild : Option Term → Option Held → Prop where
  | none : TypedWild none none
  | some {t T μ} (h : Typed t T μ) : TypedWild (some t) (some T)

end

/-- **§3 `(record)`, derived.** `record` is the object that declares no name and takes every
    key at one codec, so its rule is `object`'s at the empty key set. It was a constructor,
    and a constructor would now conclude about a term `object` already concludes about: one
    term with two derivations, and two held sets where `typed_T_eq` needs one. -/
theorem HObject_empty (b : {k // k ∈ (∅ : Finset Name)} → Bool × Held) (T : Held) :
    HObject ∅ b (some T) = HMap T := by
  funext v
  -- simp discharges the quantifier over the empty key set through an emptiness lemma that
  -- reaches `Classical.choice`; `Finset.notMem_empty` discharges it directly instead.
  refine propext ⟨?_, ?_⟩
  · rintro ⟨keys, f, rfl, -, h⟩
    refine ⟨keys, f, rfl, fun k => ?_⟩
    have hk := h k
    rw [dif_neg (Finset.notMem_empty k.1)] at hk
    obtain ⟨T', hT', hv⟩ := hk
    exact (Option.some.inj hT') ▸ hv
  · rintro ⟨keys, f, rfl, h⟩
    refine ⟨keys, f, rfl, fun k => absurd k.2 (Finset.notMem_empty k.1), fun k => ?_⟩
    rw [dif_neg (Finset.notMem_empty k.1)]
    exact ⟨T, rfl, h k⟩

/-- §3 `(record)` itself, at the held set the rule states: the object at the empty key set
    holds exactly the maps whose every entry the value term holds. -/
theorem Typed.record {t T μ} (h : Typed t T μ) : Typed (.record t) (HMap T) (some .M) := by
  rw [← HObject_empty (fun k => absurd k.2 (Finset.notMem_empty k.1)) T]
  exact Typed.object (μs := fun k => absurd k.2 (Finset.notMem_empty k.1))
    (fun k => absurd k.2 (Finset.notMem_empty k.1)) (TypedWild.some h)

/-! ## `(array)` and `(tuple)`, recovered from `(list)`

The rules the doc states for the three positional shapes. Each is `(list)` at the shape's
own prefix, spread and suffix, with the held set rewritten by the equation that says the
two held sets are one. They exist so a statement about `.array` or `.tuple` reads as the
rule it belongs to, the way the `Obligations` unfoldings do. -/

/-- `T*` (§3 `(array)`): the spread-only `list`. -/
theorem Typed.array {t T μ} (h : Typed t T μ) : Typed (.array t) (HStar T) (some .L) :=
  (HStar_eq_HList T) ▸ Typed.list TypedList.nil (TypedOpt.some h) TypedList.nil

/-- `T₁ × … × Tₙ` (§3 `(tuple)`), and `… × T*` (`(tuple-tail)`): the suffix-free `list`. -/
theorem Typed.tuple {ts Ts tail Tt} (h : TypedList ts Ts) (ht : TypedOpt tail Tt) :
    Typed (.tuple ts tail) (HProd Ts Tt) (some .L) :=
  (HProd_eq_HList Ts Tt) ▸ Typed.list h ht TypedList.nil

/-! ## Reading a field's judgement

`TypedField`'s indices at a declared name are `(b k).2`, `(b k).1` and `μs k` — none of
them a variable — so `cases` on it cannot eliminate. These two extract what the callers
want without eliminating at the use site. -/

/-- A typed field gives its term, that term's judgement, and its shape. -/
theorem TypedField.term {fd : ObjectSlot} {T π μ} (h : TypedField fd T π μ) :
    ∃ t', Typed t' T μ ∧
      (fd = .req t' ∨ fd = .optional t') := by
  cases h with
  | req h' => exact ⟨_, h', Or.inl rfl⟩
  | optional h' => exact ⟨_, h', Or.inr rfl⟩

/-- …and a required one is not optional. -/
theorem TypedField.not_optional {fd : ObjectSlot} {T π μ} (h : TypedField fd T π μ)
    (hπ : π = true) : ∀ t', fd ≠ .optional t' := by
  cases h with
  | req _ => intro t' hc; exact nomatch hc
  | optional _ => exact absurd hπ (by simp)

/-- …and the same fact read the other way: a field that is not `optional` is required.

    `not_optional` is what a *consumer* of the judgement wants — it has `π = true` and needs
    the shape. Producing `π = true` from the shape is the converse, and `typed_T_eq`'s
    `object` case is where it is needed: there the map's key set is known to contain every
    required name and the guard `valPresentB` is stated by shape, so the two have to be
    exchanged in this direction. Both rows are `rfl`. -/
theorem TypedField.true_of_not_optional {fd : ObjectSlot} {T π μ} (h : TypedField fd T π μ)
    (hno : ∀ t', fd ≠ .optional t') : π = true := by
  cases h with
  | req _ => rfl
  | optional _ => exact absurd rfl (hno _)

end Calculus
