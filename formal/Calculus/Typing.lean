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
* `Typed` keeps only the *syntactic* premises, and there are two: `(union)`'s **(D)** and
  `(dunion)`'s tag arity and disjointness. Every other side condition became a type — see each
  constructor's own docstring.
  The doc's *semantic* premises — `(held)`'s carrier-restricted iso, `(legacy)`'s
  `ran(r) ⊆ dom(e)` and coherence, `(fallback)`'s `v(∗) ∈ dom(e)`, `(custom)`'s laws, and
  `(union)`'s residual (U) — live in `Obligations` (Soundness.lean), which is where they can
  mention the denotation.
* **`literal` is one rule in §3 and one constructor here.** §3's `(literal)` reads its member
  off a base, which in a naive transcription needs `ℓ : List Value` plus a premise that the
  values share a kind. `literal (k : GroundKind) (ls : NEFinset k.Carrier)` gets that from the
  *type*: with the base as an index, homogeneity, nonemptiness and pairwise distinctness are
  Lean's. `GroundKind` covers all six bases, so nothing §3 admits is spelled `refine`.
* **§5's dischargers are in neither list, and that is the rule.** `(union)`'s premises are
  the option judgements and (D); a discharger settles the (U) obligation, and lives with
  `κ`/`ident`/`adm` in `Discharge.lean` — downstream of this file, which is why it could
  not be a premise here even if it were one. Failing to discharge is not refusing:
  `union(array(literal "A"), array(literal "B"))` is `Typed`, and `UAtCan` is false of it
  (`not_uAtCan_array_literals`), which is the calculus working as §5 describes rather
  than a gap between them.
* Premises over lists are auxiliary judgements (`TypedList`, …): the kernel refuses
  recursive occurrences nested under `∃`/`∀ ∈` binders.
* `(union)` concludes the doc's unanimous μ, computed by `unanimous` from the option
  judgements (`TypedListμ` keeps their members alongside their held sets).
* `held`'s iso premises are carrier-restricted (`T ≃ I`, not `Value ≃ Value`) and so mention
  `e`, which is why they sit in `Obligations` with the other semantic premises.
  The *rule* carries none of them, and no longer carries the held set's half of the iso
  either: that half is not a premise but the conclusion's index, `fun v => I (f v)`,
  which is what `through` builds.
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
  (∃ S : NEFinset Double, v = .numSet S ∧ ∀ d ∈ S.1, T (.num d)) ∨
  (∃ S : NEFinset Bytes,  v = .binSet S ∧ ∀ b ∈ S.1, T (.bin b))

/-- The held set of a set's **base** — §3 `(set)`'s `T` premise, now a function of the
    index. Each is the ground rule's conclusion at that base, verbatim: `string` holds every
    string, `number` §1's `D`, `decimal` §1's `Numerals` carried as strings, `binary` every
    byte string. -/
def SetBase.held : SetBase → Held
  | .string  => fun v => ∃ s, v = .str s
  | .number  => fun v => ∃ d, v = .num d ∧ Numeral.WF d.toDec = true
  | .decimal => fun v => ∃ s, v = .str s ∧ Numeral.Stored s = true
  | .binary  => fun v => ∃ b, v = .bin b

/-- The base's held set **is** its codec's, at every base — the four rows were transcribed
    from the four ground rules, and those rules' codecs carry the same condition. `rfl`, so
    `(set)`'s subset obligation reduces to nothing. -/
theorem SetBase.elem_T : ∀ b : SetBase, b.elem.T = b.held
  | .string | .number | .decimal | .binary => rfl

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

/-- `Name ⇀fin T` (§3 `(record)`). The finite partial map is now literally that: a name
    set and a function on it, so "every value holds `T`" is a statement about the
    function's codomain and needs no membership hypothesis. -/
def HMap (T : Held) : Held :=
  fun v => ∃ keys f, v = .map keys f ∧ ∀ k, T (f k)

/-- `T + 𝟙` (§3 `(nullable)`). Idempotent, as §6 requires: the value language has one
    null, so a second `𝟙` adds nothing. -/
def HNull (T : Held) : Held :=
  fun v => T v ∨ v = .null

/-- `⋃ Tᵢ` (§5 `(union)`, `(dunion)`). -/
def HUnion (Ts : List Held) : Held :=
  fun v => ∃ T ∈ Ts, T v

/-- `(dunion)`'s held set: some variant holds the value.

    **`HUnion` over a key set, and not `HUnion` itself.** `HUnion` is a disjunction over a *list*
    and a tag-keyed table has no list — building one needs `Finset.toList`, which reaches
    `Classical.choice`. This is the same disjunction, indexed.

    It does *not* say that the value's own tag picks the variant, though a lookup does. That
    reading is true and belongs where it is used: `T` is an upper bound `Carrier` keeps `e` and
    `p` inside, and asking it of `T` would cost `Carrier` two premises it does not otherwise
    need. -/
def HVariants (variants : MapOf Body) (Ts : {k // k ∈ variants.1} → Held) : Held :=
  fun v => ∃ k, Ts k v

/-- The bottom's held set: nothing. It is a subset of every held set, so (D) fails against
    every other option and `never` is an option of no `union`. -/
def HNever : Held := fun _ => False

/-- §5's **(D)**, `(union)`'s well-formedness side condition, pairwise over the held sets.

    *Incomparability*, not disjointness: disjointness would reject working unions
    (`not_uAtCan_literal_held`). Not a discharger of (U) either — no condition on held sets
    is one — so nothing consumes it; it constrains the judgement's `T`. Contrast `DDisj`,
    the strengthening §5 withdrew. -/
def DIncomp (Ts : List Held) : Prop :=
  Ts.Pairwise fun Tx Ty => ¬ (∀ v, Tx v → Ty v) ∧ ¬ (∀ v, Ty v → Tx v)

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

/-- `Uν` (§3 `(opaque)`): the values whose member is recoverable from the value alone,
    as the doc's fixpoint — everything self-identifying, closed under the containers.
    `lossy = false` is `refuse`, and **refuse is the absence of the `number` option**. -/
inductive HOpaque (lossy : Bool) : Value → Prop where
  | str  (s)  : HOpaque lossy (.str s)
  | bool (b)  : HOpaque lossy (.bool b)
  | bin  (b)  : HOpaque lossy (.bin b)
  | null      : HOpaque lossy .null
  /-- The `D` premise, for the reason `set` carries non-emptiness: a double `opaque` cannot
      **write** has no `N` for its member to be recoverable from. -/
  | num  (d) (h : lossy = true) (hw : Numeral.WF d.toDec = true) : HOpaque lossy (.num d)
  /-- Non-emptiness carried no premise here any more, because `℘⁺fin` is the type. The
      argument for it stands and is worth keeping: an empty wire set is not writable, and
      its member would not be recoverable from the value anyway — you cannot tell `SS`
      from `NS` at `∅`. Both readings §3 gives of `Uν` exclude it. What changed is where
      the exclusion lives: `HeldSet.lean` used to exhibit `opaque` refusing `strSet ∅`,
      and that witness is now unstatable. -/
  | strSet (S : NEFinset String)
      (h : ∀ s ∈ S.1, HOpaque lossy (.str s)) : HOpaque lossy (.strSet S)
  | numSet (S : NEFinset Double)
      (h : ∀ d ∈ S.1, HOpaque lossy (.num d)) : HOpaque lossy (.numSet S)
  | binSet (S : NEFinset Bytes)
      (h : ∀ b ∈ S.1, HOpaque lossy (.bin b)) : HOpaque lossy (.binSet S)
  | arr  (vs) (h : ∀ x ∈ vs, HOpaque lossy x) : HOpaque lossy (.arr vs)
  | map  (keys) (f) (h : ∀ k, HOpaque lossy (f k)) : HOpaque lossy (.map keys f)

/-! ## The judgement -/

mutual

inductive Typed : Term → Held → Option Member → Prop where
  | string  : Typed .string  (fun v => ∃ s, v = .str s) (some .S)
  /-- `number` holds `D` — §1's numeral domain — and not every double. The rule always
      concluded `⊢ number : D ⇝ N`; until `numberCodec` gated, the model's judgement said
      something weaker than the rule it was transcribing. -/
  | number  : Typed .number (fun v => ∃ d, v = .num d ∧ Numeral.WF d.toDec = true) (some .N)
  /-- `decimal` holds `Numerals`, carried as `str` values (§1) — and `Numerals` is §1's
      grammar, not every string. -/
  | decimal : Typed .decimal (fun v => ∃ s, v = .str s ∧ Numeral.Stored s = true) (some .N)
  | boolean : Typed .boolean (fun v => ∃ b, v = .bool b) (some .BOOL)
  /-- §3 `(null)`: the point held set `{null}`, stored as `⟨NULL, ∗⟩`. -/
  | null : Typed .null (fun v => v = .null) (some .NULL)
  | binary  : Typed .binary  (fun v => ∃ b, v = .bin b) (some .B)
  /-- **§3 `(literal)`, with no premise line left.**

      §3 writes it `⊢ g : T ⇝ μ, g ground; ℓ₁ … ℓₙ ∈ T; n ≥ 1; pairwise distinct`. Every clause
      is a type here: `g ground` is the index `k`; `n ≥ 1` and distinctness are `NEFinset`'s;
      `ℓᵢ ∈ T` is `NEFinset k.Carrier`, which at `number` means `WFDouble` and so carries §1's
      `ℓ ⊆ D` in the element. The member is `k.member`, a function of the index.

      **The one thing typing the carrier would have cost, and did not.**
      `literalNRule_holds_what_it_cannot_write` (`Refutations.lean`) exhibits a literal that is
      *held* and unwritable, which is (B) failing, and the case against gating the carrier was
      that gating it deletes the witness. It does not: the witness is about §3's rule, which
      admits an ungated `ℓ` only if you drop `ℓᵢ ∈ T`, so it is stated on an ungated prism that
      is deliberately not a `Term`. What the gate does buy is that `inL` is the whole of
      admission, which makes `adm (.literal .number ls)` exact.

      Not a union of arity-one literals: derivable (`Calculus/LiteralArity1.lean`) but not free,
      since `Term.union` is list-shaped and the bridge from a `Finset` is `Classical.choice`. -/
  | literal (k : GroundKind) (ls : NEFinset k.Carrier) :
      Typed (.literal k ls) (HLit k ls) (some k.member)
  /-- §3 `(set)`, and there is nothing left of the premise line.

      The rule was `⊢ c : T ⇝ μ` plus `setMember μ = some μS`, and the second premise was
      the whole content: `setMember` is partial, so the constructor could be applied to
      element terms the rule then refused. The base is an index, so `T` is `b.held`, `μS` is
      `b.member`, and both are functions rather than premises — the same move `(literal)`
      made when `GroundKind` replaced its three constructors. -/
  | set (b : SetBase) : Typed (.set b) (HSet b.held) (some b.member)
  | array {t T μ} (h : Typed t T μ) : Typed (.array t) (HStar T) (some .L)
  | tuple {ts Ts tail Tt} (h : TypedList ts Ts) (ht : TypedOpt tail Tt) :
      Typed (.tuple ts tail) (HProd Ts Tt) (some .L)
  | record {t T μ} (h : Typed t T μ) : Typed (.record t) (HMap T) (some .M)
  /-- `(held)`: the held set **is** the premise's, pulled back along `f`; the cancellation
      laws are `Obligations`'.

      No premise relating `T` to `I`, because `Codec.through` — what `denote` maps a `held` to
      — *defines* `T := fun v => c.T (f v)`. Carrying the iff instead would leave this the one
      rule whose index its term does not determine. -/
  | held {t I μ f g} (h : Typed t I μ) :
      Typed (.held t f g) (fun v => I (f v)) μ
  | refine {t T μ p} (h : Typed t T μ) :
      Typed (.refine t p) (fun v => T v ∧ p.eval v) μ
  | legacy {t T μ r} (h : Typed t T μ) : Typed (.legacy t r) T μ
  | nullable {t T μ} (h : Typed t T μ) : Typed (.nullable t) (HNull T) none
  | lazy {t T μ} (h : Typed t T μ) : Typed (.lazy t) T none
  | custom (ce cp) : Typed (.custom ce cp) (fun v => (ce v).isSome = true) none
  | opaq (lossy) : Typed (.opaq lossy) (HOpaque lossy) none
  /-- §5's bottom. It writes no value, so it stores no member, and its held set is `False`. -/
  | never : Typed .never HNever none
  /-- §4 `(object)`. The field table is a key set with a function on it, so the
      judgement is **pointwise**: every declared name's field is typed at its binding,
      and the bindings are indexed by the same set — so "the same names, in the same
      order, without repeats" is not a premise, it is the type. `hnd` is gone with it. -/
  | object {body : Body} {bind R} {μs : {k // k ∈ body.fields} → Option Member}
      (hf : ∀ k, TypedField (body.at k) (bind k).2 (bind k).1 (μs k))
      (hr : TypedRest body.rest R) :
      Typed (.object body) (HObject body.fields bind R) (some .M)
  /-- `(union)`: the option judgements, and §5's **(D)** on their held sets. -/
  | union {opts Ts μs} (h : TypedListμ opts Ts μs) (hD : DIncomp Ts) :
      Typed (.union opts) (HUnion Ts) (unanimous μs)
  /-- §5 `(dunion)`, **keyed by the tag**, where the premises used to carry what the key set
      now carries.

      `hone` did five jobs. `tagsOf` is empty for everything but an object whose `d` field is a
      `req` literal at a tag base, so asking anything of it forced *object*, *`d` declared*,
      *`req` rather than `optional`/`fallback`*, and *a literal at a tag base*; `card = 1` added
      that the literal is a singleton. `hdisj` did a sixth, that no two options answer to one tag.

      The table does four of the six. *Object* is the codomain. *Arity one* is a function on a key
      set. *Distinctness* is `Finset`. And the key is the tag, so there is no tag set to compare.

      **What is left is one fact, and it is the one a table cannot state**: that a variant's own
      `d` field agrees with its key. The field cannot go — the codec writes the tag out of it, and
      the host's variant declares it — so the agreement is a premise. `hone` is that, and
      `tagsOf_ne_nil` is still the inversion that unpacks it.

      The conclusion moved too. `HUnion` is a disjunction over a list and there is no list;
      `HVariants` is the same disjunction over the key set. -/
  | dunion {d} {variants : MapOf Body} {Ts : {k // k ∈ variants.1} → Held}
      (h : ∀ k, Typed (.object (variants.2 k)) (Ts k) (some .M))
      (hone : ∀ k, (variants.2 k).tags d = {k.1}) :
      Typed (.dunion d variants) (HVariants variants Ts) (some .M)

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
inductive TypedField : Field → Held → Bool → Option Member → Prop where
  | req {t T μ} (h : Typed t T μ) : TypedField (.req t) T true μ
  | optional {t T μ} (h : Typed t T μ) : TypedField (.optional t) T false μ
  | fallback {t T μ v} (h : Typed t T μ) : TypedField (.fallback t v) T true μ

/-- §4's `⊢ ρ : rest`, carrying `R(ρ)` — `∅` (here `none`) for the two string policies,
    the rest codec's held set otherwise. -/
inductive TypedRest : Rest → Option Held → Prop where
  | drop : TypedRest .drop none
  | refuse : TypedRest .refuse none
  | codec {t T μ} (h : Typed t T μ) : TypedRest (.codec t) (some T)

end

/-! ## Reading a field's judgement

`TypedField`'s indices at a declared name are `(b k).2`, `(b k).1` and `μs k` — none of
them a variable — so `cases` on it cannot eliminate. These two extract what the callers
want without eliminating at the use site. -/

/-- A typed field gives its term, that term's judgement, and which of the three shapes
    the field has. -/
theorem TypedField.term {fd : Field} {T π μ} (h : TypedField fd T π μ) :
    ∃ t', Typed t' T μ ∧
      (fd = .req t' ∨ fd = .optional t' ∨ ∃ v, fd = .fallback t' v) := by
  cases h with
  | req h' => exact ⟨_, h', Or.inl rfl⟩
  | optional h' => exact ⟨_, h', Or.inr (Or.inl rfl)⟩
  | fallback h' => exact ⟨_, h', Or.inr (Or.inr ⟨_, rfl⟩)⟩

/-- …and a *required* one is not `optional`, which is §4's `fallback` concluding `req`
    read backwards. -/
theorem TypedField.not_optional {fd : Field} {T π μ} (h : TypedField fd T π μ)
    (hπ : π = true) : ∀ t', fd ≠ .optional t' := by
  cases h with
  | req _ => intro t' hc; exact nomatch hc
  | fallback _ => intro t' hc; exact nomatch hc
  | optional _ => exact absurd hπ (by simp)

/-- …and the same fact read the other way: a field that is not `optional` is required.

    `not_optional` is what a *consumer* of the judgement wants — it has `π = true` and needs
    the shape. Producing `π = true` from the shape is the converse, and `typed_T_eq`'s
    `object` case is where it is needed: there the map's key set is known to contain every
    required name and the guard `valPresentB` is stated by shape, so the two have to be
    exchanged in this direction. Both rows are `rfl`; §4's "`fallback` concludes `req`" is
    the second one. -/
theorem TypedField.true_of_not_optional {fd : Field} {T π μ} (h : TypedField fd T π μ)
    (hno : ∀ t', fd ≠ .optional t') : π = true := by
  cases h with
  | req _ => rfl
  | fallback _ => rfl
  | optional _ => exact absurd rfl (hno _)

end Calculus
