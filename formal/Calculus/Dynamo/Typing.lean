import Calculus.Dynamo.Guarded
import Calculus.Lang.Typing

/-!
# §3–§5 — The judgement

Mechanization choices, and where they diverge from the doc (each is routine to sharpen):

* **Two indices, as the doc has them**: `⊢ c : T ⇝ μ` is `Typed t T μ`, where `T : Held`
  is the held set built by the rule from its premises' held sets — `℘⁺fin(T)`, `T*`,
  `T₁ × … × Tₙ`, `Name ⇀fin T`, `T + 𝟙`, `⟨n :^π T⟩ ⊕ R(ρ)`, `⋃ Tᵢ` — spelled out as the
  set formers below. The index is determined by the term in every rule, exactly as a
  syntax-directed judgement should be; it is an index rather than a function so the rules
  read as §3 writes them.
* `Typed` keeps no *syntactic* premise. Every side condition became a type — see each
  rule's own docstring.
  The doc's *semantic* premises — `(held)`'s carrier-restricted iso, `(legacy)`'s
  `ran(r) ⊆ dom(e)` and coherence, and `(union)`'s pairwise compatibility — live in
  `Obligations` (Soundness.lean), which is where they can mention the denotation.
* **`literal` is one rule in §3 and one primitive here**, `Ground.literal`, which the generic
  rule `Alg.Typed.prim` types. §3's `(literal)` reads its member
  off a base, which in a naive transcription needs `ℓ : List Value` plus a premise that the
  values share a kind. `literal (k : GroundKind) (x : k.Carrier)` gets that from the *type*:
  with the base as an index, `ℓᵢ ∈ T` is the carrier and the member is a function of the index.
  A set of alternatives is a certified `union` of singletons. `GroundKind` covers all six
  bases, so nothing §3 admits is spelled `refine`.
* **§5's dischargers are in neither list, and that is the rule.** `(union)`'s premises are
  the option judgements; a discharger settles the compatibility obligation, and lives in
  `Discharge.lean`, downstream of this file.
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

open Alg (Term.guarded)

export Alg (HTuple HTupleL HUnion HNever)

/-! ## Held sets

    §3's `T` — a set of values, written as its characteristic predicate. Each former
    below is one of the doc's, at the rule that builds it. -/

/-- A held set: §3's `T`. -/
abbrev Held := Value → Prop

/-- `T*` (§3 `(array)`). -/
def HStar (T : Held) : Held :=
  fun v => ∃ vs, v = .arr vs ∧ ∀ x ∈ vs, T x

/-- `T₁ × … × Tₙ` (§3 `(tuple)`), and `T₁ × … × Tₙ × T*` (`(tuple-tail)`). -/
def HProd (Ts : List Held) (tail : Option Held) : Held :=
  fun v => ∃ vs, v = .arr vs ∧ HTuple Ts tail vs

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

/-! ## The judgement

The judgement is `Alg.Typed` at the DynamoDB signature. Each rule below keeps its DynamoDB
spelling at the DynamoDB held set, and `Typed.casesD` gives each case at the same held set. -/

/-- The judgement of DynamoDB. -/
abbrev Typed : Term → Held → Option Member → Prop := Alg.Typed (S := dynSyn)
abbrev TypedList : List Term → List Held → Prop := Alg.TypedList (S := dynSyn)
abbrev TypedListμ : List Term → List Held → List (Option Member) → Prop :=
  Alg.TypedListμ (S := dynSyn)
abbrev TypedOpt : Option Term → Option Held → Prop := Alg.TypedOpt (S := dynSyn)
abbrev TypedField : ObjectSlot → Held → Bool → Option Member → Prop := Alg.TypedField (S := dynSyn)
abbrev TypedWild : Option Term → Option Held → Prop := Alg.TypedWild (S := dynSyn)

namespace TypedList export Alg.TypedList (nil cons «forall») end TypedList
namespace TypedListμ export Alg.TypedListμ (nil cons «forall» mem) end TypedListμ
namespace TypedOpt export Alg.TypedOpt (none some) end TypedOpt
namespace TypedField
export Alg.TypedField (req optional term not_optional true_of_not_optional)
end TypedField
namespace TypedWild export Alg.TypedWild (none some) end TypedWild

/-- §3's ground rules: the held set is the base codec's. At `number` that set is `D`, §1's
    numeral domain, and at `null` it is the point `{null}`. -/
theorem Typed.base (k : GroundKind) : Typed (.base k) (baseCodec k).T (some k.member) :=
  Alg.Typed.prim (S := dynSyn) (Ground.base k)

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
    `Calculus/Dynamo/LiteralArity1.lean` derives that rule from this one and `Typed.union`. -/
theorem Typed.literal (k : GroundKind) (x : k.Carrier) :
    Typed (.literal k x) (HLit k x) (some k.member) :=
  Alg.Typed.prim (S := dynSyn) (Ground.literal k x)

/-- §3 `(set)`: the element's judgement, lifted. The held set is `℘⁺fin` of the element's,
    and the member is `setMember` of the element's.

    **No premise names a base.** That a stored set holds elements of one member of `S`, `N`
    or `B` is the DynamoDB universe's rule, and `Obligations` carries it as `SetElem`, the
    way it carries `(union)`'s compatibility. -/
theorem Typed.set {t T μ} (h : Typed t T μ) : Typed (.set t) (HSet T) (μ.bind setMember) :=
  Alg.Typed.set rfl h

/-- `(list)`: `(array)`, `(tuple)` and `(tuple-tail)` were three rules of this one, and the
    theorems below recover each spelling. -/
theorem Typed.list {pre Tpre sp Tsp suf Tsuf} (hp : TypedList pre Tpre) (hs : TypedOpt sp Tsp)
    (hf : TypedList suf Tsuf) : Typed (.list pre sp suf) (HList Tpre Tsp Tsuf) (some .L) :=
  Alg.Typed.list (S := dynSyn) (L := dList) rfl hp hs hf

/-- The held set of a `held`, at the DynamoDB denotation. -/
theorem held_index_eq (I : Held) (P : Term) (f : Value → Value) :
    (fun v => I (f v) ∧ ((denote P).e v).isSome)
      = fun v => I (f v) ∧ ((Alg.denote P).e v).isSome := by
  rw [denote_eq_alg]

/-- The held set of a `mu`, at the DynamoDB denotation. -/
theorem mu_index_eq (b : Term) :
    (fun v => (denote (.mu b)).T v) = fun v => (Alg.denote (.mu b)).T v := by
  rw [denote_eq_alg]

/-- `(held)`, at the DynamoDB denotation of the caller-side term. -/
theorem Typed.held {t I μ P f g} (h : Typed t I μ) :
    Typed (.held t P f g) (fun v => I (f v) ∧ ((denote P).e v).isSome) μ := by
  rw [held_index_eq]; exact Alg.Typed.held h

/-- `(refine)`: the held set is the premise's, cut by the predicate. -/
theorem Typed.refine {t T μ p} (h : Typed t T μ) :
    Typed (.refine t p) (fun v => T v ∧ p.eval v) μ :=
  Alg.Typed.refine h

/-- §3 `(opaque)`: the held set is `HOpaque`. -/
theorem Typed.opaq : Typed .opaq HOpaque none := Alg.Typed.opaq

/-- §5's bottom: it holds nothing and stores no member. -/
theorem Typed.never : Typed .never HNever none := Alg.Typed.never

/-- §4 `(object)`, at the `map` prism. -/
theorem Typed.object {body : Body} {bind R} {μs : {k // k ∈ body.fields} → Option Member}
    (hf : ∀ k, TypedField (body.at k) (bind k).2 (bind k).1 (μs k))
    (hr : TypedWild body.wild R) :
    Typed (.object body) (HObject body.fields bind R) (some .M) :=
  Alg.Typed.object (S := dynSyn) (F := dMap) rfl hf hr

/-- `(union)`: the union of the options' held sets, at their unanimous member. -/
theorem Typed.union {opts Ts μs} (h : TypedListμ opts Ts μs) :
    Typed (.union opts) (HUnion Ts) (unanimous μs) :=
  Alg.Typed.union h

/-- A variable, read closed, holds nothing. -/
theorem Typed.var (i : Nat) : Typed (.var i) HNever none := Alg.Typed.var i

/-- `mu`, at the DynamoDB denotation of the binder. -/
theorem Typed.mu {b T μ} (hg : (Term.mu b).guarded = true) (h : Typed b T μ) :
    Typed (.mu b) (fun v => (denote (.mu b)).T v) none := by
  rw [mu_index_eq]; exact Alg.Typed.mu hg h

/-- **Case analysis on a DynamoDB judgement**, with the primitive rule split into `base` and
    `literal`, and each case at its DynamoDB held set. `cases` uses this eliminator for every
    `Typed`. -/
@[elab_as_elim, cases_eliminator]
theorem Typed.casesD {motive : ∀ t T μ, Typed t T μ → Prop}
    (base : ∀ k, motive (.base k) (baseCodec k).T (some k.member) (.base k))
    (literal : ∀ k x, motive (.literal k x) (HLit k x) (some k.member) (.literal k x))
    (set : ∀ {t T μ} (h : Typed t T μ), motive (.set t) (HSet T) (μ.bind setMember) (.set h))
    (list : ∀ {pre Tpre sp Tsp suf Tsuf} (hp : TypedList pre Tpre) (hs : TypedOpt sp Tsp)
      (hf : TypedList suf Tsuf),
      motive (.list pre sp suf) (HList Tpre Tsp Tsuf) (some .L) (.list hp hs hf))
    (held : ∀ {t I μ P f g} (h : Typed t I μ),
      motive (.held t P f g) (fun v => I (f v) ∧ ((denote P).e v).isSome) μ (.held h))
    (refine : ∀ {t T μ p} (h : Typed t T μ),
      motive (.refine t p) (fun v => T v ∧ p.eval v) μ (.refine h))
    (opaq : motive .opaq HOpaque none .opaq)
    (never : motive .never HNever none .never)
    (object : ∀ {body : Body} {bind R} {μs : {k // k ∈ body.fields} → Option Member}
      (hf : ∀ k, TypedField (body.at k) (bind k).2 (bind k).1 (μs k))
      (hr : TypedWild body.wild R),
      motive (.object body) (HObject body.fields bind R) (some .M) (.object hf hr))
    (union : ∀ {opts Ts μs} (h : TypedListμ opts Ts μs),
      motive (.union opts) (HUnion Ts) (unanimous μs) (.union h))
    (var : ∀ i, motive (.var i) HNever none (.var i))
    (mu : ∀ {b T μ} (hg : (Term.mu b).guarded = true) (h : Typed b T μ),
      motive (.mu b) (fun v => (denote (.mu b)).T v) none (.mu hg h)) :
    ∀ {t T μ} (h : Typed t T μ), motive t T μ h := by
  intro t T μ h
  cases h with
  | prim g =>
    cases g with
    | base k => exact base k
    | literal k x => exact literal k x
  | set hL h => cases hL; exact set h
  | list hL hp hs hf => cases hL; exact list hp hs hf
  | @held t I μ P f g h =>
    have hm : ∀ T' (h' : Typed (.held t P f g) T' μ),
        T' = (fun v => I (f v) ∧ ((denote P).e v).isSome) → motive _ T' μ h' := by
      intro T' h' e; subst e; exact held h
    exact hm _ _ (held_index_eq I P f).symm
  | refine h => exact refine h
  | opaq => exact opaq
  | never => exact never
  | object hF hf hr => cases hF; exact object hf hr
  | union h => exact union h
  | var i => exact var i
  | @mu b T μ hg h =>
    have hm : ∀ T' (h' : Typed (.mu b) T' none),
        T' = (fun v => (denote (.mu b)).T v) → motive _ T' none h' := by
      intro T' h' e; subst e; exact mu hg h
    exact hm _ _ (mu_index_eq b).symm

inductive TypedListM : List Term → List Held → Prop where
  | nil : TypedListM [] []
  | cons {t ts T Ts} (h : Typed t T (some .M)) (hs : TypedListM ts Ts) :
      TypedListM (t :: ts) (T :: Ts)

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

end Calculus
