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
* `Typed` keeps only the *syntactic and fuel-free* premises (set member, literal
  side conditions, `(dunion)` tag disjointness, object name distinctness).
  The doc's *semantic* premises — `(held)`'s carrier-restricted iso, `(legacy)`'s
  `ran(r) ⊆ dom(e)` and coherence, `(nullable)`'s null-honesty, `(fallback)`'s
  `v(∗) ∈ dom(e)`, `(custom)`'s laws, and `(union)`'s residual (U) — are fuel-indexed
  and live in `Obligations` (Soundness.lean), consumed by the theorem. Same premises,
  fueled form.
* Premises over lists are auxiliary judgements (`TypedList`, …): the kernel refuses
  recursive occurrences nested under `∃`/`∀ ∈` binders.
* `(union)` concludes the doc's unanimous μ, computed by `unanimous` from the option
  judgements (`TypedListμ` keeps their members alongside their held sets).
* `held`'s iso premises are carrier-restricted (`T ≃ I`, not `Value ≃ Value`) and so
  mention `e` — fuel-indexed, hence in `Obligations` with the other semantic premises.
  What the *rule* carries is the held set's half of the iso, `T v ↔ I (f v)`, which is
  syntactic and is what `through` builds.
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
def HSet (T : Held) : Held :=
  fun v => ∃ vs, v = .set vs ∧ vs ≠ [] ∧ ∀ x ∈ vs, T x

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

/-- `Name ⇀fin T` (§3 `(record)`). -/
def HMap (T : Held) : Held :=
  fun v => ∃ kvs, v = .map kvs ∧ ∀ kv ∈ kvs, T kv.2

/-- `T + 𝟙` (§3 `(nullable)`). Idempotent, as §6 requires: the value language has one
    null, so a second `𝟙` adds nothing. -/
def HNull (T : Held) : Held :=
  fun v => T v ∨ v = .null

/-- `⋃ Tᵢ` (§5 `(union)`, `(dunion)`). -/
def HUnion (Ts : List Held) : Held :=
  fun v => ∃ T ∈ Ts, T v

/-- `⟨n₁ :^π₁ T₁ … nₙ :^πₙ Tₙ⟩ ⊕ R(ρ)` (§4 `(object)`). A binding is `(name, required?,
    held set)`; `R` is the open part — `none` for `drop`/`refuse`, the rest codec's held
    set otherwise. Every `req` name is present, and every present name is either
    declared (and holds its own set) or falls to the open part. -/
def HObject (binds : List (Name × Bool × Held)) (R : Option Held) : Held :=
  fun v => ∃ kvs, v = .map kvs ∧
    (∀ nb ∈ binds, nb.2.1 = true → (kvs.lookup nb.1).isSome) ∧
    (∀ k x, kvs.lookup k = some x →
      match binds.lookup k with
      | some b => b.2 x
      | none => ∃ T, R = some T ∧ T x)

/-- `Uν` (§3 `(opaque)`): the values whose member is recoverable from the value alone,
    as the doc's fixpoint — everything self-identifying, closed under the containers.
    `lossy = false` is `refuse`, and **refuse is the absence of the `number` option**. -/
inductive HOpaque (lossy : Bool) : Value → Prop where
  | str  (s)  : HOpaque lossy (.str s)
  | bool (b)  : HOpaque lossy (.bool b)
  | bin  (b)  : HOpaque lossy (.bin b)
  | null      : HOpaque lossy .null
  | num  (d) (h : lossy = true) : HOpaque lossy (.num d)
  /-- Non-emptiness is not decoration: §1's `SS`/`NS`/`BS` are `℘⁺fin`, so there is no
      empty wire set to write, and an empty set's member is not recoverable from the
      value anyway — you cannot tell `SS` from `NS`. Both readings §3 gives of `Uν` (the
      prose one, and the fixpoint `union(…, set(opaque), …)` whose `(set)` rule carries
      `vs ≠ []`) exclude it. `HeldSet.lean` has the witness. -/
  | set  (vs) (hne : vs ≠ []) (h : ∀ x ∈ vs, HOpaque lossy x) : HOpaque lossy (.set vs)
  | arr  (vs) (h : ∀ x ∈ vs, HOpaque lossy x) : HOpaque lossy (.arr vs)
  | map  (kvs) (h : ∀ kv ∈ kvs, HOpaque lossy kv.2) : HOpaque lossy (.map kvs)

/-! ## The judgement -/

mutual

inductive Typed : Term → Held → Option Member → Prop where
  | string  : Typed .string  (fun v => ∃ s, v = .str s) (some .S)
  | number  : Typed .number  (fun v => ∃ d, v = .num d) (some .N)
  /-- `decimal` holds `Numerals`, carried as `str` values (§1) — and `Numerals` is §1's
      grammar, not every string. -/
  | decimal : Typed .decimal (fun v => ∃ s, v = .str s ∧ Numeral.WF s = true) (some .N)
  | boolean : Typed .boolean (fun v => ∃ b, v = .bool b) (some .BOOL)
  /-- §3 `(null)`: the point held set `{null}`, stored as `⟨NULL, ∗⟩`. -/
  | null : Typed .null (fun v => v = .null) (some .NULL)
  | binary  : Typed .binary  (fun v => ∃ b, v = .bin b) (some .B)
  | numeric (q) : Typed (.numeric q) (fun v => ∃ d, q d ∧ v = .num d) (some .N)
  | literalS (ls : List String) (hne : ls ≠ []) (hnd : ls.Nodup) :
      Typed (.literalS ls) (fun v => ∃ s, s ∈ ls ∧ v = .str s) (some .S)
  | literalN (ls : List Double) (hne : ls ≠ []) (hnd : ls.Nodup) :
      Typed (.literalN ls) (fun v => ∃ d, d ∈ ls ∧ v = .num d) (some .N)
  | set {t T μ μS} (h : Typed t T (some μ)) (hs : setMember μ = some μS) :
      Typed (.set t) (HSet T) (some μS)
  | array {t T μ} (h : Typed t T μ) : Typed (.array t) (HStar T) (some .L)
  | tuple {ts Ts tail Tt} (h : TypedList ts Ts) (ht : TypedOpt tail Tt) :
      Typed (.tuple ts tail) (HProd Ts Tt) (some .L)
  | record {t T μ} (h : Typed t T μ) : Typed (.record t) (HMap T) (some .M)
  /-- `(held)`: the carrier half of the iso is the rule's, the cancellation laws are
      `Obligations`'. -/
  | held {t I T μ f g} (h : Typed t I μ) (hT : ∀ v, T v ↔ I (f v)) :
      Typed (.held t f g) T μ
  | refine {t T μ q} (h : Typed t T μ) :
      Typed (.refine t q) (fun v => T v ∧ q v) μ
  | legacy {t T μ r} (h : Typed t T μ) : Typed (.legacy t r) T μ
  | nullable {t T μ} (h : Typed t T μ) : Typed (.nullable t) (HNull T) none
  | lazy {t T μ} (h : Typed t T μ) : Typed (.lazy t) T none
  | custom (ce cp) : Typed (.custom ce cp) (fun v => (ce v).isSome = true) none
  | opaq (lossy) : Typed (.opaq lossy) (HOpaque lossy) none
  | object {fields binds rest R} (hf : TypedFields fields binds)
      (hnd : (fields.map (·.1)).Nodup) (hr : TypedRest rest R) :
      Typed (.object fields rest) (HObject binds R) (some .M)
  | union {opts Ts μs} (h : TypedListμ opts Ts μs) :
      Typed (.union opts) (HUnion Ts) (unanimous μs)
  | dunion {d opts Ts} (h : TypedListM opts Ts)
      (htags : ∀ t' ∈ opts, tagsOf d t' ≠ [])
      (hdisj : List.Pairwise (fun a b => ∀ tag ∈ tagsOf d a, tag ∉ tagsOf d b) opts) :
      Typed (.dunion d opts) (HUnion Ts) (some .M)

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

inductive TypedFields : List (Name × Field) → List (Name × Bool × Held) → Prop where
  | nil : TypedFields [] []
  | cons {k f fs binds T π μ} (h : TypedField f T π μ) (hs : TypedFields fs binds) :
      TypedFields ((k, f) :: fs) ((k, π, T) :: binds)

/-- §4's `⊢ ρ : rest`, carrying `R(ρ)` — `∅` (here `none`) for the two string policies,
    the rest codec's held set otherwise. -/
inductive TypedRest : Rest → Option Held → Prop where
  | drop : TypedRest .drop none
  | refuse : TypedRest .refuse none
  | codec {t T μ} (h : Typed t T μ) : TypedRest (.codec t) (some T)

end

end Calculus
