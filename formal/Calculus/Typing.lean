import Calculus.Denote

/-!
# §3–§5 — The judgement

Mechanization choices, and where they diverge from the doc (each is routine to sharpen):

* The held-set index `T` is elided: `Lawful` never reads it, and the denotation carries
  its own `T` for §5 (D). Reinstating the two-index form is mechanical.
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
  judgements (`TypedListμ` keeps their members).
* `held`'s iso premises are carrier-restricted (`T ≃ I`, not `Value ≃ Value`) and so
  mention `e` — fuel-indexed, hence in `Obligations` with the other semantic premises.
-/

namespace Calculus

mutual

inductive Typed : Term → Option Member → Prop where
  | string  : Typed .string  (some .S)
  | number  : Typed .number  (some .N)
  | decimal : Typed .decimal (some .N)
  | boolean : Typed .boolean (some .BOOL)
  | binary  : Typed .binary  (some .B)
  | numeric (q) : Typed (.numeric q) (some .N)
  | literalS (ls : List String) (hne : ls ≠ []) (hnd : ls.Nodup) :
      Typed (.literalS ls) (some .S)
  | literalN (ls : List Double) (hne : ls ≠ []) (hnd : ls.Nodup) :
      Typed (.literalN ls) (some .N)
  | set {t μ μS} (h : Typed t (some μ)) (hs : setMember μ = some μS) :
      Typed (.set t) (some μS)
  | array {t μ} (h : Typed t μ) : Typed (.array t) (some .L)
  | tuple {ts tail} (h : TypedList ts) (ht : TypedOpt tail) :
      Typed (.tuple ts tail) (some .L)
  | record {t μ} (h : Typed t μ) : Typed (.record t) (some .M)
  | held {t μ f g} (h : Typed t μ) : Typed (.held t f g) μ
  | refine {t μ q} (h : Typed t μ) : Typed (.refine t q) μ
  | legacy {t μ r} (h : Typed t μ) : Typed (.legacy t r) μ
  | nullable {t μ} (h : Typed t μ) : Typed (.nullable t) none
  | lazy {γ μ} (h : Typed (γ ()) μ) : Typed (.lazy γ) none
  | custom (ce cp) : Typed (.custom ce cp) none
  | opaq (lossy) : Typed (.opaq lossy) none
  | object {fields rest} (hf : TypedFields fields)
      (hnd : (fields.map (·.1)).Nodup) (hr : TypedRest rest) :
      Typed (.object fields rest) (some .M)
  | union {opts μs} (h : TypedListμ opts μs) : Typed (.union opts) (unanimous μs)
  | dunion {d opts} (h : TypedListM opts)
      (htags : ∀ t' ∈ opts, tagsOf d t' ≠ [])
      (hdisj : List.Pairwise (fun a b => ∀ tag ∈ tagsOf d a, tag ∉ tagsOf d b) opts) :
      Typed (.dunion d opts) (some .M)

inductive TypedList : List Term → Prop where
  | nil : TypedList []
  | cons {t ts μ} (h : Typed t μ) (hs : TypedList ts) : TypedList (t :: ts)

/-- The option judgements of a `(union)`, members kept: the rule's conclusion is
    computed from them (`unanimous`), as in the doc. -/
inductive TypedListμ : List Term → List (Option Member) → Prop where
  | nil : TypedListμ [] []
  | cons {t ts μ μs} (h : Typed t μ) (hs : TypedListμ ts μs) :
      TypedListμ (t :: ts) (μ :: μs)

inductive TypedListM : List Term → Prop where
  | nil : TypedListM []
  | cons {t ts} (h : Typed t (some .M)) (hs : TypedListM ts) : TypedListM (t :: ts)

inductive TypedOpt : Option Term → Prop where
  | none : TypedOpt none
  | some {t μ} (h : Typed t μ) : TypedOpt (some t)

inductive TypedField : Field → Option Member → Prop where
  | req {t μ} (h : Typed t μ) : TypedField (.req t) μ
  | optional {t μ} (h : Typed t μ) : TypedField (.optional t) μ
  | fallback {t μ v} (h : Typed t μ) : TypedField (.fallback t v) μ

inductive TypedFields : List (Name × Field) → Prop where
  | nil : TypedFields []
  | cons {k f fs μ} (h : TypedField f μ) (hs : TypedFields fs) :
      TypedFields ((k, f) :: fs)

inductive TypedRest : Rest → Prop where
  | drop : TypedRest .drop
  | refuse : TypedRest .refuse
  | codec {t μ} (h : Typed t μ) : TypedRest (.codec t)

end

end Calculus
