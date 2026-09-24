import Calculus.Objects

/-!
# Sums (§5), and unknown values

`altCodec` over the options' codecs: the first option that acts answers. `opaqCodec` is `altCodec`'s fueled fixpoint over everything self-identifying,
and its number option is `numberCodec`, which holds a numeral exactly.
-/

namespace Calculus

noncomputable section
/-- A list no two of whose entries stand in any relation holds at most one entry. -/
theorem length_le_one_of_pairwise_false {α : Type} {l : List α}
    (h : List.Pairwise (fun _ _ : α => False) l) : l.length ≤ 1 := by
  cases l with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp
    | cons y ys => exact absurd ((List.pairwise_cons.mp h).1 y (by simp)) id

/-- **No value and no attribute is admitted by two options.** The certificate implies it
    (`admitsAtMostOne_of_separated`). -/
def AdmitsAtMostOne (os : List Codec) : Prop :=
  (∀ t, (os.filter (fun c => (c.e t).isSome)).length ≤ 1) ∧
  (∀ a, (os.filter (fun c => (c.p a).isSome)).length ≤ 1)

/-- A union's member: `μ` when unanimous, else `⊤` (§5 `(union)`). -/
def unanimous : List (Option Member) → Option Member
  | [] => none
  | μ :: μs => if μs.all (· == μ) then μ else none

/-- **One side of a sum.** Both halves of `altCodec` are this: act through the first option
    that admits by the admission *that side* reads. Stating the shape once is what lets
    `altCodec_e` and `altCodec_p` be the same theorem at two instances. -/
def select {A B : Type} (os : List Codec) (run : Codec → A → Option B) (x : A) : Option B :=
  (os.find? (fun c => (run c x).isSome)).bind (run · x)

/-- `union`: the sum, resolved by the first admitter. Over lawful, pairwise compatible options
    the order is unobservable (`altCodec_perm`). -/
def altCodec (os : List Codec) (μA : Option Member) : Codec :=
  { T := fun v => ∃ o ∈ os, o.T v
    μ := μA
    e := select os (·.e)
    p := select os (·.p) }

/-! ## Unknown values (§3 `(opaque)`) -/

/-- §3 `(opaque)`'s eight self-identifying options; `rec` is where the recursion goes.

    Named because three statements cite it — `opaqCodec`, `opaq_onKinds`,
    `compat_opaque` — and a list spelled three times can drift twice. The number
    option is `numberCodec`, which holds a numeral exactly. -/
def opaqOptions (rec : Codec) : List Codec :=
  [stringCodec, booleanCodec, binaryCodec, nullCodec, numberCodec,
   setCodec rec, arrayCodec rec, recordCodec rec]

/-- `opaque` is not special: it is the recursive union of everything self-identifying,
    closed under the containers — "the values whose type is recoverable", as a
    fixpoint of the algebra. Its compatibility is kind-disjointness (`compat_opaque`). -/
def opaqCodec : Nat → Codec
  | 0 => .empty
  | fuel+1 => altCodec (opaqOptions (opaqCodec fuel)) none

end

end Calculus
