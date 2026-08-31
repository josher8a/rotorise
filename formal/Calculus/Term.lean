import Calculus.Codec

/-!
# §3–§4 — The term language

Deep embedding. Notes:

* Predicates carried by terms (`refine`) are `Bool`-valued so the denotation
  needs no classical choice; the doc's subsets are their coercions.
* `custom` carries its pair as data; its *laws* are premises of the typing rule (§3),
  exactly as in the doc.
* `opaque` is a Lean keyword, hence `opaq`.
* Fields (§4) are a separate inductive — the stratification is the point: no `Term`
  position accepts a `Field`.
-/

namespace Calculus

mutual

inductive Term where
  | string | number | decimal | boolean | binary
  /-- §3 `(null)`: the `NULL` point. `Value.null` and `⟨NULL, ∗⟩` are in §1 and
      `nullCodec` is one of `opaque`'s options, but until now no *term* denoted it —
      so a schema could not say "this attribute is exactly NULL". -/
  | null
  /-- §3 `(literal)` at arity one: a single value, whose base — and so whose member — is
      fixed by its kind. The n-ary form is surface syntax for the union of these. -/
  | literal (v : Value)
  /-- §3 `(literal-S)`. The alternatives are a **nonempty finite set**, which is what the
      rule's `hne`/`hnd` premises said about a list: order does not matter to `∈`, so two
      orderings were two terms denoting one codec, and a repeat was a term the rule had to
      exclude by hand. Both premises are gone with the type. -/
  | literalS (ls : NEFinset String)
  | literalN (ls : NEFinset Double)
  | set      (elem : Term)
  | array    (elem : Term)
  /-- `(tuple)` and `(tuple-tail)` in one constructor; `tail = none` is the plain tuple. -/
  | tuple    (elems : List Term) (tail : Option Term)
  | record   (val : Term)
  | held     (inner : Term) (f : Value → Value) (g : Value → Value)
  | refine   (inner : Term) (q : Value → Bool)
  | legacy   (inner : Term) (r : Attr → Option Value)
  | nullable (inner : Term)
  /-- §3 `(lazy)`. The thunk is *not* `Unit → Term`: a closure adds no constructible
      term (every `Term` is finite either way) and only defeats the termination
      checker. Recursive codecs are not modelled, and cannot be — see
      `Continuity.lean`: `union`'s admission is anti-monotone, so a genuinely
      recursive union has no fixpoint semantics in any system. -/
  | lazy     (inner : Term)
  | custom   (ce : Value → Option Attr) (cp : Attr → Option Value)
  /-- §3 `(opaque)`: `lossy = false` is the `refuse` policy. -/
  | opaq     (lossy : Bool)
  /-- §4's field table is a *set* of names each declaring one field, so that is what the
      term carries. A `List (Name × Field)` admitted two orderings of one object and a
      repeated name, and the typing rule carried a `Nodup` premise to make the first
      harmless and rule out the second; both are now properties of the type. `Field`
      sits in the function's codomain, which is strictly positive — the same factoring
      `Attr.m` and `Value.map` use one level down. -/
  | object   (fields : Finset Name) (f : {k // k ∈ fields} → Field) (rest : Rest)
  | union    (options : List Term)
  | dunion   (d : Name) (options : List Term)

inductive Field where
  | req      (t : Term)
  | optional (t : Term)
  | fallback (t : Term) (v : Value)

inductive Rest where
  | drop | refuse
  | codec (t : Term)

end

end Calculus
