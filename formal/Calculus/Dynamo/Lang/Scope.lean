import Calculus.Dynamo.Lang.Term
import Calculus.Lang.Scope

/-!
# The scoped term at DynamoDB

A closed codec of DynamoDB is one scope over the term container at the DynamoDB signature, and a
root entry. Each builder keeps the spelling of the constructor of today's term. Above every guard
a term names an entry of the scope by `ref`. Each child of a container is an entry of the scope,
and each child of a wall is a closed graph term. The meaning of a closed codec is the solution of
the scope. The meaning reads the caller table at the side `false` and the store table at the side
`true`.
-/

namespace Calculus

namespace Scoped.Graph

/-- A flat term at DynamoDB over the term container, with a leaf for each of `N` entries. -/
abbrev Term (N : Nat) := Alg.Scoped.Graph dynSig N

/-- A slot of a flat term: its presence and its term. -/
abbrev ObjectSlot (N : Nat) := Alg.Scoped.SlotMode dynSig × Term N

section Builders
variable {N : Nat}

@[match_pattern] abbrev Term.prim (g : Ground) : Term N := .node (.prim g) Empty.elim
@[match_pattern] abbrev Term.base (kd : GroundKind) : Term N := .node (.prim (.base kd)) Empty.elim
@[match_pattern] abbrev Term.literal (kd : GroundKind) (v : kd.Carrier) : Term N :=
  .node (.prim (.literal kd v)) Empty.elim
@[match_pattern] abbrev Term.set (e : Term N) : Term N := .node .set fun _ => e
@[match_pattern] abbrev Term.refine (t : Term N) (p : Pred) (pA : dynSyn.PredA) : Term N :=
  .node (.refine p pA) fun _ => t
@[match_pattern] abbrev Term.legacy (t : Term N) (r : Attr → Option Value) : Term N :=
  .node (.legacy r) fun _ => t
@[match_pattern] abbrev Term.opaq : Term N := .node .opaq Empty.elim
@[match_pattern] abbrev Term.never : Term N := .node .never Empty.elim
@[match_pattern] abbrev Term.ref (i : Fin N) : Term N := .leaf i
@[match_pattern] abbrev Term.string : Term N := .base .string
@[match_pattern] abbrev Term.number : Term N := .base .number
@[match_pattern] abbrev Term.boolean : Term N := .base .boolean
@[match_pattern] abbrev Term.binary : Term N := .base .binary
@[match_pattern] abbrev Term.null : Term N := .base .null

/-- The rule `(held)`: the inner term and the outer term, below the wall. -/
def Term.held (s : Bool) (inner outer : Term N) (k₀ : dynSig.G s × Bool)
    (ks : List (dynSig.G s × Bool)) : Term N :=
  .node (.held s k₀ ks) fun
    | true => inner
    | false => outer

/-- The rule `(union)`, from a list of options. -/
def Term.union (os : List (Term N)) : Term N := .node (.union os.length) os.get

/-- The rule `(list)`, from a prefix, at most one spread, and a suffix. -/
def Term.list (pre : List (Term N)) (sp : Option (Term N)) (suf : List (Term N)) : Term N :=
  match sp with
  | none => .node (.list pre.length 0 suf.length) fun
    | .inl p => pre.get p
    | .inr (.inl p) => p.elim0
    | .inr (.inr p) => suf.get p
  | some t => .node (.list pre.length 1 suf.length) fun
    | .inl p => pre.get p
    | .inr (.inl _) => t
    | .inr (.inr p) => suf.get p

/-- The rule `(array)`. -/
def Term.array (e : Term N) : Term N := Term.list [] (some e) []

/-- The rules `(tuple)` and `(tuple-tail)`. -/
def Term.tuple (es : List (Term N)) (tail : Option (Term N)) : Term N := Term.list es tail []

@[match_pattern] abbrev ObjectSlot.req (t : Term N) : ObjectSlot N := (.req, t)
@[match_pattern] abbrev ObjectSlot.optional (t : Term N) : ObjectSlot N := (.opt, t)
@[match_pattern] abbrev ObjectSlot.fill (t : Term N) (v : Value) : ObjectSlot N := (.fill v, t)

/-- **An object payload** of a flat term. -/
structure Body (N : Nat) where
  mk ::
  fields : Finset Name
  slot : {x // x ∈ fields} → ObjectSlot N
  wild : Option (Term N)

/-- The rule `(object)`. -/
def Term.object (b : Body N) : Term N :=
  match b.wild with
  | none => .node (.obj b.fields (fun x => (b.slot x).1) 0) fun
    | .inl x => (b.slot x).2
    | .inr p => p.elim0
  | some t => .node (.obj b.fields (fun x => (b.slot x).1) 1) fun
    | .inl x => (b.slot x).2
    | .inr _ => t

end Builders

end Scoped.Graph

namespace Scoped

/-- A term of an entry of a scope at DynamoDB: each child of a container is one of the `w`
    entries, and above every guard the term names one of the `k` entries. -/
abbrev Term (w k : Nat) := Alg.Scoped.Term dynSig w k

/-- A slot at DynamoDB: its presence and its entry. -/
abbrev ObjectSlot (w : Nat) := Alg.Scoped.ObjectSlot dynSig w

section Builders
variable {w k : Nat}

@[match_pattern] abbrev Term.base (kd : GroundKind) : Term w k := Alg.Scoped.Term.prim (.base kd)
@[match_pattern] abbrev Term.literal (kd : GroundKind) (v : kd.Carrier) : Term w k :=
  Alg.Scoped.Term.prim (.literal kd v)
@[match_pattern] abbrev Term.set (e : Fin w) : Term w k := Alg.Scoped.Term.set e
@[match_pattern] abbrev Term.refine (t : Term w k) (p : Pred) (pA : dynSyn.PredA) : Term w k :=
  Alg.Scoped.Term.refine t p pA
@[match_pattern] abbrev Term.legacy (t : Graph.Term 0) (r : Attr → Option Value) : Term w k :=
  Alg.Scoped.Term.legacy t r
@[match_pattern] abbrev Term.opaq : Term w k := Alg.Scoped.Term.opaq
@[match_pattern] abbrev Term.never : Term w k := Alg.Scoped.Term.never
@[match_pattern] abbrev Term.ref (i : Fin k) : Term w k := Alg.Scoped.Term.ref i
@[match_pattern] abbrev Term.string : Term w k := .base .string
@[match_pattern] abbrev Term.number : Term w k := .base .number
@[match_pattern] abbrev Term.boolean : Term w k := .base .boolean
@[match_pattern] abbrev Term.binary : Term w k := .base .binary
@[match_pattern] abbrev Term.null : Term w k := .base .null

/-- The rule `(held)`: the inner term and the outer term, closed below the wall. -/
abbrev Term.held (s : Bool) (inner outer : Graph.Term 0) (k₀ : dynSig.G s × Bool)
    (ks : List (dynSig.G s × Bool)) : Term w k :=
  Alg.Scoped.Term.held s inner outer k₀ ks

/-- The rule `(union)`, from a list of options. -/
abbrev Term.union (os : List (Term w k)) : Term w k := Alg.Scoped.Term.union os

/-- The rule `(list)`, from a prefix, at most one spread, and a suffix, each an entry. -/
abbrev Term.list (pre : List (Fin w)) (sp : Option (Fin w)) (suf : List (Fin w)) : Term w k :=
  Alg.Scoped.Term.list pre sp suf

/-- The rule `(array)`. -/
abbrev Term.array (e : Fin w) : Term w k := Alg.Scoped.Term.array e

/-- The rules `(tuple)` and `(tuple-tail)`. -/
abbrev Term.tuple (es : List (Fin w)) (tail : Option (Fin w)) : Term w k :=
  Alg.Scoped.Term.tuple es tail

@[match_pattern] abbrev ObjectSlot.req (t : Fin w) : ObjectSlot w := (.req, t)
@[match_pattern] abbrev ObjectSlot.optional (t : Fin w) : ObjectSlot w := (.opt, t)
@[match_pattern] abbrev ObjectSlot.fill (t : Fin w) (v : Value) : ObjectSlot w :=
  (.fill v, t)

/-- **An object payload**: the declared names, the slot of each, and the open block. -/
structure Body (w : Nat) where
  mk ::
  fields : Finset Name
  slot : {x // x ∈ fields} → ObjectSlot w
  wild : Option (Fin w)

/-- The rule `(object)`. -/
abbrev Term.object (b : Body w) : Term w k := Alg.Scoped.Term.object b.fields b.slot b.wild

/-- The rule `(record)`: the object that declares no name and takes every key at one codec. It is
    not a constructor, because the open block is a block like any other. -/
abbrev Term.record (val : Fin w) : Term w k :=
  Term.object (.mk ∅ (fun x => absurd x.2 (Finset.notMem_empty x.1)) (some val))

end Builders

end Scoped

/-- **The flat graph of a codec**: one entry for each cycle point of the codec, in any order. -/
structure Graph where
  N : Nat
  sys : Fin N → Scoped.Graph.Term N

/-- **The guard of the graph**: no leaf under a wall, and no cycle of unguarded edges. -/
def Graph.guarded (g : Graph) : Bool := Alg.graphGuard (Alg.Scoped.TSig dynSig) g.sys

/-- **A closed codec of DynamoDB**: one scope over the term container, and a root entry. -/
structure Closed where
  N : Nat
  scope : Alg.Scoped.Closed dynSig N
  root : Fin N

/-- **The meaning of a closed codec** at the caller table `α`: the solution of its scope at the
    root. -/
def Closed.meaning (α : Table) (t : Closed) : Codec :=
  Alg.Scoped.Closed.meaning (Alg.tables dynSyn.o α dynTableA) t.scope t.root

/-- **The read row of a closed codec**: whether the meaning reads the attribute. The row reads
    the meaning, and no second description of it. -/
def Closed.AdmA (α : Table) (t : Closed) (a : Attr) : Bool := ((t.meaning α).p a).isSome

/-- **The read row is the domain of the read of the meaning.** -/
theorem Closed.AdmA_eq_isSome (α : Table) (t : Closed) (a : Attr) :
    t.AdmA α a = ((t.meaning α).p a).isSome := rfl

end Calculus
