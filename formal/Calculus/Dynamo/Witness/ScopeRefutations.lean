import Calculus.Dynamo.Lang.ScopeSound

/-!
# The "Do not hold" table of `≡`, over closed codecs

The rows of `≡` that fail, refuted at small closed codecs. The meaning of a closed codec
holds exactly its write domain, so each refutation is a held-set separation: one side writes a
value that the other side does not write.

The member of the meaning of a closed codec is `⊤`. So the set obligation reads the member of the
term of the entry, at every table and environment: that term is the element that `set`
lifts.
-/

namespace Calculus

variable {α : Table}

/-! ## `union(c₁ … cₙ) ≢ union(c₁ … cₙ, c)` -/

/-- The extension writes a boolean, and the union of one string does not. -/
theorem Closed.not_equiv_union_extend :
    ¬ Codec.Equiv ((Closed.one (Scoped.Term.union [.string])).meaning α)
      ((Closed.one (Scoped.Term.union [.string, .boolean])).meaning α) :=
  fun h => Bool.false_ne_true ((h.heldSet (.bool true)).mpr rfl)

/-! ## `union(array(c₁), array(c₂)) ≢ array(union(c₁, c₂))` -/

/-- `["A", "B"]` is an array of either literal, but homogeneous in neither. -/
theorem Closed.not_equiv_union_array :
    ¬ Codec.Equiv
        ((⟨3, fun i => match i with
          | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.array 1, Scoped.Term.array 2] : Scoped.Term 3 0)
          | ⟨1, _⟩ => (Scoped.Term.literal .string "A" : Scoped.Term 3 1)
          | ⟨2, _⟩ => (Scoped.Term.literal .string "B" : Scoped.Term 3 2), 0⟩ : Closed).meaning α)
        ((Closed.two (.array 1) (.union [.literal .string "A", .literal .string "B"])).meaning α) :=
  fun h => Bool.false_ne_true ((h.heldSet (.arr [.str "A", .str "B"])).mpr rfl)

/-! ## `tuple(c₁ … cₙ, rest(c))` is neither a tuple nor an array of unions -/

/-- Against the plain tuple: a second element the tail accepts and the tuple has no position for. -/
theorem Closed.not_equiv_tupleTail_tuple :
    ¬ Codec.Equiv ((Closed.two (.tuple [1] (some 1)) .string).meaning α)
      ((Closed.two (.tuple [1] none) .string).meaning α) :=
  fun h => Bool.false_ne_true ((h.heldSet (.arr [.str "a", .str "b"])).mp rfl)

/-- Against the array: the empty sequence, which an array holds and a fixed head cannot. -/
theorem Closed.not_equiv_tupleTail_array :
    ¬ Codec.Equiv ((Closed.two (.tuple [1] (some 1)) .string).meaning α)
      ((Closed.two (.array 1) (.union [.string])).meaning α) :=
  fun h => Bool.false_ne_true ((h.heldSet (.arr [])).mpr rfl)

/-! ## `refine(held(c, P, k), q) ≢ held(refine(c, q), P, k)` -/

/-- A constant-on-strings iso half, and a predicate that tells `"A"` from `"B"`. -/
def isoF : Value → Value
  | .str _ => .str "A"
  | v => v

def predA : Value → Bool
  | .str s => s == "A"
  | _ => false

/-- The table that gives each generator the pair `isoF`, `id`. -/
def isoTable : Table := fun _ => (isoF, id)

/-- At `"B"`: the outer refinement refuses `"B"`, and the inner refinement reads `"A"`. -/
theorem Closed.not_equiv_refine_held :
    ¬ Codec.Equiv
        ((Closed.one (Scoped.Term.refine
          (Scoped.Term.held false .string .string (.caller 0, false) [])
            (.closure predA) ())).meaning isoTable)
        ((Closed.one (Scoped.Term.held false (Scoped.Graph.Term.refine .string (.closure predA) ())
          .string (.caller 0, false) [])).meaning isoTable) :=
  fun h => Bool.false_ne_true ((h.heldSet (.str "B")).mpr rfl)

/-! ## `set(union(c₁, c₂))`: typed, and refused by the store -/

section Set
variable {w k : Nat} (τ : (s : Bool) → Alg.TableAt dynSig s)

/-- **A heterogeneous union fails the DynamoDB set obligation**, over a scope term. -/
theorem Scoped.setElem_union_refused (ρw : Fin w → Codec) (ρk : Fin k → Codec) :
    ¬ SetElem (Alg.SFlat.interp (Alg.Scoped.TStep τ)
      (Scoped.Term.union [.string, .boolean] : Scoped.Term w k) ρw ρk) :=
  Bool.false_ne_true

/-- The union on its own is typed at a scope, at the member `none`. -/
theorem Scoped.typed_union_string_boolean (ρw : Fin w → Codec) (ρk : Fin k → Codec) :
    Alg.Scoped.Typed τ ρw ρk (Scoped.Term.union [.string, .boolean] : Scoped.Term w k)
      (Alg.HUnion [fun v : Value => v.member = Member.S, fun v : Value => v.member = Member.BOOL])
      none :=
  Alg.Scoped.Typed.node (B := dynSig) (o := .union 2)
    (T := [fun v : Value => v.member = Member.S, fun v : Value => v.member = Member.BOOL].get)
    (μ := [some Member.S, some Member.BOOL].get)
    (r := (Alg.HUnion [fun v : Value => v.member = Member.S,
      fun v : Value => v.member = Member.BOOL], none))
    (fun p => match p with
      | ⟨0, _⟩ => Alg.Scoped.Typed.node (B := dynSig) (o := .prim (Ground.base .string))
          (T := Empty.elim) (μ := Empty.elim) (fun p => p.elim) rfl
      | ⟨1, _⟩ => Alg.Scoped.Typed.node (B := dynSig) (o := .prim (Ground.base .boolean))
          (T := Empty.elim) (μ := Empty.elim) (fun p => p.elim) rfl) rfl

/-- **An empty option is the unit of the sum**, over a scope term. -/
example (ρw : Fin w → Codec) (ρk : Fin k → Codec) :
    ∃ T μ,
      Alg.Scoped.Typed τ ρw ρk (Scoped.Term.union [.string, .never] : Scoped.Term w k) T μ :=
  ⟨_, _, Alg.Scoped.Typed.node (B := dynSig) (o := .union 2)
    (T := [fun v : Value => v.member = Member.S, Alg.HNever].get) (μ := [some Member.S, none].get)
    (fun p => match p with
      | ⟨0, _⟩ => Alg.Scoped.Typed.node (B := dynSig) (o := .prim (Ground.base .string))
          (T := Empty.elim) (μ := Empty.elim) (fun p => p.elim) rfl
      | ⟨1, _⟩ => Alg.Scoped.Typed.node (B := dynSig) (o := .never)
          (T := Empty.elim) (μ := Empty.elim) (fun p => p.elim) rfl) rfl⟩

end Set

end Calculus
