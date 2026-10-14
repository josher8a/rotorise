import Calculus.Dynamo.Lang.ScopeSound
import Calculus.Dynamo.Lang.Store

/-!
# The nesting bound, over a closed codec

`Attr.Storable n a` bounds the nesting of an attribute, and the calculus states no such bound. A
typed closed codec can write an attribute that the store refuses: `Closed.not_storable_of_typed`
is the witness, `n` nested arrays over a string. The witness carries no premise about depth,
because no rule of the judgement states one. The port gates each write at the bound
(`storeCodec`), and the gate refuses the witness.
-/

namespace Calculus

variable {α : Table}

/-! ## The witness family -/

/-- A value on its held set: `n` nested one-element arrays over a string. -/
def deepV : Nat → Value
  | 0 => .str ""
  | n + 1 => .arr [deepV n]

/-- What the pair writes: `n` nested `L`s over an `S`. -/
def deepA : Nat → Attr
  | 0 => .s ""
  | n + 1 => .l [deepA n]

/-- The nesting is the index, on the nose — `S` is not a document type and each `L` is one. -/
theorem nesting_deepA : ∀ n, Attr.nesting (deepA n) = n
  | 0 => rfl
  | n + 1 => by
    show Attr.nestingL [deepA n] + 1 = n + 1
    show max (Attr.nesting (deepA n)) 0 + 1 = n + 1
    rw [nesting_deepA n]; simp

/-- The witness holds no numeral, so the numeral half of the store gate admits it at every
    index. -/
theorem numeralsStored_deepA : ∀ n, Attr.numeralsStored (deepA n) = true
  | 0 => rfl
  | n + 1 => (Bool.and_true _).trans (numeralsStored_deepA n)

/-- The other side of the boundary: the witness one level shallower is storable. -/
theorem storable_deepA (bound : Nat) : Attr.Storable bound (deepA bound) := by
  show Attr.nesting (deepA bound) ≤ bound
  rw [nesting_deepA]

/-! ## The witness as a closed codec -/

/-- `n` nested arrays over a string, as the term of an entry. -/
def deepS : Nat → {w k : Nat} → Scoped.Term 0 w k
  | 0 => Scoped.Term.string
  | n + 1 => Scoped.Term.array (deepS n)

/-- `n` nested arrays over a string, as a closed codec of one entry. -/
def deepClosed (n : Nat) : Closed := Closed.one (deepS n)

/-- Each term of the family is typed at every environment. -/
theorem typed_deepS (τ : (s : Bool) → Alg.TableAt dynSig s) (κ : Fin 0 → Codec) :
    ∀ (n : Nat) {w k : Nat} (ρw : Fin w → Codec) (ρk : Fin k → Codec),
      ∃ T μ, Alg.Scoped.Typed τ κ ρw ρk (deepS n) T μ
  | 0, _, _, _, _ =>
    ⟨_, _, Alg.Scoped.Typed.node (B := dynSig) (o := .prim (Ground.base .string)) (T := Empty.elim)
      (μ := Empty.elim) (fun p => p.elim) rfl⟩
  | n + 1, w, _, ρw, _ => by
    obtain ⟨T, μ, h⟩ := typed_deepS τ κ n ρw ρw
    exact ⟨_, _, Alg.Scoped.Typed.node (B := dynSig) (o := .list 0 1 0) (T := fun _ => T)
      (μ := fun _ => μ) (fun p => match p with
        | .inl p => p.elim0
        | .inr (.inl _) => h
        | .inr (.inr p) => p.elim0) rfl⟩

/-- Each closed codec of the family is typed. -/
theorem Closed.typed_deep (n : Nat) : (deepClosed n).Typed α :=
  fun i => match i with | ⟨0, _⟩ => typed_deepS _ _ n _ _

/-- Each term of the family writes what the index says, at every environment: it names no entry. -/
theorem deepS_e (τ : (s : Bool) → Alg.TableAt dynSig s) (κ : Fin 0 → Codec) :
    ∀ (n : Nat) {w k : Nat} (ρw : Fin w → Codec) (ρk : Fin k → Codec),
      (Alg.SFlat.interp (Alg.CStep (Alg.Scoped.TStep τ) 0 κ) (deepS n) ρw ρk).e (deepV n) =
        some (deepA n)
  | 0, _, _, _, _ => rfl
  | n + 1, _, _, ρw, _ => by
    show (arrayCodec (Alg.SFlat.interp (Alg.CStep (Alg.Scoped.TStep τ) 0 κ) (deepS n) ρw ρw)).e
      (.arr [deepV n]) = some (.l [deepA n])
    refine (arrayCodec_f _ _ [deepV n]).trans ?_
    have h := deepS_e τ κ n ρw ρw
    simp only [traverse, orient_rows] at h ⊢; rw [h]; rfl

/-- Each closed codec of the family writes what the index says. -/
theorem Closed.deep_e (n : Nat) : ((deepClosed n).meaning α).e (deepV n) = some (deepA n) :=
  (Closed.one_fix α (deepS n) .host (deepV n)).trans (deepS_e _ _ n _ _)

/-- **The claim the calculus cannot make, over a closed codec.** At every bound, a typed closed
    codec, a value it writes, and an attribute the store refuses. -/
theorem Closed.not_storable_of_typed (bound : Nat) :
    ∃ (t : Closed) (v : Value) (a : Attr),
      t.Typed α ∧ (t.meaning α).e v = some a ∧ ¬ Attr.Storable bound a :=
  ⟨deepClosed (bound + 1), deepV (bound + 1), deepA (bound + 1), Closed.typed_deep (bound + 1),
    Closed.deep_e (bound + 1), fun h => Nat.not_succ_le_self bound
      ((congrArg (· ≤ bound) (nesting_deepA (bound + 1))).mp h)⟩

end Calculus

namespace Calculus.DynamoDB

variable {α : Table}

/-- At the store's bound, a typed closed codec writes an attribute that DynamoDB refuses. -/
theorem Closed.not_storable_of_typed :
    ∃ (t : Closed) (v : Value) (a : Attr),
      t.Typed α ∧ (t.meaning α).e v = some a ∧ ¬ Attr.Storable maxNesting a :=
  Calculus.Closed.not_storable_of_typed maxNesting

/-- The port gates every typed closed codec: `storeCodec` keeps the laws of `Closed.sound`. -/
theorem Closed.lawful_storeCodec {t : Calculus.Closed} (hty : t.Typed α) (hob : t.Obligations α) :
    Lawful (storeCodec (t.meaning α)) :=
  Calculus.lawful_storeCodec (Calculus.Closed.sound hty hob)

/-- …and keeps the carrier of every typed closed codec. -/
theorem Closed.carrier_storeCodec {t : Calculus.Closed} (hty : t.Typed α) (hob : t.Obligations α) :
    Carrier (storeCodec (t.meaning α)) :=
  Calculus.carrier_storeCodec (Calculus.Closed.carrier hty hob)

/-- **The port refuses the witness**: the write at `maxNesting + 1` levels is refused. -/
theorem Closed.storeCodec_refuses_deep :
    (storeCodec ((deepClosed (maxNesting + 1)).meaning α)).e (deepV (maxNesting + 1)) = none := by
  rw [storeCodec, Alg.refine2_e_def]
  simp only [if_true]
  rw [Calculus.Closed.deep_e]
  simp [isStorable, nesting_deepA]

/-- …and writes the witness at `maxNesting` levels unchanged. -/
theorem Closed.storeCodec_writes_deep :
    (storeCodec ((deepClosed maxNesting).meaning α)).e (deepV maxNesting) = some (deepA maxNesting) := by
  rw [storeCodec, Alg.refine2_e_def]
  simp only [if_true]
  rw [Calculus.Closed.deep_e]
  simp [isStorable, nesting_deepA, numeralsStored_deepA]

end Calculus.DynamoDB
