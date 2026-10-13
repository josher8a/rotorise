import Calculus.JSON.Basic
import Calculus.Lang.ScopeSound

/-!
# The string-or-number codec, as a closed codec

The union of the string codec and the number codec is a closed codec of one entry
(`strOrNumClosed`). The generic soundness of a closed codec (`Alg.Scoped.Closed.meaning_lawful`)
makes its meaning lawful. The two options are compatible because each kind is below the identity
codec, so two kinds send a value to the same value.

The meaning of the entry is the union of the two ground codecs, at the fixed point of the scope.
So the meaning acts at each orientation exactly where the primitive row of a string or of a number
accepts the datum.
-/

namespace Calculus.JSON

/-- The term of the one entry: a string or a number. The term names no entry. -/
def strOrNumBody {k : Nat} : Alg.Scoped.Term jsonSig 0 1 k :=
  Alg.Scoped.Term.union [.prim .str, .prim .num]

/-- A string or a number, as a closed codec of one entry. -/
def strOrNumClosed : Alg.Scoped.Closed jsonSig 1 :=
  .snoc (c := 0) (n := 1) .nil fun _ => strOrNumBody

/-- A string or a number: the meaning of the closed codec at the JSON tables. -/
def strOrNumC : Alg.Codec Json JMember :=
  Alg.Scoped.Closed.meaning (Alg.tables jsonSyn.o jsonTable jsonTableA) strOrNumClosed 0

/-- Two kinds agree at each orientation: each ground codec sends a value to the value. -/
theorem compat_ground (m m' : JMember) : Alg.Compat (ground m) (ground m') :=
  have agree : ∀ o, Alg.Agree o (ground m) (ground m') := fun o x _ _ hy hz =>
    Option.some.inj ((Alg.sub_fiberCodec Json.member m o x _ hy).symm.trans
      (Alg.sub_fiberCodec Json.member m' o x _ hz))
  (Alg.compat_iff_agree (lawful_ground m) (lawful_ground m')).mpr ⟨agree .host, agree .dual⟩

/-- The entry of `strOrNumClosed` is typed at every environment. -/
theorem typed_strOrNumBody (τ : (s : Bool) → Alg.TableAt jsonSig s)
    (κ : Fin 0 → Alg.Codec Json JMember) (ρw : Fin 1 → Alg.Codec Json JMember)
    (ρk : Fin 0 → Alg.Codec Json JMember) :
    ∃ T μ, Alg.Scoped.Typed τ κ ρw ρk (strOrNumBody (k := 0)) T μ := by
  have hp : ∀ m : JMember, ∃ T μ,
      Alg.Scoped.Typed τ κ ρw ρk (Alg.Scoped.Term.prim (B := jsonSig) m) T μ := fun m =>
    ⟨_, _, Alg.Scoped.Typed.node (B := jsonSig) (o := .prim m) (T := Empty.elim)
      (μ := Empty.elim) (fun p => p.elim) rfl⟩
  obtain ⟨T1, μ1, h1⟩ := hp .str
  obtain ⟨T2, μ2, h2⟩ := hp .num
  exact ⟨_, _, Alg.Scoped.Typed.node (B := jsonSig) (o := .union 2) (T := [T1, T2].get)
    (μ := [μ1, μ2].get) (fun p => match p with
      | ⟨0, _⟩ => h1
      | ⟨1, _⟩ => h2) rfl⟩

/-- `strOrNumClosed` is typed at all tables. -/
theorem typed_strOrNumClosed (τ : (s : Bool) → Alg.TableAt jsonSig s) :
    Alg.Scoped.Closed.Typed τ strOrNumClosed :=
  ⟨trivial, fun i => match i with | ⟨0, _⟩ => typed_strOrNumBody _ _ _ _⟩

/-- `strOrNumClosed` meets its obligations at all tables: its two options are compatible. -/
theorem obligations_strOrNumClosed (τ : (s : Bool) → Alg.TableAt jsonSig s) :
    Alg.Scoped.Closed.Obligations τ strOrNumClosed := by
  refine ⟨trivial, fun _ _ i => match i with | ⟨0, _⟩ => ⟨fun p => ?_, fun p q => ?_⟩⟩
  · match p with
    | ⟨0, _⟩ => exact ⟨fun q => q.elim, trivial⟩
    | ⟨1, _⟩ => exact ⟨fun q => q.elim, trivial⟩
  match p, q with
  | ⟨0, _⟩, ⟨0, _⟩ => exact compat_ground _ _
  | ⟨0, _⟩, ⟨1, _⟩ => exact compat_ground _ _
  | ⟨1, _⟩, ⟨0, _⟩ => exact compat_ground _ _
  | ⟨1, _⟩, ⟨1, _⟩ => exact compat_ground _ _

/-- **The closed union of the string codec and the number codec is lawful.** -/
theorem lawful_strOrNumC : Alg.Lawful Json.member strOrNumC :=
  Alg.Scoped.Closed.meaning_lawful _ strOrNumClosed (typed_strOrNumClosed _)
    (obligations_strOrNumClosed _) 0

/-- **The closed string-or-number codec acts exactly where a string or a number row accepts.** -/
theorem exact_strOrNumC (τ : (s : Bool) → Alg.TableAt jsonSig s) (o : Alg.Orient) (v : Json) :
    ((Alg.Scoped.Closed.meaning τ strOrNumClosed 0).f o v).isSome =
      (Alg.PrimAdm.admV (S := jsonSyn) .str v || Alg.PrimAdm.admV (S := jsonSyn) .num v) := by
  have h := congrFun (congrFun
    (Alg.Scoped.mng_leaf (Alg.Scoped.Closed.toG (S := jsonSyn) τ strOrNumClosed) 0) o) v
  change (Alg.Scoped.Closed.meaning τ strOrNumClosed 0).f o v = _ at h
  rw [h]
  cases v <;> rfl

end Calculus.JSON
