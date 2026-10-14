import Calculus.Dynamo.Lang.Scope
import Calculus.Lang.ScopeSound

/-!
# Soundness of a closed codec at DynamoDB

`Closed.Typed` and `Closed.Obligations` are the judgement and the obligations of a closed codec at
the DynamoDB tables. `Closed.sound` states `Alg.Scoped.Closed.sound` at the root of the codec.

The meaning of a closed codec is an entry of a solution, and the held set of a solution entry is
its write domain. So a lawful meaning is on its carrier, with no second walk of the derivation.
-/

namespace Calculus

/-- **The judgement of a closed codec** at DynamoDB: each entry is typed at the solution of the
    scope. -/
def Closed.Typed (α : Table) (t : Closed) : Prop :=
  Alg.Scoped.Closed.Typed (Alg.tables dynSyn.o α dynTableA) t.scope

/-- **The obligations of a closed codec** at DynamoDB: each entry meets them at each stage after a
    lawful stage. -/
def Closed.Obligations (α : Table) (t : Closed) : Prop :=
  Alg.Scoped.Closed.Obligations (Alg.tables dynSyn.o α dynTableA) t.scope

/-- **Soundness at DynamoDB**: a typed closed codec that meets its obligations is lawful. -/
theorem Closed.sound {α : Table} {t : Closed} (hty : t.Typed α) (hob : t.Obligations α) :
    Lawful (t.meaning α) :=
  Alg.Scoped.Closed.meaning_lawful _ t.scope hty hob t.root

/-- **A typed closed codec is on its carrier**: it writes and reads only values of its held set. -/
theorem Closed.carrier {α : Table} {t : Closed} (hty : t.Typed α) (hob : t.Obligations α) :
    Carrier (t.meaning α) := by
  have e := congrArg Alg.Codec.T (Alg.Scope.sol_eq (R := Alg.Scoped.TStep (Alg.tables dynSyn.o α dynTableA))
    (depth := Alg.Mean.d) t.scope t.root
    (c := ⟨fun v => ((t.meaning α).e v).isSome = true, none, (t.meaning α).f⟩) (fun _ => rfl) rfl rfl)
  refine ⟨fun {v a} he => ?_, fun {a v} hp => ?_⟩
  · exact (congrFun e v).mpr (Option.isSome_iff_exists.mpr ⟨a, he⟩)
  · exact (congrFun e v).mpr (Option.isSome_iff_exists.mpr ⟨a, (Closed.sound hty hob).canon hp⟩)

/-- **The rule `(alternate reader)`** over a typed closed codec keeps the three core laws. -/
theorem Closed.extendRead_lawfulCore {α : Table} {t : Closed} (hty : t.Typed α)
    (hob : t.Obligations α) (r : Attr → Option Value) : LawfulCore ((t.meaning α).extendRead r) :=
  Alg.LawfulCore.extendRead (Closed.sound hty hob).core

/-- **A closed codec of one entry**: one scope of one entry. -/
def Closed.one (t : Scoped.Term 0 1 0) : Closed :=
  ⟨1, fun i => match i with | ⟨0, _⟩ => t, 0⟩

/-- **The fixpoint law of a closed codec of one entry**: the meaning moves what its term moves over
    the meaning. -/
theorem Closed.one_fix (α : Table) (t : Scoped.Term 0 1 0) (o : Alg.Orient) (v : Value) :
    ((Closed.one t).meaning α).f o v =
      (Alg.SFlat.interp (Alg.CStep (Alg.Scoped.TStep (Alg.tables dynSyn.o α dynTableA)) 0 Fin.elim0)
        t (fun _ => (Closed.one t).meaning α) Fin.elim0).f o v := by
  have hfix := Alg.solve_fix Alg.Mean.d_pos (Alg.nf_contractive
    (Alg.CStep.lawful (Alg.Scoped.TStep_lawful (Alg.tables dynSyn.o α dynTableA)) 0 Fin.elim0)
    (fun i => match i with | ⟨0, _⟩ => t)) 0 o v
  refine hfix.trans ?_
  rw [Alg.sysB, Alg.interp_nf]
  congr 2
  · funext j
    rw [Fin.fin_one_eq_zero j]
    rfl
  · funext j
    exact j.elim0

end Calculus
