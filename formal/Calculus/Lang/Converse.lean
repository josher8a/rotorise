import Calculus.Lang.Term

/-!
# The denotation of the dual

The dual universe `S.op` keeps the signature and flips the orientation. So the dual reads the
stored carrier as its caller carrier, the stored half of each two-sided row as its caller half,
and the stored table as its caller table. The denotation reads the tables at the absolute sides,
and the dual gives the same table at each absolute side. So the dual denotes each term by the
same codec, and an analysis at the dual reads that codec at the dual orientation.
-/

namespace Calculus.Alg

variable {S : Syn} [Sem S] {α : Table S} {β : Table S.op}

/-- **The dual universe denotes each term by the same codec**: it reads the stored table as its
    caller table and the caller table as its stored table, and the tables of each absolute side
    are the same. -/
theorem denote_op (t : Term S) (ρ : List S.C) : denote (S := S.op) β α t ρ = denote α β t ρ :=
  congrArg (denoteAbs · t ρ) (tables_op S.o α β)

end Calculus.Alg
