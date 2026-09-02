import Calculus.Domain
open Calculus
-- resolves, and noncomputably — but so did the ungated carrier, which is the point
noncomputable example : DecidableEq WFDouble := inferInstance
noncomputable example : DecidableEq Double := inferInstance   -- unchanged, for comparison
noncomputable example (d : WFDouble) : NEFinset WFDouble := NEFinset.of d ∅
example : GroundKind.number.Carrier = WFDouble := rfl
example (d : WFDouble) : GroundKind.number.toValue d = Value.num d.1 := rfl
example : GroundKind.number.member = Member.N := rfl
