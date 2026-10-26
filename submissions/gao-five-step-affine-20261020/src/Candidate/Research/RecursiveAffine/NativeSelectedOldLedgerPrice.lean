/- Actual fixed-stage prices license the native OLD radial rate. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode
import Candidate.Research.RecursiveAffine.RootLedger

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Cycle153ActualSourceGates
noncomputable section
open HeckeFamily Cycle153Reachable

/-- The actual four inner prices are at most the native OLD slot price.
No global deletion-to-OLD class or price equality is asserted. -/
theorem actualInnerPrice_le_native (j : Fin 4) :
    (innerStage j.val).price≤Cycle63.Optimization.slotPrice :=by
  fin_cases j <;>
    norm_num [innerStage,Cycle153.FixedStages.stage1,Cycle153.FixedStages.stage2,
      Cycle153.FixedStages.stage3,Cycle153.FixedStages.stage4,Cycle63.Optimization.slotPrice,Cycle63.Optimization.betaBound]

theorem actualRootPrice_le_native :
    letI : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
    Cycle63.AffineLedger.price≤Cycle63.Optimization.slotPrice :=by
  change Cycle153.FixedStages.stage0.price≤Cycle63.Optimization.slotPrice
  norm_num [Cycle153.FixedStages.stage0,Cycle63.Optimization.slotPrice,Cycle63.Optimization.betaBound]

variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}

theorem actualNodePrice_le_native (N : ReachableNode C j) :
    letI : Cycle63.AffineLedger:=N.ledger
    Cycle63.AffineLedger.price≤Cycle63.Optimization.slotPrice :=
  actualInnerPrice_le_native j

end
end OAI.SevenEighths.Cycle153ActualSourceGates
#print axioms OAI.SevenEighths.Cycle153ActualSourceGates.actualNodePrice_le_native
#print axioms OAI.SevenEighths.Cycle153ActualSourceGates.actualRootPrice_le_native
