import Candidate.Local.Qrh.PositiveGap.Return.SourceInlet
import Candidate.Local.Qrh.PositiveGap.Return.Formulas
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.PositiveGap.Return
open QRH.Record1252270103Return
noncomputable section
variable [TargetC]
open QRH.Record12518109Source QRH.Record12518109Existence
def countingSource (b:CountBranch) : SourceFace :=
 broadFace (branchB b) (branchL b) (branchCap b)
def sourceSupplier (b:CountBranch) : SourceFace :=
 match b with
 | .capP => physicalGlobal
 | _ => countGlobal
theorem supplier_restricts_counting (b:CountBranch) (hb:b≠.old) :
 (sourceSupplier b).Restricts (countingSource b) := by
 cases b <;> first | exact (hb rfl).elim | (constructor <;>
  (dsimp [sourceSupplier,countingSource,broadFace,countGlobal,physicalGlobal,globalFace,
   branchB,branchL,branchCap,countCB,countCL,countCap,physicalB,physicalLambda,physicalCap];
   linarith [eps_pos, eps_le]))
end
end QRH.PositiveGap.Return
