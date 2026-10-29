/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/pointwise_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
The actual selected all-source norm remains an explicit analytic premise. -/
/- Repeated marks: fork of Collet's final-stage module WindowSources (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): three branches; the count face C supplies the `C` windows and the
physical face P the capped `capP` windows (literal `Restricts`); unused corollaries removed. -/
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.SourceInlet
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Formulas
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace Qrh.JointDetector.PointwiseReturn
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence

def countingSource (b:CountBranch) : SourceFace :=
 broadFace (branchB b) (branchL b) (branchCap b)
def sourceSupplier (b:CountBranch) : SourceFace :=
 match b with
 | .capP | .Cphys => physicalGlobal
 | _ => countGlobal

theorem supplier_restricts_counting (b:CountBranch) (hb:b≠.old) :
 (sourceSupplier b).Restricts (countingSource b) := by
 cases b <;> first | exact (hb rfl).elim | (constructor <;>
  norm_num [sourceSupplier,countingSource,broadFace,countGlobal,physicalGlobal,globalFace,
   branchB,branchL,branchCap,countCB,countCL,countCap,physicalB,physicalLambda,physicalCap])
end
end Qrh.JointDetector.PointwiseReturn
