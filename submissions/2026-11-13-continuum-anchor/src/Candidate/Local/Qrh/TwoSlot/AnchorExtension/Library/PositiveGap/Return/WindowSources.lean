/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Adapted by Joseph Bebel (2026-10-30, 2026-10-31) for the fixed five-window return. -/
/- Repeated marks: fork of Collet's final-stage module WindowSources (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): three branches; the count face C supplies the `C` windows and the
physical face P the capped `capP` windows (literal `Restricts`); unused corollaries removed. -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return (no other change). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.PositiveGap.Return.SourceInlet
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.PositiveGap.Return.Formulas
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.PositiveGap.Return
open QRH.Record1252270103Return
noncomputable section
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
  norm_num [sourceSupplier,countingSource,broadFace,countGlobal,physicalGlobal,globalFace,
   branchB,branchL,branchCap,countCB,countCL,countCap,physicalB,physicalLambda,physicalCap])
end
end QRH.PositiveGap.Return
