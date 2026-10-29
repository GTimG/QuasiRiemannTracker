/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.FineSlotHistogram
import Candidate.Local.Qrh.JointDetector.FineActualSelectedNorm

namespace Qrh.JointDetector.FineCanonicalFromNorm
noncomputable section
set_option autoImplicit false

theorem actual_norm (h : NaturalSelectedCellNorm) : FineNaturalCount.ActualSelectedSlotNorm :=
  FineActualSelectedNorm.actualSelectedSlotNorm_of_aggregate
    (FineSlotHistogram.naturalAggregateSlotNorm_of_cell h)

end
end Qrh.JointDetector.FineCanonicalFromNorm

#print axioms Qrh.JointDetector.FineCanonicalFromNorm.actual_norm
