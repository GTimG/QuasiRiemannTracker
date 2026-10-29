/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed selected-amplitude gap 1/10^9; original slots, masks, ordinary sources
and early mesh order are retained. Inherited notices follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.FrontierSlotHistogram
import Candidate.Local.Qrh.JointDetector.FrontierActualSelectedNorm

namespace Qrh.JointDetector.FrontierCanonicalFromNorm
noncomputable section
set_option autoImplicit false

theorem actual_norm (h : NaturalSelectedCellNorm) : FrontierNaturalCount.ActualSelectedSlotNorm :=
  FrontierActualSelectedNorm.actualSelectedSlotNorm_of_aggregate
    (FrontierSlotHistogram.naturalAggregateSlotNorm_of_cell h)

end
end Qrh.JointDetector.FrontierCanonicalFromNorm

#print axioms Qrh.JointDetector.FrontierCanonicalFromNorm.actual_norm
