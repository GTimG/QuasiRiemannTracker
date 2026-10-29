/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.FrontierCanonicalFromNorm
import Candidate.Local.Qrh.JointDetector.NaturalUniformNear

namespace Qrh.JointDetector.FrontierActualNorm
noncomputable section

/-- The actual selected ordinary-source norm at the fixed positive gap 10^-9.
The natural cell theorem keeps its original arbitrary-gap quantifiers. -/
theorem actual_norm : FrontierNaturalCount.ActualSelectedSlotNorm :=
  FrontierCanonicalFromNorm.actual_norm NaturalSelectedNorm.natural_selected_cell_norm

end
end Qrh.JointDetector.FrontierActualNorm
#print axioms Qrh.JointDetector.FrontierActualNorm.actual_norm
