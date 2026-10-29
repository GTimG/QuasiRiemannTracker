/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.NaturalUniformNear
import Candidate.Local.Qrh.JointDetector.CanonicalFromNorm
namespace Qrh.JointDetector.RestartSourceChains
noncomputable section
open OAI.SevenEighths

/-- The already proved local ceiling used by the first LOW restart. -/
theorem previous_beta_le : HeckeZeroSupremum.beta ≤ (87393871/100000000:ℝ) := by
 have hn := CanonicalFromNorm.actual_norm NaturalSelectedNorm.natural_selected_cell_norm
 simpa only [PointwiseReturn.theta] using PointwiseReturn.beta_le_theta hn

#print axioms previous_beta_le
end
end Qrh.JointDetector.RestartSourceChains
