/- Copyright (c) 2026 Sil. Apache-2.0.
Exact target and terminal parameter compatibility. This module supplies only
arithmetic interfaces; it makes no analytic source or final-bound assertion.
-/
import Candidate.FourthPower.Parameters

set_option autoImplicit false

namespace Candidate.FourthPower.TargetCompatibility
noncomputable section

/-- This is exactly the requested decimal, without upward rounding. -/
theorem target_exact : theta = (8746935 / 10000000 : ℝ) := by
  norm_num [theta]

theorem target_positive : 0 < theta := by norm_num [theta]

theorem target_half : (1 / 2 : ℝ) ≤ theta := by norm_num [theta]

theorem target_seven_eighths : theta ≤ (7 / 8 : ℝ) := by norm_num [theta]

theorem target_strictly_improves_874699 : theta < (874699 / 1000000 : ℝ) := by
  norm_num [theta]

/-- Native source cost and the new feedback cost are deliberately different. -/
theorem native_feedback_gap : (3 / 4 : ℝ) - kappa = 613 / 1000000 := by
  norm_num [kappa, theta]

theorem target_below_incumbent : theta < incumbent := feedback_domain.2.2.2.1

/-- The common-probe shift is tied to the NEW geometry, not an old endpoint. -/
def probeShift : ℝ := -(4 + y - x) / 6

theorem probeShift_exact : probeShift = (-2044621 / 3000000 : ℝ) := by
  norm_num [probeShift, x, y, ell, theta, h]

theorem boundary_signal_identity :
    theta + probeShift = x / 2 + (y - x) / 12 := by
  simpa only [probeShift, sub_eq_add_neg, neg_div] using geometry_identities.2

theorem boundary_signal_exact :
    theta + probeShift = (1158919 / 6000000 : ℝ) := by
  rw [probeShift_exact]
  norm_num [theta]

/-- All terminal continuation gates are unconditional arithmetic facts. -/
theorem continuation_gates :
    0 < theta ∧ (1 / 2 : ℝ) ≤ theta ∧ theta ≤ (7 / 8 : ℝ) :=
  ⟨target_positive, target_half, target_seven_eighths⟩

end
end Candidate.FourthPower.TargetCompatibility
