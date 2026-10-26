import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.NumeratorLocalCoefficients
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A finite Fourier extraction of coefficient mass from a uniform local bound.
Unlike a pointwise estimate at a single `w`, the four evaluations below determine
all coefficients of the local quadratic polynomial. -/
noncomputable section
namespace Cycle25.Weighted.Numerator

private theorem average_four_norm_le (a b c d : ℂ) (B : ℝ)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B) (hd : ‖d‖ ≤ B) :
    ‖(a + b + c + d) / 4‖ ≤ B := by
  rw [norm_div]
  rw [show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  have h := (norm_add_le (a + b + c) d).trans
    (add_le_add ((norm_add_le (a + b) c).trans
      (add_le_add (norm_add_le a b) le_rfl)) le_rfl)
  linarith

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
