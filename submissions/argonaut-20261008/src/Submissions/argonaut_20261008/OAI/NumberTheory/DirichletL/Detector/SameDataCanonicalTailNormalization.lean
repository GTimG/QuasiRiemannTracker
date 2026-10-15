import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.SameDataCanonicalBudgets

namespace OAI
noncomputable section
namespace SevenEighths.PerturbedCanonicalLocalPrep
open SevenEighths.Parameters SevenEighths.PerturbedCentral

/-- Both actual tail powers pay the same t/8 inverse-normalizer loss. -/
theorem same_D_canonical_error_power
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    {beta Z : ℝ} (hbeta : boundary < beta) (hZ : 1 ≤ Z) :
    (Z ^ (beta - 11 / 16 - 63 / 800 + 8 * D.e + 51 * rho0 / 100) +
      Z ^ (-D.t)) * Z ^ (D.t / 8) ≤
      2 * Z ^ (beta - 11 / 16 - D.sigma) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hs : Z ^ (beta - 11 / 16 - 63 / 800 + 8 * D.e + 51 * rho0 / 100) *
      Z ^ (D.t / 8) ≤ Z ^ (beta - 11 / 16 - D.sigma) := by
    calc
      _ ≤ Z ^ (beta - 11 / 16 - D.sigma - D.t / 8) * Z ^ (D.t / 8) :=
        mul_le_mul_of_nonneg_right (same_D_small_power D beta Z hZ)
          (Real.rpow_nonneg hZ0.le _)
      _ = _ := by
        rw [← Real.rpow_add hZ0]
        congr 1
        ring
  have hl : Z ^ (-D.t) * Z ^ (D.t / 8) ≤
      Z ^ (beta - 11 / 16 - D.sigma) := by
    rw [← Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (same_D_tail_saving_exponent D hbeta)
  rw [add_mul]
  linarith

end SevenEighths.PerturbedCanonicalLocalPrep
end
end OAI
