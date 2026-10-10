import Cycle25.Numerator.PacketBinBound

/-! Upper amplitude-bin slack is restored after the packet estimate, without
changing the diluted lower-bin mean used by either the count or the capacity. -/
noncomputable section
open scoped BigOperators
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator

theorem upper_bin_normalized (P : ℂ) (U a loss : ℝ) (hU : 0 < U)
    (hP : ‖P‖ ≤ U^(a+loss)) :
    ‖P / ((U^loss : ℝ) : ℂ)‖ ≤ U^a := by
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hU.le _)]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hU _)).mpr
  simpa only [Real.rpow_add hU] using hP

theorem restore_upper_bin_loss {ι : Type*} (s : Finset ι) (S P : ι→ℂ)
    (U loss E C : ℝ) (hU : 0 < U)
    (hb : (∑ i ∈ s, ‖S i * (P i / ((U^loss : ℝ) : ℂ))‖) ≤ C*U^E) :
    (∑ i ∈ s, ‖S i*P i‖) ≤ C*U^(E+loss) := by
  have he : (∑ i ∈ s, ‖S i * (P i / ((U^loss : ℝ) : ℂ))‖) =
      (∑ i ∈ s, ‖S i*P i‖) / U^loss := by
    simp_rw [←mul_div_assoc,norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hU.le _)]
    exact (Finset.sum_div _ _ _).symm
  rw [he] at hb
  have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hU loss)).mp hb
  simpa only [mul_assoc,←Real.rpow_add hU] using hh

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/
