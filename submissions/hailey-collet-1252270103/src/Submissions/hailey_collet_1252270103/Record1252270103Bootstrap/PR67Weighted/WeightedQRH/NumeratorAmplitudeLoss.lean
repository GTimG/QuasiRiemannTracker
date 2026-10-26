import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.NumeratorPacketBinBound
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-! Upper amplitude-bin slack is restored after the packet estimate, without
changing the diluted lower-bin mean used by either the count or the capacity. -/
noncomputable section
open scoped BigOperators
namespace WeightedQRH.Numerator

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

end WeightedQRH.Numerator

end
end Record1252270103Bootstrap.PR67
