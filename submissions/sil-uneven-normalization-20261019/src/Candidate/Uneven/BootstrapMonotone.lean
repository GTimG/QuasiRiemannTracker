/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.BootstrapCore

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Sil.Uneven.Bootstrap

theorem slope_le_density {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) (i : Fin 7) :
    slope d i ≤ d := by
  have hd : 0 ≤ d := by linarith
  fin_cases i
  · norm_num [slope]
    apply (div_le_iff₀ (by linarith : 0 < 5+ -(2*d))).mpr
    nlinarith [sq_nonneg d]
  · norm_num [slope]
    apply (div_le_iff₀ (by linarith : 0 < 52867295+ -(25146918*d))).mpr
    nlinarith [sq_nonneg d]
  · norm_num [slope]
    apply (div_le_iff₀ (by linarith : 0 < 15+ -(6*d))).mpr
    nlinarith [sq_nonneg d]
  · norm_num [slope]
    apply (div_le_iff₀ (by linarith : 0 < 25+ -(18*d))).mpr
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hd1)]
  all_goals norm_num [slope]; exact hd

/-- Adding slot widths cannot lower the full weighted-count exponent. -/
theorem full_exponent_mono {d S T : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50)
    (hST : S ≤ T) : count d S+d*S ≤ count d T+d*T := by
  obtain ⟨i,hi⟩ := FiniteGain.gain_attained (slope d) (offset d) S 1
  have ht := FiniteGain.gain_le (slope d) (offset d) T 1 i
  have hs := mul_nonneg (sub_nonneg.mpr (slope_le_density hd0 hd1 i)) (sub_nonneg.mpr hST)
  unfold count physicalGain
  nlinarith only [hi,ht,hs]

theorem zero_width_count {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    count d 0=Saturated.rho d := by
  have hnonneg := FiniteGain.gain_nonneg (coefficient_nonneg hd0 hd1).1
    (coefficient_nonneg hd0 hd1).2 (show (0:ℝ) ≤ 0 by norm_num) (show (0:ℝ) ≤ 1 by norm_num)
  have hle := FiniteGain.gain_le (slope d) (offset d) 0 1 0
  have hz : offset d 0=0 := by norm_num [offset]
  rw [mul_zero,zero_add,mul_one,hz] at hle
  unfold count physicalGain
  linarith

end Sil.Uneven.Bootstrap
