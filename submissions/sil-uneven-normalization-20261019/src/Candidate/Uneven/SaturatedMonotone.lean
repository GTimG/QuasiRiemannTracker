/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.SaturatedScalar

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.Saturated
open PR63Adaptation

theorem affine_compensated_mono {den num c d S T : ℝ}
    (hden : 0 < den) (hslope : c ≤ d*den) (hST : S ≤ T) :
    (num-c*S)/den+d*S ≤ (num-c*T)/den+d*T := by
  have he : ((num-c*T)/den+d*T)-((num-c*S)/den+d*S)=
      (d*den-c)*(T-S)/den := by field_simp;ring
  apply sub_nonneg.mp
  rw [he]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hST)) hden.le

theorem full_exponent_mono {d S T : ℝ} (hd0 : 0 ≤ d) (hd : d < 5/6) (hST : S ≤ T) :
    fullCount d S+d*S ≤ fullCount d T+d*T := by
  have ha : 0 < a d := by unfold a;linarith
  have had : 0 ≤ a d*d := mul_nonneg ha.le hd0
  have h00 : c00 d S+d*S ≤ c00 d T+d*T := by
    unfold c00
    apply affine_compensated_mono (by positivity) _ hST
    nlinarith only [sq_nonneg d]
  have h10 : c10 d S+d*S ≤ c10 d T+d*T := by
    unfold c10
    apply affine_compensated_mono (by positivity) _ hST
    nlinarith only [had,sq_nonneg d]
  have h01 : c01 d S+d*S ≤ c01 d T+d*T := by
    unfold c01
    apply affine_compensated_mono (by positivity) _ hST
    nlinarith only [had,sq_nonneg d]
  have h11 : c11 d+d*S ≤ c11 d+d*T := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hST hd0)
  have he (X : ℝ) : fullCount d X+d*X=
      max (max (c00 d X+d*X) (c10 d X+d*X)) (max (c01 d X+d*X) (c11 d+d*X)) := by
    simp only [fullCount,max_add_add_right]
  rw [he S,he T]
  exact max_le_max (max_le_max h00 h10) (max_le_max h01 h11)

def rho (d : ℝ) : ℝ := 1-10*d/(3*(5-2*d))

theorem zero_width_lower {d : ℝ} (hd : d < 5/6) : rho d ≤ fullCount d 0 := by
  have hden : 5-2*d ≠ 0 := by linarith
  have he : c00 d 0=rho d := by
    have hden3 : 3*(5-2*d)≠0 := mul_ne_zero (by norm_num) hden
    have hc : c00 d 0=(15-16*d)/(3*(5-2*d)) := by
      unfold c00
      apply (div_eq_div_iff (by unfold a;linarith : 3*a d+2*d≠0) hden3).mpr
      unfold a
      ring
    rw [hc]
    unfold rho
    apply (div_eq_iff hden3).mpr
    have hh := div_mul_cancel₀ (10*d) hden3
    nlinarith only [hh]
  rw [←he]
  exact (le_max_left _ _).trans (le_max_left _ _)

end Sil.Uneven.Saturated
