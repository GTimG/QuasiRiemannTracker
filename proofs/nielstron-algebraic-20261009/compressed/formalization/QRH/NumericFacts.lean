import QRH.Geometry

/-! Rational bounds on the exact algebraic geometry. -/

namespace QRH.NumericFacts

theorem shape_bounds {e : ℝ} (he : (1/6:ℝ) ≤ e) (he' : e ≤ 167/1000) :
    (123/1000:ℝ) ≤ -(3*e+1)*(36*e^2-75*e+19)/(3*(114*e^2-159*e-7)) ∧
    -(3*e+1)*(36*e^2-75*e+19)/(3*(114*e^2-159*e-7)) ≤ (124/1000:ℝ) := by
  have he0 : 0 ≤ e := by linarith
  have he2 : (1/36:ℝ) ≤ e^2 := by nlinarith
  have he2' : e^2 ≤ (167/1000:ℝ)^2 := by nlinarith
  have he3 : (1/216:ℝ) ≤ e^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (sq_nonneg e)]
  have he3' : e^3 ≤ (167/1000:ℝ)^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he') (sq_nonneg e)]
  have hd : 3*(114*e^2-159*e-7) < 0 := by nlinarith
  constructor
  · rw [le_div_iff_of_neg hd]
    nlinarith
  · rw [div_le_iff_of_neg hd]
    nlinarith

theorem ell_lower : (1/6:ℝ) ≤ QRH.ell := QRH.ell_interval.1

theorem ell_sharp_upper : QRH.ell ≤ (167/1000:ℝ) := QRH.ell_interval.2

theorem ell_bounds : 0 < QRH.ell ∧ QRH.ell < (1/5:ℝ) := by
  constructor <;> linarith [ell_lower, ell_sharp_upper]

theorem ell_upper : QRH.ell < (1/5:ℝ) := ell_bounds.2

theorem ell_ne_zero : QRH.ell ≠ 0 := ne_of_gt ell_bounds.1

theorem b_lower : (123/1000:ℝ) ≤ QRH.b :=
  (shape_bounds ell_lower ell_sharp_upper).1

theorem b_upper : QRH.b ≤ (124/1000:ℝ) :=
  (shape_bounds ell_lower ell_sharp_upper).2

theorem b_pos : 0 < QRH.b := by linarith [b_lower]

theorem theta_strict_lower : (87/100:ℝ) < QRH.tightTheta := by
  have h := ell_sharp_upper
  unfold QRH.ell at h
  linarith

theorem theta_lower : (87/100:ℝ) ≤ QRH.tightTheta := theta_strict_lower.le

theorem kappa_lower : (13/18:ℝ) ≤ QRH.kappa0 := by
  unfold QRH.kappa0
  linarith [theta_lower]

theorem kappa_upper : QRH.kappa0 ≤ (3/4:ℝ) := by
  have he := ell_lower
  unfold QRH.ell at he
  unfold QRH.kappa0
  linarith

theorem lx_lower : (7/20:ℝ) ≤ QRH.lx := by
  unfold QRH.lx QRH.M
  linarith [ell_sharp_upper, b_upper]

theorem lx_upper : QRH.lx ≤ (9/25:ℝ) := by
  unfold QRH.lx QRH.M
  linarith [ell_lower, b_lower]

theorem lx_bounds : 0 ≤ QRH.lx ∧ QRH.lx ≤ 1 := by
  constructor <;> linarith [lx_lower, lx_upper]

theorem ly_lower : (239/500:ℝ) ≤ QRH.ly := by
  unfold QRH.ly QRH.M
  linarith [ell_sharp_upper, b_lower]

theorem ly_upper : QRH.ly ≤ (12/25:ℝ) := by
  unfold QRH.ly QRH.M
  linarith [ell_lower, b_upper]

theorem ly_nonneg : 0 ≤ QRH.ly := by linarith [ly_lower]

theorem h_lower : (4/5:ℝ) ≤ QRH.h := by
  unfold QRH.h
  linarith [lx_upper, ell_lower]

theorem h_sharp_upper : QRH.h ≤ (21/25:ℝ) := by
  unfold QRH.h
  linarith [lx_lower, ell_sharp_upper]

theorem h_upper : QRH.h ≤ (9/10:ℝ) := by linarith [h_sharp_upper]

theorem h_zeta_upper : QRH.h+QRH.zeta ≤ (17/20:ℝ) := by
  have h := h_sharp_upper
  norm_num [QRH.zeta] at *
  linarith

theorem h_add_slack_upper {ζ : ℝ} (hζ : ζ ≤ (1/100:ℝ)) :
    QRH.h+ζ ≤ (17/20:ℝ) := by linarith [h_sharp_upper]

theorem mass_bounds : (49/100:ℝ)+2*QRH.ell < QRH.M ∧ QRH.M ≤ 1 := by
  unfold QRH.M
  constructor <;> linarith [ell_lower, ell_sharp_upper]

theorem C_pos : 0 < QRH.C QRH.tightTheta := by
  rw [QRH.C_formula]
  linarith [theta_lower, b_upper]

theorem lx_minus_ell_pos : 0 < QRH.lx-QRH.ell := by
  linarith [lx_lower, ell_sharp_upper]

theorem double_lx_gap_pos : 0 < 2*QRH.lx-QRH.ly-QRH.ell := by
  linarith [lx_lower, ly_upper, ell_sharp_upper]

theorem lx_le_ly : QRH.lx ≤ QRH.ly := by linarith [lx_upper, ly_lower]

theorem transport_geometry : (7/100:ℝ) ≤ QRH.ly/2-(13/75)*QRH.h-1/50 := by
  linarith [ly_lower, h_sharp_upper]

end QRH.NumericFacts
