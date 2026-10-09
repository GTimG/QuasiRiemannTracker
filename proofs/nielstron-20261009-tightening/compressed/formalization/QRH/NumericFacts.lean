import QRH.Geometry

/-! Shared exact arithmetic facts used by the compressed analytic proofs. -/

namespace QRH.NumericFacts

theorem kappa_lower : (13/18:ℝ)≤QRH.kappa0 := by
  norm_num [QRH.kappa0,QRH.tightTheta]

theorem h_zeta_upper : QRH.h+QRH.zeta≤(17/20:ℝ) := by
  norm_num [QRH.h,QRH.zeta,QRH.lx,QRH.M,QRH.ell,QRH.b,QRH.tightTheta]

theorem ell_upper : QRH.ell < (1/5:ℝ) := by
  norm_num [QRH.ell, QRH.tightTheta]

theorem ell_ne_zero : QRH.ell≠0 := by
  norm_num [QRH.ell,QRH.tightTheta]

theorem h_lower : (4/5:ℝ)≤QRH.h := by
  norm_num [QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.tightTheta]

theorem h_upper : QRH.h≤9/10 := by
  norm_num [QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.tightTheta]

theorem lx_bounds : 0≤QRH.lx ∧ QRH.lx≤1 := by
  norm_num [QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.tightTheta]

theorem ly_nonneg : 0≤QRH.ly := by
  norm_num [QRH.ly,QRH.M,QRH.b,QRH.ell,QRH.tightTheta]

theorem theta_lower : (87/100:ℝ)≤QRH.tightTheta := by
  norm_num [QRH.tightTheta]

theorem ell_bounds : 0 < QRH.ell ∧ QRH.ell < (1/5:ℝ) := by
  norm_num [QRH.ell, QRH.tightTheta]

theorem mass_bounds : (49/100:ℝ) + 2*QRH.ell < QRH.M ∧ QRH.M ≤ 1 := by
  norm_num [QRH.M, QRH.ell, QRH.tightTheta]

theorem C_pos : 0 < QRH.C QRH.tightTheta := by
  rw [QRH.C_formula]; norm_num [QRH.tightTheta, QRH.b, QRH.ell]

end QRH.NumericFacts
