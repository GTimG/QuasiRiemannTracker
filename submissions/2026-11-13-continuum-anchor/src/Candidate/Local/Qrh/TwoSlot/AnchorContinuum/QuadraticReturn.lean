/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Exact square factorization of the maximum-amplitude limiting return. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.CutoffBounds

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section
open Qrh.TwoSlot.AnchorZeroLoss.Affine.Return

def curvature (h : ℝ) : ℝ :=
  -jSlope*(1/2+ell-h/8)+(3/4)*h*(jSlope+criticalU)
def densityDerivative (h : ℝ) : ℝ :=
  jSlope*(theta-baseCost h density (1/2))-
    ExactWindow.JI density (1/2)*(1/2+ell-h/8)-
    (3/4)*h*(-ExactWindow.JI density (1/2)+(1-density)*jSlope+
      (5/6-2*density)*criticalU)

theorem margin_density_deriv (h : ℝ) :
    HasDerivAt (fun x => margin h x (1/2)) (densityDerivative h) density := by
  have hh := ((J_density_deriv density).mul ((baseCost_density_deriv h).const_sub theta)).sub
    ((N_density_deriv density).const_mul ((3/4)*h))
  convert hh using 1 <;> (try funext x) <;> dsimp [margin,densityDerivative] <;> ring

theorem stationary_densityDerivative_zero : densityDerivative stationaryCutoff = 0 :=
  (margin_density_deriv stationaryCutoff).unique stationary_margin_deriv

theorem quadratic_expansion (h d : ℝ) :
    margin h d (1/2) = curvature h*(d-density)^2+
      densityDerivative h*(d-density)+margin h density (1/2) := by
  unfold margin curvature densityDerivative baseCost ExactWindow.NI ExactWindow.JI
    ExactWindow.kI jSlope criticalU ExactWindow.UI
  ring

theorem stationary_curvature_pos : (1/5:ℝ) < curvature stationaryCutoff := by
  have hs := negative_jSlope_sharp
  have hu := critical_U_sharp
  have he := ell_bounds
  have hh := stationaryCutoff_bounds
  have hm0 := mul_le_mul hs.1 (show (67328/100000:ℝ) ≤ 1/2+ell by linarith [he.1])
    (by norm_num : (0:ℝ) ≤ 67328/100000) (show 0 ≤ -jSlope by linarith [hs.1])
  have hb : -(7/8)*jSlope-(3/4)*criticalU ≤ (30493/20000:ℝ) := by
    linarith [hs.2,hu.1]
  have hb0 : 0 ≤ -(7/8)*jSlope-(3/4)*criticalU := by linarith [hs.1,hu.2]
  have hm1 := mul_le_mul hh.2.le hb hb0 (by norm_num : (0:ℝ) ≤ 102/125)
  unfold curvature
  nlinarith only [hm0,hm1]

theorem maximum_amplitude_factorization (d : ℝ) :
    margin stationaryCutoff d (1/2) = curvature stationaryCutoff*(d-density)^2 := by
  rw [quadratic_expansion,stationary_densityDerivative_zero,stationary_margin_zero]
  ring

theorem maximum_amplitude_nonnegative (d : ℝ) : 0 ≤ margin stationaryCutoff d (1/2) := by
  rw [maximum_amplitude_factorization]
  exact mul_nonneg (by linarith [stationary_curvature_pos]) (sq_nonneg _)

theorem maximum_amplitude_zero_iff (d : ℝ) :
    margin stationaryCutoff d (1/2) = 0 ↔ d = density := by
  rw [maximum_amplitude_factorization,mul_eq_zero]
  have hc : curvature stationaryCutoff ≠ 0 := by linarith [stationary_curvature_pos]
  simp only [hc,false_or,pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0),sub_eq_zero]

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.maximum_amplitude_factorization
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.maximum_amplitude_nonnegative
