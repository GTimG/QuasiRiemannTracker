/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The exact stationary cutoff makes the density derivative of the critical
limiting return vanish. This is not the complete global return certificate. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.CountDensityDerivative

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section
open Qrh.TwoSlot.AnchorZeroLoss.Affine.Return

theorem baseCost_density_deriv (h : ℝ) :
    HasDerivAt (fun x => baseCost h x (1/2)) (1/2+ell-h/8) density := by
  have hh := ((hasDerivAt_id density).const_mul (1/2+ell-h/8)).const_add
    (1/2+ell/2-5*h/12)
  convert hh using 1
  · funext x
    dsimp [baseCost]
    ring
  · ring

/-- The cutoff is constructed from the derivative of the actual admitted
count. Its denominator was proved positive before this stationarity step. -/
theorem stationary_margin_deriv :
    HasDerivAt (fun x => margin stationaryCutoff x (1/2)) 0 density := by
  let f : ℝ → ℝ := fun x => theta-baseCost stationaryCutoff x (1/2)-
    (3/4)*stationaryCutoff*ExactWindow.valueI x (1/2)
  have hf : HasDerivAt f 0 density := by
    have hh := ((baseCost_density_deriv stationaryCutoff).const_sub theta).sub
      ((value_density_deriv critical_denominator_pos.ne').const_mul ((3/4)*stationaryCutoff))
    convert hh using 1
    nlinarith only [stationary_cutoff_balance]
  have hf0 : f density = 0 := by
    dsimp [f]
    rw [value_at_contact]
    exact critical_return_balance stationaryCutoff
  have hp : HasDerivAt (fun x => ExactWindow.JI x (1/2)*f x) 0 density := by
    convert (J_density_deriv density).mul hf using 1
    simp only [hf0,mul_zero,add_zero]
  apply hp.congr_of_eventuallyEq
  have hnear := (J_density_deriv density).continuousAt.eventually_ne critical_denominator_pos.ne'
  filter_upwards [hnear] with x hx
  dsimp [f]
  unfold margin ExactWindow.valueI
  field_simp [hx]

theorem stationary_margin_zero : margin stationaryCutoff density (1/2) = 0 :=
  margin_at_contact stationaryCutoff

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.stationary_margin_deriv
