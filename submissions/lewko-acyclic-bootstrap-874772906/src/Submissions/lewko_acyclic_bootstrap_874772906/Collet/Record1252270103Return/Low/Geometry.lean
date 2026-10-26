import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.Geometry
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! Exact low-probe geometry. All lengths refer to Cycle61, including the total ray length. -/
namespace QRH.Record1252270103Return.LowGeometry
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters]
open QRH.Record1252270103Return.Geometry

theorem x_pos : 0 < x := by linarith [ell_pos, ell_lt_x]
theorem b_pos : 0 < y-x := by linarith [x_lt_y]
theorem signal_pos : 0 < signal theta := by
  rw [signal_at_boundary]
  linarith [x_pos, b_pos]
theorem scale_square : (2*x-y)+y=2*x := by ring
theorem gram_power (δ : ℝ) :
    x+(y-x)*(1/6)+y*δ = 2*signal theta+y*δ := by
  rw [signal_at_boundary]
  ring
theorem gram_sqrt_power (δ : ℝ) :
    (2*signal theta+y*δ)*(1/2) = signal theta+(y/2)*δ := by ring
theorem dilation_gap : 0 < 2*x-y-ell := Parameters.dilation_gap
 theorem dilation_le_y : 2*x-y ≤ y := by linarith [x_lt_y]
 theorem tuple_margin_neg : 1+3*ell-2*(x+y) < 0 := Parameters.tuple_margin_neg
end
end QRH.Record1252270103Return.LowGeometry
