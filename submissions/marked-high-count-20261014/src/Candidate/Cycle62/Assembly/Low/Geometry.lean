import Candidate.Cycle62.Assembly.Geometry
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! Exact low-probe geometry. All lengths refer to Cycle62, including the total ray length. -/
namespace Cycle62.Assembly.LowGeometry
noncomputable section
open Cycle62.Arithmetic

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
theorem dilation_gap : 0 < 2*x-y-ell := by
  rw [show 2*x-y-ell = -(y-2*x+ell) by ring, marked_short_margin]
  norm_num
theorem dilation_le_y : 2*x-y ≤ y := by linarith [x_lt_y]
theorem tuple_margin_neg : 1+3*ell-2*(x+y) < 0 := by
  rw [marked_tuple_margin]
  norm_num
end
end Cycle62.Assembly.LowGeometry
