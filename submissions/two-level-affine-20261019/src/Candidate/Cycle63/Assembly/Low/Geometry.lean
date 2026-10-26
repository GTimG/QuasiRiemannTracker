import Candidate.Cycle63.Assembly.Geometry
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! Exact low-probe geometry. All lengths refer to Cycle63, including the total ray length. -/
namespace Cycle63.Assembly.LowGeometry
noncomputable section
open Cycle63.Arithmetic

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
theorem dilation_gap : 0 < 2*x-y-ell := by
  have := marked_short_margin
  linarith
theorem dilation_le_y : 2*x-y ≤ y := by linarith [x_lt_y]
end
end Cycle63.Assembly.LowGeometry
