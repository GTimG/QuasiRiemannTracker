/- Private .874836 LOW probe, adapted from credited accepted source; Apache-2.0. -/
import Candidate.Target836.Detector836.Transport.GeometryFacts
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Target836.Assembly
noncomputable section
open Target836.Arithmetic
theorem marked_tuple_margin :
    1+3*ell-2*(x+y) = (-6127/37500:ℝ) := by
  norm_num [ell,x,y]
theorem marked_short_margin :
    y-2*x+ell = (-58109/500000:ℝ) := by
  norm_num [ell,x,y]
theorem marked_subset_decreases {v:ℝ} (hv:0≤ v) :
    -v+max 0 (1+3*ell-2*(x+y)+v)/8 ≤ 0 := by
  have hn : 1+3*ell-2*(x+y)<0 := by rw [marked_tuple_margin];norm_num
  have hm : max 0 (1+3*ell-2*(x+y)+v)≤8*v := max_le (by linarith) (by linarith)
  linarith
end
end Target836.Assembly
/-! Exact low-probe geometry. All lengths refer to Cycle63, including the total ray length. -/
namespace Target836.Assembly.LowGeometry
noncomputable section
open Target836.Arithmetic

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
end Target836.Assembly.LowGeometry

#print axioms Target836.Assembly.LowGeometry.x_pos
#print axioms Target836.Assembly.LowGeometry.b_pos
#print axioms Target836.Assembly.LowGeometry.signal_pos
#print axioms Target836.Assembly.LowGeometry.scale_square
#print axioms Target836.Assembly.LowGeometry.gram_power
#print axioms Target836.Assembly.LowGeometry.gram_sqrt_power
#print axioms Target836.Assembly.LowGeometry.dilation_gap
#print axioms Target836.Assembly.LowGeometry.dilation_le_y
#print axioms Target836.Assembly.LowGeometry.tuple_margin_neg
