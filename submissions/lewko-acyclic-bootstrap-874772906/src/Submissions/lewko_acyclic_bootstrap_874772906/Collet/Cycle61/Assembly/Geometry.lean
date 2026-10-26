import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Arithmetic.LocalReserves

/-! Physical probe geometry at the exact rational Cycle61 boundary. -/
namespace Cycle61.Assembly
noncomputable section
open Arithmetic

def signalShift : ℝ := -(5/6-x/3-ell/6)
def signal (s : ℝ) : ℝ := s+signalShift

theorem theta_gt_half : (1/2 : ℝ) < theta := by norm_num [theta]
theorem theta_lt_seven_eighths : theta < (7/8 : ℝ) := by norm_num [theta]
theorem theta_lt_one : theta < 1 := by norm_num [theta]

theorem signalShift_eq : signalShift = -(4+(y-x))/6 := by
  unfold signalShift
  linarith [x_add_y]

theorem signal_at_boundary : signal theta = x/2+(y-x)/12 := by
  unfold signal signalShift
  linarith [ell_eq, x_add_y]

theorem signal_slope (s t : ℝ) : signal s-signal t = s-t := by
  unfold signal
  ring

theorem row_endpoint : h = 1-x+ell := by linarith [x_eq]

theorem marked_tuple_margin :
    1+3*ell-2*(x+y) = -(24583/150000 : ℝ) := by
  norm_num [ell, x, y]

theorem marked_short_margin :
    y-2*x+ell = -(599126039/5000000000 : ℝ) := by
  norm_num [ell, x, y]

theorem marked_subset_decreases {v : ℝ} (hv : 0 ≤ v) :
    -v+max 0 (1+3*ell-2*(x+y)+v)/8 ≤ 0 := by
  have hnegative : 1+3*ell-2*(x+y) < 0 := by
    rw [marked_tuple_margin]
    norm_num
  have hm : max 0 (1+3*ell-2*(x+y)+v) ≤ 8*v :=
    max_le (by linarith) (by linarith)
  linarith

theorem principal_remainders_positive : 0 < y/4 ∧ 0 < h/24 := by
  norm_num [y, h]

end
end Cycle61.Assembly
