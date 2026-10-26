import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.LocalReserves
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-! Physical probe geometry at the exact rational Cycle63 boundary. -/
namespace Cycle63.Assembly
noncomputable section
open Arithmetic

def signalShift : ℝ := -(5/6-x/3-ell/6)
def signal (s : ℝ) : ℝ := s+signalShift

theorem theta_gt_half : (1/2 : ℝ) < theta := by norm_num [theta]
theorem theta_lt_seven_eighths : theta < (7/8 : ℝ) := by norm_num [theta]

theorem signalShift_eq : signalShift = -(4+(y-x))/6 := by
  unfold signalShift
  linarith [x_add_y]

theorem signal_at_boundary : signal theta = x/2+(y-x)/12 := by
  unfold signal signalShift
  linarith [ell_eq, x_add_y]

theorem row_endpoint : h = 1-x+ell := by linarith [x_eq]

theorem marked_short_margin : y-2*x+ell < 0 := by
  have hh := h_bounds
  unfold x y
  norm_num [ell, theta]
  linarith [hh.2]

end
end Cycle63.Assembly

end Record1252270103Bootstrap.PR67
