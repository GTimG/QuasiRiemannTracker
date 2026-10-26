import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Arithmetic.LocalReserves

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Assembly_Geometry : Cycle63.AffineLedger := Cycle153.Root.rootLedger


/-! Physical probe geometry at the exact rational Cycle153Endpoint boundary. -/
namespace Cycle153Endpoint.Assembly
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
end Cycle153Endpoint.Assembly
