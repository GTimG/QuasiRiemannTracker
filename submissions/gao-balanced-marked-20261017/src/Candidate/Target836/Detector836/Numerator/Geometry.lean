/- Private .874836 scalar specialization. Adapted from accepted Hailey Collet,
OpenAI, weighted PR6 and Cycle63 sources; Apache-2.0. -/
import Candidate.Target836.Detector836.Feedback
namespace Target836.Assembly
noncomputable section
open Target836.Arithmetic
def signalShift : ℝ := -(5/6-x/3-ell/6)
def signal (s : ℝ) : ℝ := s+signalShift
theorem signalShift_eq : signalShift=-(4+(y-x))/6 := by
  unfold signalShift
  linarith [x_add_y]
theorem signal_at_boundary : signal theta=x/2+(y-x)/12 := by
  unfold signal signalShift
  linarith [ell_eq,x_add_y]
end
end Target836.Assembly

#print axioms Target836.Assembly.signal_at_boundary
