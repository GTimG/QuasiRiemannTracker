/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08801_08832
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08801_08832
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08801_08832
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08801_08832 Qrh.JointDetector.CurvedSourceFractions.Stages08801_08832 $number $index $kind $mode $r)
cs 8801 0 2 1 (0)
cs 8802 1 2 1 (0)
cs 8803 2 2 1 (0)
cs 8804 3 2 1 (0)
cs 8805 4 2 1 (0)
cs 8806 5 2 1 (0)
cs 8807 6 2 1 (0)
cs 8808 7 2 1 (0)
cs 8809 8 2 1 (0)
cs 8810 9 2 1 (0)
cs 8811 10 2 1 (0)
cs 8812 11 2 1 (0)
cs 8813 12 2 1 (0)
cs 8814 13 2 1 (0)
cs 8815 14 2 1 (0)
cs 8816 15 2 1 (0)
cs 8817 16 2 1 (0)
cs 8818 17 2 1 (0)
cs 8819 18 2 1 (0)
cs 8820 19 2 1 (0)
cs 8821 20 2 1 (0)
cs 8822 21 2 1 (0)
cs 8823 22 2 1 (0)
cs 8824 23 2 1 (0)
cs 8825 24 2 1 (0)
cs 8826 25 2 1 (0)
cs 8827 26 2 1 (0)
cs 8828 27 2 1 (0)
cs 8829 28 2 1 (0)
cs 8830 29 2 1 (0)
cs 8831 30 2 1 (0)
cs 8832 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08801_08832
