/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages12801_12832
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages12801_12832
namespace Qrh.JointDetector.CurvedSourceHigh.Stages12801_12832
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages12801_12832 Qrh.JointDetector.CurvedSourceFractions.Stages12801_12832 $number $index $kind $mode $r)
cs 12801 0 1 0 (1)
cs 12802 1 1 0 (1)
cs 12803 2 1 0 (1)
cs 12804 3 1 0 (1)
cs 12805 4 1 0 (1)
cs 12806 5 1 0 (1)
cs 12807 6 1 0 (1)
cs 12808 7 1 0 (1)
cs 12809 8 1 0 (1)
cs 12810 9 1 0 (1)
cs 12811 10 1 0 (1)
cs 12812 11 1 0 (1)
cs 12813 12 1 0 (1)
cs 12814 13 1 0 (1)
cs 12815 14 1 0 (1)
cs 12816 15 1 0 (1)
cs 12817 16 1 0 (1)
cs 12818 17 1 0 (1)
cs 12819 18 1 0 (1)
cs 12820 19 1 0 (1)
cs 12821 20 1 0 (1)
cs 12822 21 1 0 (1)
cs 12823 22 1 0 (1)
cs 12824 23 1 0 (1)
cs 12825 24 1 0 (1)
cs 12826 25 1 0 (1)
cs 12827 26 1 0 (1)
cs 12828 27 1 0 (1)
cs 12829 28 1 0 (1)
cs 12830 29 1 0 (1)
cs 12831 30 1 0 (1)
cs 12832 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages12801_12832
