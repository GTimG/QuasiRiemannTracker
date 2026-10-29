/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages17025_17046
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages17025_17046
namespace Qrh.JointDetector.CurvedSourceHigh.Stages17025_17046
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages17025_17046 Qrh.JointDetector.CurvedSourceFractions.Stages17025_17046 $number $index $kind $mode $r)
cs 17025 0 1 0 (1)
cs 17026 1 1 0 (1)
cs 17027 2 1 0 (1)
cs 17028 3 1 0 (1)
cs 17029 4 1 0 (1)
cs 17030 5 1 0 (1)
cs 17031 6 1 0 (1)
cs 17032 7 1 0 (1)
cs 17033 8 1 0 (1)
cs 17034 9 1 0 (1)
cs 17035 10 1 0 (1)
cs 17036 11 1 0 (1)
cs 17037 12 1 0 (1)
cs 17038 13 1 0 (1)
cs 17039 14 1 0 (1)
cs 17040 15 1 0 (1)
cs 17041 16 1 0 (1)
cs 17042 17 1 0 (1)
cs 17043 18 1 0 (1)
cs 17044 19 1 0 (1)
cs 17045 20 1 0 (1)
cs 17046 21 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages17025_17046
