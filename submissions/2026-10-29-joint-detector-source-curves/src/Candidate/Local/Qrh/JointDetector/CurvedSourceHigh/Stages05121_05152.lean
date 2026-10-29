/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages05121_05152
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages05121_05152
namespace Qrh.JointDetector.CurvedSourceHigh.Stages05121_05152
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages05121_05152 Qrh.JointDetector.CurvedSourceFractions.Stages05121_05152 $number $index $kind $mode $r)
cs 5121 0 2 1 (0)
cs 5122 1 2 1 (0)
cs 5123 2 2 1 (0)
cs 5124 3 2 1 (0)
cs 5125 4 2 1 (0)
cs 5126 5 2 1 (0)
cs 5127 6 2 1 (0)
cs 5128 7 2 1 (0)
cs 5129 8 2 1 (0)
cs 5130 9 2 1 (0)
cs 5131 10 2 1 (0)
cs 5132 11 2 1 (0)
cs 5133 12 2 1 (0)
cs 5134 13 2 1 (0)
cs 5135 14 2 1 (0)
cs 5136 15 2 1 (0)
cs 5137 16 2 1 (0)
cs 5138 17 2 1 (0)
cs 5139 18 2 1 (0)
cs 5140 19 2 1 (0)
cs 5141 20 2 1 (0)
cs 5142 21 2 1 (0)
cs 5143 22 2 1 (0)
cs 5144 23 2 1 (0)
cs 5145 24 2 1 (0)
cs 5146 25 2 1 (0)
cs 5147 26 2 1 (0)
cs 5148 27 2 1 (0)
cs 5149 28 2 1 (0)
cs 5150 29 2 1 (0)
cs 5151 30 2 1 (0)
cs 5152 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages05121_05152
