/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages05089_05120
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages05089_05120
namespace Qrh.JointDetector.CurvedSourceHigh.Stages05089_05120
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages05089_05120 Qrh.JointDetector.CurvedSourceFractions.Stages05089_05120 $number $index $kind $mode $r)
cs 5089 0 2 1 (0)
cs 5090 1 2 1 (0)
cs 5091 2 2 1 (0)
cs 5092 3 2 1 (0)
cs 5093 4 2 1 (0)
cs 5094 5 2 1 (0)
cs 5095 6 2 1 (0)
cs 5096 7 2 1 (0)
cs 5097 8 2 1 (0)
cs 5098 9 2 1 (0)
cs 5099 10 2 1 (0)
cs 5100 11 2 1 (0)
cs 5101 12 2 1 (0)
cs 5102 13 2 1 (0)
cs 5103 14 2 1 (0)
cs 5104 15 2 1 (0)
cs 5105 16 2 1 (0)
cs 5106 17 2 1 (0)
cs 5107 18 2 1 (0)
cs 5108 19 2 1 (0)
cs 5109 20 2 1 (0)
cs 5110 21 2 1 (0)
cs 5111 22 2 1 (0)
cs 5112 23 2 1 (0)
cs 5113 24 2 1 (0)
cs 5114 25 2 1 (0)
cs 5115 26 2 1 (0)
cs 5116 27 2 1 (0)
cs 5117 28 2 1 (0)
cs 5118 29 2 1 (0)
cs 5119 30 2 1 (0)
cs 5120 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages05089_05120
