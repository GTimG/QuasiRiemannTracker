/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages09121_09152
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages09121_09152
namespace Qrh.JointDetector.CurvedSourceHigh.Stages09121_09152
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages09121_09152 Qrh.JointDetector.CurvedSourceFractions.Stages09121_09152 $number $index $kind $mode $r)
cs 9121 0 2 1 (0)
cs 9122 1 2 1 (0)
cs 9123 2 2 1 (0)
cs 9124 3 2 1 (0)
cs 9125 4 2 1 (0)
cs 9126 5 2 1 (0)
cs 9127 6 2 1 (0)
cs 9128 7 2 1 (0)
cs 9129 8 2 1 (0)
cs 9130 9 2 1 (0)
cs 9131 10 2 1 (0)
cs 9132 11 2 1 (0)
cs 9133 12 2 1 (0)
cs 9134 13 2 1 (0)
cs 9135 14 2 1 (0)
cs 9136 15 2 1 (0)
cs 9137 16 2 1 (0)
cs 9138 17 2 1 (0)
cs 9139 18 2 1 (0)
cs 9140 19 2 1 (0)
cs 9141 20 2 1 (0)
cs 9142 21 2 1 (0)
cs 9143 22 2 1 (0)
cs 9144 23 2 1 (0)
cs 9145 24 2 1 (0)
cs 9146 25 2 1 (0)
cs 9147 26 2 1 (0)
cs 9148 27 2 1 (0)
cs 9149 28 2 1 (0)
cs 9150 29 2 1 (0)
cs 9151 30 2 1 (0)
cs 9152 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages09121_09152
