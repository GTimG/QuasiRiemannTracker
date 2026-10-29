/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages15105_15136
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages15105_15136
namespace Qrh.JointDetector.CurvedSourceHigh.Stages15105_15136
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages15105_15136 Qrh.JointDetector.CurvedSourceFractions.Stages15105_15136 $number $index $kind $mode $r)
cs 15105 0 1 0 (1)
cs 15106 1 1 0 (1)
cs 15107 2 1 0 (1)
cs 15108 3 1 0 (1)
cs 15109 4 1 0 (1)
cs 15110 5 1 0 (1)
cs 15111 6 1 0 (1)
cs 15112 7 1 0 (1)
cs 15113 8 1 0 (1)
cs 15114 9 1 0 (1)
cs 15115 10 1 0 (1)
cs 15116 11 1 0 (1)
cs 15117 12 1 0 (1)
cs 15118 13 1 0 (1)
cs 15119 14 1 0 (1)
cs 15120 15 1 0 (1)
cs 15121 16 1 0 (1)
cs 15122 17 1 0 (1)
cs 15123 18 1 0 (1)
cs 15124 19 1 0 (1)
cs 15125 20 1 0 (1)
cs 15126 21 1 0 (1)
cs 15127 22 1 0 (1)
cs 15128 23 1 0 (1)
cs 15129 24 1 0 (1)
cs 15130 25 1 0 (1)
cs 15131 26 1 0 (1)
cs 15132 27 1 0 (1)
cs 15133 28 1 0 (1)
cs 15134 29 1 0 (1)
cs 15135 30 1 0 (1)
cs 15136 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages15105_15136
