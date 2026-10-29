/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages06113_06144
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages06113_06144
namespace Qrh.JointDetector.CurvedSourceHigh.Stages06113_06144
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages06113_06144 Qrh.JointDetector.CurvedSourceFractions.Stages06113_06144 $number $index $kind $mode $r)
cs 6113 0 2 1 (0)
cs 6114 1 2 1 (0)
cs 6115 2 2 1 (0)
cs 6116 3 2 1 (0)
cs 6117 4 2 1 (0)
cs 6118 5 2 1 (0)
cs 6119 6 2 1 (0)
cs 6120 7 2 1 (0)
cs 6121 8 2 1 (0)
cs 6122 9 2 1 (0)
cs 6123 10 2 1 (0)
cs 6124 11 2 1 (0)
cs 6125 12 2 1 (0)
cs 6126 13 2 1 (0)
cs 6127 14 2 1 (0)
cs 6128 15 2 1 (0)
cs 6129 16 2 1 (0)
cs 6130 17 2 1 (0)
cs 6131 18 2 1 (0)
cs 6132 19 2 1 (0)
cs 6133 20 2 1 (0)
cs 6134 21 2 1 (0)
cs 6135 22 2 1 (0)
cs 6136 23 2 1 (0)
cs 6137 24 2 1 (0)
cs 6138 25 2 1 (0)
cs 6139 26 2 1 (0)
cs 6140 27 2 1 (0)
cs 6141 28 2 1 (0)
cs 6142 29 2 1 (0)
cs 6143 30 2 1 (0)
cs 6144 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages06113_06144
