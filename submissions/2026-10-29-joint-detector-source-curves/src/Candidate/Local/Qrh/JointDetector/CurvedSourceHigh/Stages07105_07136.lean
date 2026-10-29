/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages07105_07136
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages07105_07136
namespace Qrh.JointDetector.CurvedSourceHigh.Stages07105_07136
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages07105_07136 Qrh.JointDetector.CurvedSourceFractions.Stages07105_07136 $number $index $kind $mode $r)
cs 7105 0 2 1 (0)
cs 7106 1 2 1 (0)
cs 7107 2 2 1 (0)
cs 7108 3 2 1 (0)
cs 7109 4 2 1 (0)
cs 7110 5 2 1 (0)
cs 7111 6 2 1 (0)
cs 7112 7 2 1 (0)
cs 7113 8 2 1 (0)
cs 7114 9 2 1 (0)
cs 7115 10 2 1 (0)
cs 7116 11 2 1 (0)
cs 7117 12 2 1 (0)
cs 7118 13 2 1 (0)
cs 7119 14 2 1 (0)
cs 7120 15 2 1 (0)
cs 7121 16 2 1 (0)
cs 7122 17 2 1 (0)
cs 7123 18 2 1 (0)
cs 7124 19 2 1 (0)
cs 7125 20 2 1 (0)
cs 7126 21 2 1 (0)
cs 7127 22 2 1 (0)
cs 7128 23 2 1 (0)
cs 7129 24 2 1 (0)
cs 7130 25 2 1 (0)
cs 7131 26 2 1 (0)
cs 7132 27 2 1 (0)
cs 7133 28 2 1 (0)
cs 7134 29 2 1 (0)
cs 7135 30 2 1 (0)
cs 7136 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages07105_07136
