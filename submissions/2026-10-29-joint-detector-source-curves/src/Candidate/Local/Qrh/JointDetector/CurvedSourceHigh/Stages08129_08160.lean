/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08129_08160
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08129_08160
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08129_08160
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08129_08160 Qrh.JointDetector.CurvedSourceFractions.Stages08129_08160 $number $index $kind $mode $r)
cs 8129 0 2 1 (0)
cs 8130 1 2 1 (0)
cs 8131 2 2 1 (0)
cs 8132 3 2 1 (0)
cs 8133 4 2 1 (0)
cs 8134 5 2 1 (0)
cs 8135 6 2 1 (0)
cs 8136 7 2 1 (0)
cs 8137 8 2 1 (0)
cs 8138 9 2 1 (0)
cs 8139 10 2 1 (0)
cs 8140 11 2 1 (0)
cs 8141 12 2 1 (0)
cs 8142 13 2 1 (0)
cs 8143 14 2 1 (0)
cs 8144 15 2 1 (0)
cs 8145 16 2 1 (0)
cs 8146 17 2 1 (0)
cs 8147 18 2 1 (0)
cs 8148 19 2 1 (0)
cs 8149 20 2 1 (0)
cs 8150 21 2 1 (0)
cs 8151 22 2 1 (0)
cs 8152 23 2 1 (0)
cs 8153 24 2 1 (0)
cs 8154 25 2 1 (0)
cs 8155 26 2 1 (0)
cs 8156 27 2 1 (0)
cs 8157 28 2 1 (0)
cs 8158 29 2 1 (0)
cs 8159 30 2 1 (0)
cs 8160 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08129_08160
