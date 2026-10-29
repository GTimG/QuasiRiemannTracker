/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04129_04160
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04129_04160
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04129_04160
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04129_04160 Qrh.JointDetector.CurvedSourceFractions.Stages04129_04160 $number $index $kind $mode $r)
cs 4129 0 2 1 (0)
cs 4130 1 2 1 (0)
cs 4131 2 2 1 (0)
cs 4132 3 2 1 (0)
cs 4133 4 2 1 (0)
cs 4134 5 2 1 (0)
cs 4135 6 2 1 (0)
cs 4136 7 2 1 (0)
cs 4137 8 2 1 (0)
cs 4138 9 2 1 (0)
cs 4139 10 2 1 (0)
cs 4140 11 2 1 (0)
cs 4141 12 2 1 (0)
cs 4142 13 2 1 (0)
cs 4143 14 2 1 (0)
cs 4144 15 2 1 (0)
cs 4145 16 2 1 (0)
cs 4146 17 2 1 (0)
cs 4147 18 2 1 (0)
cs 4148 19 2 1 (0)
cs 4149 20 2 1 (0)
cs 4150 21 2 1 (0)
cs 4151 22 2 1 (0)
cs 4152 23 2 1 (0)
cs 4153 24 2 1 (0)
cs 4154 25 2 1 (0)
cs 4155 26 2 1 (0)
cs 4156 27 2 1 (0)
cs 4157 28 2 1 (0)
cs 4158 29 2 1 (0)
cs 4159 30 2 1 (0)
cs 4160 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04129_04160
