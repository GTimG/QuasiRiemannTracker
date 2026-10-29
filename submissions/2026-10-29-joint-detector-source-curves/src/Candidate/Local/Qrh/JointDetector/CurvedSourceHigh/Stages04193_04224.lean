/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04193_04224
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04193_04224
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04193_04224
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04193_04224 Qrh.JointDetector.CurvedSourceFractions.Stages04193_04224 $number $index $kind $mode $r)
cs 4193 0 2 1 (0)
cs 4194 1 2 1 (0)
cs 4195 2 2 1 (0)
cs 4196 3 2 1 (0)
cs 4197 4 2 1 (0)
cs 4198 5 2 1 (0)
cs 4199 6 2 1 (0)
cs 4200 7 2 1 (0)
cs 4201 8 2 1 (0)
cs 4202 9 2 1 (0)
cs 4203 10 2 1 (0)
cs 4204 11 2 1 (0)
cs 4205 12 2 1 (0)
cs 4206 13 2 1 (0)
cs 4207 14 2 1 (0)
cs 4208 15 2 1 (0)
cs 4209 16 2 1 (0)
cs 4210 17 2 1 (0)
cs 4211 18 2 1 (0)
cs 4212 19 2 1 (0)
cs 4213 20 2 1 (0)
cs 4214 21 2 1 (0)
cs 4215 22 2 1 (0)
cs 4216 23 2 1 (0)
cs 4217 24 2 1 (0)
cs 4218 25 2 1 (0)
cs 4219 26 2 1 (0)
cs 4220 27 2 1 (0)
cs 4221 28 2 1 (0)
cs 4222 29 2 1 (0)
cs 4223 30 2 1 (0)
cs 4224 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04193_04224
