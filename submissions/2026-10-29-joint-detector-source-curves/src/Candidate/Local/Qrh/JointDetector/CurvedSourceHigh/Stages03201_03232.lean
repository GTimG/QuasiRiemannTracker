/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages03201_03232
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages03201_03232
namespace Qrh.JointDetector.CurvedSourceHigh.Stages03201_03232
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages03201_03232 Qrh.JointDetector.CurvedSourceFractions.Stages03201_03232 $number $index $kind $mode $r)
cs 3201 0 2 1 (0)
cs 3202 1 2 1 (0)
cs 3203 2 2 1 (0)
cs 3204 3 2 1 (0)
cs 3205 4 2 1 (0)
cs 3206 5 2 1 (0)
cs 3207 6 2 1 (0)
cs 3208 7 2 1 (0)
cs 3209 8 2 1 (0)
cs 3210 9 2 1 (0)
cs 3211 10 2 1 (0)
cs 3212 11 2 1 (0)
cs 3213 12 2 1 (0)
cs 3214 13 2 1 (0)
cs 3215 14 2 1 (0)
cs 3216 15 2 1 (0)
cs 3217 16 2 1 (0)
cs 3218 17 2 1 (0)
cs 3219 18 2 1 (0)
cs 3220 19 2 1 (0)
cs 3221 20 2 1 (0)
cs 3222 21 2 1 (0)
cs 3223 22 2 1 (0)
cs 3224 23 2 1 (0)
cs 3225 24 2 1 (0)
cs 3226 25 2 1 (0)
cs 3227 26 2 1 (0)
cs 3228 27 2 1 (0)
cs 3229 28 2 1 (0)
cs 3230 29 2 1 (0)
cs 3231 30 2 1 (0)
cs 3232 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages03201_03232
