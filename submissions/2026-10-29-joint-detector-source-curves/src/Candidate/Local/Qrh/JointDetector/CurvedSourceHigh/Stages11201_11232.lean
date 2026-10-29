/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages11201_11232
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages11201_11232
namespace Qrh.JointDetector.CurvedSourceHigh.Stages11201_11232
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages11201_11232 Qrh.JointDetector.CurvedSourceFractions.Stages11201_11232 $number $index $kind $mode $r)
cs 11201 0 2 1 (0)
cs 11202 1 2 1 (0)
cs 11203 2 2 1 (0)
cs 11204 3 2 1 (0)
cs 11205 4 2 1 (0)
cs 11206 5 2 1 (0)
cs 11207 6 2 1 (0)
cs 11208 7 2 1 (0)
cs 11209 8 2 1 (0)
cs 11210 9 2 1 (0)
cs 11211 10 2 1 (0)
cs 11212 11 2 1 (0)
cs 11213 12 2 1 (0)
cs 11214 13 2 1 (0)
cs 11215 14 2 1 (0)
cs 11216 15 2 1 (0)
cs 11217 16 2 1 (0)
cs 11218 17 2 1 (0)
cs 11219 18 2 1 (0)
cs 11220 19 2 1 (0)
cs 11221 20 2 1 (0)
cs 11222 21 2 1 (0)
cs 11223 22 2 1 (0)
cs 11224 23 2 1 (0)
cs 11225 24 2 1 (0)
cs 11226 25 2 1 (0)
cs 11227 26 2 1 (0)
cs 11228 27 2 1 (0)
cs 11229 28 2 1 (0)
cs 11230 29 2 1 (0)
cs 11231 30 2 1 (0)
cs 11232 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages11201_11232
