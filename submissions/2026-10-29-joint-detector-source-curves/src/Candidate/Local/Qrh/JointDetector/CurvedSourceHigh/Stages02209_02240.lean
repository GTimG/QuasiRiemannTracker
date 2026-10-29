/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages02209_02240
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages02209_02240
namespace Qrh.JointDetector.CurvedSourceHigh.Stages02209_02240
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages02209_02240 Qrh.JointDetector.CurvedSourceFractions.Stages02209_02240 $number $index $kind $mode $r)
cs 2209 0 2 1 (0)
cs 2210 1 2 1 (0)
cs 2211 2 2 1 (0)
cs 2212 3 2 1 (0)
cs 2213 4 2 1 (0)
cs 2214 5 2 1 (0)
cs 2215 6 2 1 (0)
cs 2216 7 2 1 (0)
cs 2217 8 2 1 (0)
cs 2218 9 2 1 (0)
cs 2219 10 2 1 (0)
cs 2220 11 2 1 (0)
cs 2221 12 2 1 (0)
cs 2222 13 2 1 (0)
cs 2223 14 2 1 (0)
cs 2224 15 2 1 (0)
cs 2225 16 2 1 (0)
cs 2226 17 2 1 (0)
cs 2227 18 2 1 (0)
cs 2228 19 2 1 (0)
cs 2229 20 2 1 (0)
cs 2230 21 2 1 (0)
cs 2231 22 2 1 (0)
cs 2232 23 2 1 (0)
cs 2233 24 2 1 (0)
cs 2234 25 2 1 (0)
cs 2235 26 2 1 (0)
cs 2236 27 2 1 (0)
cs 2237 28 2 1 (0)
cs 2238 29 2 1 (0)
cs 2239 30 2 1 (0)
cs 2240 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages02209_02240
