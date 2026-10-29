/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages02241_02272
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages02241_02272
namespace Qrh.JointDetector.CurvedSourceHigh.Stages02241_02272
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages02241_02272 Qrh.JointDetector.CurvedSourceFractions.Stages02241_02272 $number $index $kind $mode $r)
cs 2241 0 2 1 (0)
cs 2242 1 2 1 (0)
cs 2243 2 2 1 (0)
cs 2244 3 2 1 (0)
cs 2245 4 2 1 (0)
cs 2246 5 2 1 (0)
cs 2247 6 2 1 (0)
cs 2248 7 2 1 (0)
cs 2249 8 2 1 (0)
cs 2250 9 2 1 (0)
cs 2251 10 2 1 (0)
cs 2252 11 2 1 (0)
cs 2253 12 2 1 (0)
cs 2254 13 2 1 (0)
cs 2255 14 2 1 (0)
cs 2256 15 2 1 (0)
cs 2257 16 2 1 (0)
cs 2258 17 2 1 (0)
cs 2259 18 2 1 (0)
cs 2260 19 2 1 (0)
cs 2261 20 2 1 (0)
cs 2262 21 2 1 (0)
cs 2263 22 2 1 (0)
cs 2264 23 2 1 (0)
cs 2265 24 2 1 (0)
cs 2266 25 2 1 (0)
cs 2267 26 2 1 (0)
cs 2268 27 2 1 (0)
cs 2269 28 2 1 (0)
cs 2270 29 2 1 (0)
cs 2271 30 2 1 (0)
cs 2272 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages02241_02272
