/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages05281_05312
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages05281_05312
namespace Qrh.JointDetector.CurvedSourceHigh.Stages05281_05312
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages05281_05312 Qrh.JointDetector.CurvedSourceFractions.Stages05281_05312 $number $index $kind $mode $r)
cs 5281 0 2 1 (0)
cs 5282 1 2 1 (0)
cs 5283 2 2 1 (0)
cs 5284 3 2 1 (0)
cs 5285 4 2 1 (0)
cs 5286 5 2 1 (0)
cs 5287 6 2 1 (0)
cs 5288 7 2 1 (0)
cs 5289 8 2 1 (0)
cs 5290 9 2 1 (0)
cs 5291 10 2 1 (0)
cs 5292 11 2 1 (0)
cs 5293 12 2 1 (0)
cs 5294 13 2 1 (0)
cs 5295 14 2 1 (0)
cs 5296 15 2 1 (0)
cs 5297 16 2 1 (0)
cs 5298 17 2 1 (0)
cs 5299 18 2 1 (0)
cs 5300 19 2 1 (0)
cs 5301 20 2 1 (0)
cs 5302 21 2 1 (0)
cs 5303 22 2 1 (0)
cs 5304 23 2 1 (0)
cs 5305 24 2 1 (0)
cs 5306 25 2 1 (0)
cs 5307 26 2 1 (0)
cs 5308 27 2 1 (0)
cs 5309 28 2 1 (0)
cs 5310 29 2 1 (0)
cs 5311 30 2 1 (0)
cs 5312 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages05281_05312
