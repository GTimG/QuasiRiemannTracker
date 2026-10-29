/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages10401_10432
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages10401_10432
namespace Qrh.JointDetector.CurvedSourceHigh.Stages10401_10432
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages10401_10432 Qrh.JointDetector.CurvedSourceFractions.Stages10401_10432 $number $index $kind $mode $r)
cs 10401 0 2 1 (0)
cs 10402 1 2 1 (0)
cs 10403 2 2 1 (0)
cs 10404 3 2 1 (0)
cs 10405 4 2 1 (0)
cs 10406 5 2 1 (0)
cs 10407 6 2 1 (0)
cs 10408 7 2 1 (0)
cs 10409 8 2 1 (0)
cs 10410 9 2 1 (0)
cs 10411 10 2 1 (0)
cs 10412 11 2 1 (0)
cs 10413 12 2 1 (0)
cs 10414 13 2 1 (0)
cs 10415 14 2 1 (0)
cs 10416 15 2 1 (0)
cs 10417 16 2 1 (0)
cs 10418 17 2 1 (0)
cs 10419 18 2 1 (0)
cs 10420 19 2 1 (0)
cs 10421 20 2 1 (0)
cs 10422 21 2 1 (0)
cs 10423 22 2 1 (0)
cs 10424 23 2 1 (0)
cs 10425 24 2 1 (0)
cs 10426 25 2 1 (0)
cs 10427 26 2 1 (0)
cs 10428 27 2 1 (0)
cs 10429 28 2 1 (0)
cs 10430 29 2 1 (0)
cs 10431 30 2 1 (0)
cs 10432 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages10401_10432
