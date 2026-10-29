/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages16385_16416
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages16385_16416
namespace Qrh.JointDetector.CurvedSourceHigh.Stages16385_16416
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages16385_16416 Qrh.JointDetector.CurvedSourceFractions.Stages16385_16416 $number $index $kind $mode $r)
cs 16385 0 1 0 (1)
cs 16386 1 1 0 (1)
cs 16387 2 1 0 (1)
cs 16388 3 1 0 (1)
cs 16389 4 1 0 (1)
cs 16390 5 1 0 (1)
cs 16391 6 1 0 (1)
cs 16392 7 1 0 (1)
cs 16393 8 1 0 (1)
cs 16394 9 1 0 (1)
cs 16395 10 1 0 (1)
cs 16396 11 1 0 (1)
cs 16397 12 1 0 (1)
cs 16398 13 1 0 (1)
cs 16399 14 1 0 (1)
cs 16400 15 1 0 (1)
cs 16401 16 1 0 (1)
cs 16402 17 1 0 (1)
cs 16403 18 1 0 (1)
cs 16404 19 1 0 (1)
cs 16405 20 1 0 (1)
cs 16406 21 1 0 (1)
cs 16407 22 1 0 (1)
cs 16408 23 1 0 (1)
cs 16409 24 1 0 (1)
cs 16410 25 1 0 (1)
cs 16411 26 1 0 (1)
cs 16412 27 1 0 (1)
cs 16413 28 1 0 (1)
cs 16414 29 1 0 (1)
cs 16415 30 1 0 (1)
cs 16416 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages16385_16416
