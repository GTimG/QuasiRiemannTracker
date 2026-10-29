/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages15521_15552
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages15521_15552
namespace Qrh.JointDetector.CurvedSourceHigh.Stages15521_15552
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages15521_15552 Qrh.JointDetector.CurvedSourceFractions.Stages15521_15552 $number $index $kind $mode $r)
cs 15521 0 1 0 (1)
cs 15522 1 1 0 (1)
cs 15523 2 1 0 (1)
cs 15524 3 1 0 (1)
cs 15525 4 1 0 (1)
cs 15526 5 1 0 (1)
cs 15527 6 1 0 (1)
cs 15528 7 1 0 (1)
cs 15529 8 1 0 (1)
cs 15530 9 1 0 (1)
cs 15531 10 1 0 (1)
cs 15532 11 1 0 (1)
cs 15533 12 1 0 (1)
cs 15534 13 1 0 (1)
cs 15535 14 1 0 (1)
cs 15536 15 1 0 (1)
cs 15537 16 1 0 (1)
cs 15538 17 1 0 (1)
cs 15539 18 1 0 (1)
cs 15540 19 1 0 (1)
cs 15541 20 1 0 (1)
cs 15542 21 1 0 (1)
cs 15543 22 1 0 (1)
cs 15544 23 1 0 (1)
cs 15545 24 1 0 (1)
cs 15546 25 1 0 (1)
cs 15547 26 1 0 (1)
cs 15548 27 1 0 (1)
cs 15549 28 1 0 (1)
cs 15550 29 1 0 (1)
cs 15551 30 1 0 (1)
cs 15552 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages15521_15552
