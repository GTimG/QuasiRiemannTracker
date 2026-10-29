/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages07521_07552
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages07521_07552
namespace Qrh.JointDetector.CurvedSourceHigh.Stages07521_07552
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages07521_07552 Qrh.JointDetector.CurvedSourceFractions.Stages07521_07552 $number $index $kind $mode $r)
cs 7521 0 2 1 (0)
cs 7522 1 2 1 (0)
cs 7523 2 2 1 (0)
cs 7524 3 2 1 (0)
cs 7525 4 2 1 (0)
cs 7526 5 2 1 (0)
cs 7527 6 2 1 (0)
cs 7528 7 2 1 (0)
cs 7529 8 2 1 (0)
cs 7530 9 2 1 (0)
cs 7531 10 2 1 (0)
cs 7532 11 2 1 (0)
cs 7533 12 2 1 (0)
cs 7534 13 2 1 (0)
cs 7535 14 2 1 (0)
cs 7536 15 2 1 (0)
cs 7537 16 2 1 (0)
cs 7538 17 2 1 (0)
cs 7539 18 2 1 (0)
cs 7540 19 2 1 (0)
cs 7541 20 2 1 (0)
cs 7542 21 2 1 (0)
cs 7543 22 2 1 (0)
cs 7544 23 2 1 (0)
cs 7545 24 2 1 (0)
cs 7546 25 2 1 (0)
cs 7547 26 2 1 (0)
cs 7548 27 2 1 (0)
cs 7549 28 2 1 (0)
cs 7550 29 2 1 (0)
cs 7551 30 2 1 (0)
cs 7552 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages07521_07552
