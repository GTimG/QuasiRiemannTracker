/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04545_04576
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04545_04576
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04545_04576
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04545_04576 Qrh.JointDetector.CurvedSourceFractions.Stages04545_04576 $number $index $kind $mode $r)
cs 4545 0 2 1 (0)
cs 4546 1 2 1 (0)
cs 4547 2 2 1 (0)
cs 4548 3 2 1 (0)
cs 4549 4 2 1 (0)
cs 4550 5 2 1 (0)
cs 4551 6 2 1 (0)
cs 4552 7 2 1 (0)
cs 4553 8 2 1 (0)
cs 4554 9 2 1 (0)
cs 4555 10 2 1 (0)
cs 4556 11 2 1 (0)
cs 4557 12 2 1 (0)
cs 4558 13 2 1 (0)
cs 4559 14 2 1 (0)
cs 4560 15 2 1 (0)
cs 4561 16 2 1 (0)
cs 4562 17 2 1 (0)
cs 4563 18 2 1 (0)
cs 4564 19 2 1 (0)
cs 4565 20 2 1 (0)
cs 4566 21 2 1 (0)
cs 4567 22 2 1 (0)
cs 4568 23 2 1 (0)
cs 4569 24 2 1 (0)
cs 4570 25 2 1 (0)
cs 4571 26 2 1 (0)
cs 4572 27 2 1 (0)
cs 4573 28 2 1 (0)
cs 4574 29 2 1 (0)
cs 4575 30 2 1 (0)
cs 4576 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04545_04576
