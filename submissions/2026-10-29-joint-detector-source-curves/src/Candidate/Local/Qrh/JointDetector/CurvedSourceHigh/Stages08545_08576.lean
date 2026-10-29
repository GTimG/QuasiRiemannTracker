/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08545_08576
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08545_08576
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08545_08576
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08545_08576 Qrh.JointDetector.CurvedSourceFractions.Stages08545_08576 $number $index $kind $mode $r)
cs 8545 0 2 1 (0)
cs 8546 1 2 1 (0)
cs 8547 2 2 1 (0)
cs 8548 3 2 1 (0)
cs 8549 4 2 1 (0)
cs 8550 5 2 1 (0)
cs 8551 6 2 1 (0)
cs 8552 7 2 1 (0)
cs 8553 8 2 1 (0)
cs 8554 9 2 1 (0)
cs 8555 10 2 1 (0)
cs 8556 11 2 1 (0)
cs 8557 12 2 1 (0)
cs 8558 13 2 1 (0)
cs 8559 14 2 1 (0)
cs 8560 15 2 1 (0)
cs 8561 16 2 1 (0)
cs 8562 17 2 1 (0)
cs 8563 18 2 1 (0)
cs 8564 19 2 1 (0)
cs 8565 20 2 1 (0)
cs 8566 21 2 1 (0)
cs 8567 22 2 1 (0)
cs 8568 23 2 1 (0)
cs 8569 24 2 1 (0)
cs 8570 25 2 1 (0)
cs 8571 26 2 1 (0)
cs 8572 27 2 1 (0)
cs 8573 28 2 1 (0)
cs 8574 29 2 1 (0)
cs 8575 30 2 1 (0)
cs 8576 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08545_08576
