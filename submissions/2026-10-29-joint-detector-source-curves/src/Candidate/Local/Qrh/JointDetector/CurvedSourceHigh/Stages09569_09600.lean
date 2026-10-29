/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages09569_09600
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages09569_09600
namespace Qrh.JointDetector.CurvedSourceHigh.Stages09569_09600
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages09569_09600 Qrh.JointDetector.CurvedSourceFractions.Stages09569_09600 $number $index $kind $mode $r)
cs 9569 0 2 1 (0)
cs 9570 1 2 1 (0)
cs 9571 2 2 1 (0)
cs 9572 3 2 1 (0)
cs 9573 4 2 1 (0)
cs 9574 5 2 1 (0)
cs 9575 6 2 1 (0)
cs 9576 7 2 1 (0)
cs 9577 8 2 1 (0)
cs 9578 9 2 1 (0)
cs 9579 10 2 1 (0)
cs 9580 11 2 1 (0)
cs 9581 12 2 1 (0)
cs 9582 13 2 1 (0)
cs 9583 14 2 1 (0)
cs 9584 15 2 1 (0)
cs 9585 16 2 1 (0)
cs 9586 17 2 1 (0)
cs 9587 18 2 1 (0)
cs 9588 19 2 1 (0)
cs 9589 20 2 1 (0)
cs 9590 21 2 1 (0)
cs 9591 22 2 1 (0)
cs 9592 23 2 1 (0)
cs 9593 24 2 1 (0)
cs 9594 25 2 1 (0)
cs 9595 26 2 1 (0)
cs 9596 27 2 1 (0)
cs 9597 28 2 1 (0)
cs 9598 29 2 1 (0)
cs 9599 30 2 1 (0)
cs 9600 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages09569_09600
