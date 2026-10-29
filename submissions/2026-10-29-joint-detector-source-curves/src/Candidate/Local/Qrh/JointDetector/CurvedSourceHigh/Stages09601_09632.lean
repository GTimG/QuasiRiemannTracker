/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages09601_09632
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages09601_09632
namespace Qrh.JointDetector.CurvedSourceHigh.Stages09601_09632
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages09601_09632 Qrh.JointDetector.CurvedSourceFractions.Stages09601_09632 $number $index $kind $mode $r)
cs 9601 0 2 1 (0)
cs 9602 1 2 1 (0)
cs 9603 2 2 1 (0)
cs 9604 3 2 1 (0)
cs 9605 4 2 1 (0)
cs 9606 5 2 1 (0)
cs 9607 6 2 1 (0)
cs 9608 7 2 1 (0)
cs 9609 8 2 1 (0)
cs 9610 9 2 1 (0)
cs 9611 10 2 1 (0)
cs 9612 11 2 1 (0)
cs 9613 12 2 1 (0)
cs 9614 13 2 1 (0)
cs 9615 14 2 1 (0)
cs 9616 15 2 1 (0)
cs 9617 16 2 1 (0)
cs 9618 17 2 1 (0)
cs 9619 18 2 1 (0)
cs 9620 19 2 1 (0)
cs 9621 20 2 1 (0)
cs 9622 21 2 1 (0)
cs 9623 22 2 1 (0)
cs 9624 23 2 1 (0)
cs 9625 24 2 1 (0)
cs 9626 25 2 1 (0)
cs 9627 26 2 1 (0)
cs 9628 27 2 1 (0)
cs 9629 28 2 1 (0)
cs 9630 29 2 1 (0)
cs 9631 30 2 1 (0)
cs 9632 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages09601_09632
