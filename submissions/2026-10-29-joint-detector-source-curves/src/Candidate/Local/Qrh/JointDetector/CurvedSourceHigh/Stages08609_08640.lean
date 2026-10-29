/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08609_08640
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08609_08640
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08609_08640
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08609_08640 Qrh.JointDetector.CurvedSourceFractions.Stages08609_08640 $number $index $kind $mode $r)
cs 8609 0 2 1 (0)
cs 8610 1 2 1 (0)
cs 8611 2 2 1 (0)
cs 8612 3 2 1 (0)
cs 8613 4 2 1 (0)
cs 8614 5 2 1 (0)
cs 8615 6 2 1 (0)
cs 8616 7 2 1 (0)
cs 8617 8 2 1 (0)
cs 8618 9 2 1 (0)
cs 8619 10 2 1 (0)
cs 8620 11 2 1 (0)
cs 8621 12 2 1 (0)
cs 8622 13 2 1 (0)
cs 8623 14 2 1 (0)
cs 8624 15 2 1 (0)
cs 8625 16 2 1 (0)
cs 8626 17 2 1 (0)
cs 8627 18 2 1 (0)
cs 8628 19 2 1 (0)
cs 8629 20 2 1 (0)
cs 8630 21 2 1 (0)
cs 8631 22 2 1 (0)
cs 8632 23 2 1 (0)
cs 8633 24 2 1 (0)
cs 8634 25 2 1 (0)
cs 8635 26 2 1 (0)
cs 8636 27 2 1 (0)
cs 8637 28 2 1 (0)
cs 8638 29 2 1 (0)
cs 8639 30 2 1 (0)
cs 8640 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08609_08640
