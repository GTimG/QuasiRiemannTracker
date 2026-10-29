/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04641_04672
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04641_04672
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04641_04672
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04641_04672 Qrh.JointDetector.CurvedSourceFractions.Stages04641_04672 $number $index $kind $mode $r)
cs 4641 0 2 1 (0)
cs 4642 1 2 1 (0)
cs 4643 2 2 1 (0)
cs 4644 3 2 1 (0)
cs 4645 4 2 1 (0)
cs 4646 5 2 1 (0)
cs 4647 6 2 1 (0)
cs 4648 7 2 1 (0)
cs 4649 8 2 1 (0)
cs 4650 9 2 1 (0)
cs 4651 10 2 1 (0)
cs 4652 11 2 1 (0)
cs 4653 12 2 1 (0)
cs 4654 13 2 1 (0)
cs 4655 14 2 1 (0)
cs 4656 15 2 1 (0)
cs 4657 16 2 1 (0)
cs 4658 17 2 1 (0)
cs 4659 18 2 1 (0)
cs 4660 19 2 1 (0)
cs 4661 20 2 1 (0)
cs 4662 21 2 1 (0)
cs 4663 22 2 1 (0)
cs 4664 23 2 1 (0)
cs 4665 24 2 1 (0)
cs 4666 25 2 1 (0)
cs 4667 26 2 1 (0)
cs 4668 27 2 1 (0)
cs 4669 28 2 1 (0)
cs 4670 29 2 1 (0)
cs 4671 30 2 1 (0)
cs 4672 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04641_04672
