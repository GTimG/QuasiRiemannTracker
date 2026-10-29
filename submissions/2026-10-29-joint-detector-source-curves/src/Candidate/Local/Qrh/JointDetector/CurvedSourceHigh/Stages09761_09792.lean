/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages09761_09792
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages09761_09792
namespace Qrh.JointDetector.CurvedSourceHigh.Stages09761_09792
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages09761_09792 Qrh.JointDetector.CurvedSourceFractions.Stages09761_09792 $number $index $kind $mode $r)
cs 9761 0 2 1 (0)
cs 9762 1 2 1 (0)
cs 9763 2 2 1 (0)
cs 9764 3 2 1 (0)
cs 9765 4 2 1 (0)
cs 9766 5 2 1 (0)
cs 9767 6 2 1 (0)
cs 9768 7 2 1 (0)
cs 9769 8 2 1 (0)
cs 9770 9 2 1 (0)
cs 9771 10 2 1 (0)
cs 9772 11 2 1 (0)
cs 9773 12 2 1 (0)
cs 9774 13 2 1 (0)
cs 9775 14 2 1 (0)
cs 9776 15 2 1 (0)
cs 9777 16 2 1 (0)
cs 9778 17 2 1 (0)
cs 9779 18 2 1 (0)
cs 9780 19 2 1 (0)
cs 9781 20 2 1 (0)
cs 9782 21 2 1 (0)
cs 9783 22 2 1 (0)
cs 9784 23 2 1 (0)
cs 9785 24 2 1 (0)
cs 9786 25 2 1 (0)
cs 9787 26 2 1 (0)
cs 9788 27 2 1 (0)
cs 9789 28 2 1 (0)
cs 9790 29 2 1 (0)
cs 9791 30 2 1 (0)
cs 9792 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages09761_09792
