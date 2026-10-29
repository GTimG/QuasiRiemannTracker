/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08769_08800
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08769_08800
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08769_08800
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08769_08800 Qrh.JointDetector.CurvedSourceFractions.Stages08769_08800 $number $index $kind $mode $r)
cs 8769 0 2 1 (0)
cs 8770 1 2 1 (0)
cs 8771 2 2 1 (0)
cs 8772 3 2 1 (0)
cs 8773 4 2 1 (0)
cs 8774 5 2 1 (0)
cs 8775 6 2 1 (0)
cs 8776 7 2 1 (0)
cs 8777 8 2 1 (0)
cs 8778 9 2 1 (0)
cs 8779 10 2 1 (0)
cs 8780 11 2 1 (0)
cs 8781 12 2 1 (0)
cs 8782 13 2 1 (0)
cs 8783 14 2 1 (0)
cs 8784 15 2 1 (0)
cs 8785 16 2 1 (0)
cs 8786 17 2 1 (0)
cs 8787 18 2 1 (0)
cs 8788 19 2 1 (0)
cs 8789 20 2 1 (0)
cs 8790 21 2 1 (0)
cs 8791 22 2 1 (0)
cs 8792 23 2 1 (0)
cs 8793 24 2 1 (0)
cs 8794 25 2 1 (0)
cs 8795 26 2 1 (0)
cs 8796 27 2 1 (0)
cs 8797 28 2 1 (0)
cs 8798 29 2 1 (0)
cs 8799 30 2 1 (0)
cs 8800 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08769_08800
