/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages12769_12800
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages12769_12800
namespace Qrh.JointDetector.CurvedSourceHigh.Stages12769_12800
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages12769_12800 Qrh.JointDetector.CurvedSourceFractions.Stages12769_12800 $number $index $kind $mode $r)
cs 12769 0 2 1 (0)
cs 12770 1 2 1 (0)
cs 12771 2 2 1 (0)
cs 12772 3 2 1 (0)
cs 12773 4 2 1 (0)
cs 12774 5 2 1 (0)
cs 12775 6 2 1 (0)
cs 12776 7 2 1 (0)
cs 12777 8 2 1 (0)
cs 12778 9 2 1 (0)
cs 12779 10 2 1 (0)
cs 12780 11 2 1 (0)
cs 12781 12 2 1 (0)
cs 12782 13 2 1 (0)
cs 12783 14 2 1 (0)
cs 12784 15 2 1 (0)
cs 12785 16 2 1 (0)
cs 12786 17 2 1 (0)
cs 12787 18 2 1 (0)
cs 12788 19 1 0 (1)
cs 12789 20 1 0 (1)
cs 12790 21 1 0 (1)
cs 12791 22 1 0 (1)
cs 12792 23 1 0 (1)
cs 12793 24 1 0 (1)
cs 12794 25 1 0 (1)
cs 12795 26 1 0 (1)
cs 12796 27 1 0 (1)
cs 12797 28 1 0 (1)
cs 12798 29 1 0 (1)
cs 12799 30 1 0 (1)
cs 12800 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages12769_12800
