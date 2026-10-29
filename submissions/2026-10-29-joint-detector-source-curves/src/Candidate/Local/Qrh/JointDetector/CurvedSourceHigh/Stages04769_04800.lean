/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04769_04800
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04769_04800
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04769_04800
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04769_04800 Qrh.JointDetector.CurvedSourceFractions.Stages04769_04800 $number $index $kind $mode $r)
cs 4769 0 2 1 (0)
cs 4770 1 2 1 (0)
cs 4771 2 2 1 (0)
cs 4772 3 2 1 (0)
cs 4773 4 2 1 (0)
cs 4774 5 2 1 (0)
cs 4775 6 2 1 (0)
cs 4776 7 2 1 (0)
cs 4777 8 2 1 (0)
cs 4778 9 2 1 (0)
cs 4779 10 2 1 (0)
cs 4780 11 2 1 (0)
cs 4781 12 2 1 (0)
cs 4782 13 2 1 (0)
cs 4783 14 2 1 (0)
cs 4784 15 2 1 (0)
cs 4785 16 2 1 (0)
cs 4786 17 2 1 (0)
cs 4787 18 2 1 (0)
cs 4788 19 2 1 (0)
cs 4789 20 2 1 (0)
cs 4790 21 2 1 (0)
cs 4791 22 2 1 (0)
cs 4792 23 2 1 (0)
cs 4793 24 2 1 (0)
cs 4794 25 2 1 (0)
cs 4795 26 2 1 (0)
cs 4796 27 2 1 (0)
cs 4797 28 2 1 (0)
cs 4798 29 2 1 (0)
cs 4799 30 2 1 (0)
cs 4800 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04769_04800
