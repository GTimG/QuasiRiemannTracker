/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04801_04832
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04801_04832
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04801_04832
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04801_04832 Qrh.JointDetector.CurvedSourceFractions.Stages04801_04832 $number $index $kind $mode $r)
cs 4801 0 2 1 (0)
cs 4802 1 2 1 (0)
cs 4803 2 2 1 (0)
cs 4804 3 2 1 (0)
cs 4805 4 2 1 (0)
cs 4806 5 2 1 (0)
cs 4807 6 2 1 (0)
cs 4808 7 2 1 (0)
cs 4809 8 2 1 (0)
cs 4810 9 2 1 (0)
cs 4811 10 2 1 (0)
cs 4812 11 2 1 (0)
cs 4813 12 2 1 (0)
cs 4814 13 2 1 (0)
cs 4815 14 2 1 (0)
cs 4816 15 2 1 (0)
cs 4817 16 2 1 (0)
cs 4818 17 2 1 (0)
cs 4819 18 2 1 (0)
cs 4820 19 2 1 (0)
cs 4821 20 2 1 (0)
cs 4822 21 2 1 (0)
cs 4823 22 2 1 (0)
cs 4824 23 2 1 (0)
cs 4825 24 2 1 (0)
cs 4826 25 2 1 (0)
cs 4827 26 2 1 (0)
cs 4828 27 2 1 (0)
cs 4829 28 2 1 (0)
cs 4830 29 2 1 (0)
cs 4831 30 2 1 (0)
cs 4832 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04801_04832
