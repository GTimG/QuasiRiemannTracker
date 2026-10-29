/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages16801_16832
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages16801_16832
namespace Qrh.JointDetector.CurvedSourceHigh.Stages16801_16832
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages16801_16832 Qrh.JointDetector.CurvedSourceFractions.Stages16801_16832 $number $index $kind $mode $r)
cs 16801 0 1 0 (1)
cs 16802 1 1 0 (1)
cs 16803 2 1 0 (1)
cs 16804 3 1 0 (1)
cs 16805 4 1 0 (1)
cs 16806 5 1 0 (1)
cs 16807 6 1 0 (1)
cs 16808 7 1 0 (1)
cs 16809 8 1 0 (1)
cs 16810 9 1 0 (1)
cs 16811 10 1 0 (1)
cs 16812 11 1 0 (1)
cs 16813 12 1 0 (1)
cs 16814 13 1 0 (1)
cs 16815 14 1 0 (1)
cs 16816 15 1 0 (1)
cs 16817 16 1 0 (1)
cs 16818 17 1 0 (1)
cs 16819 18 1 0 (1)
cs 16820 19 1 0 (1)
cs 16821 20 1 0 (1)
cs 16822 21 1 0 (1)
cs 16823 22 1 0 (1)
cs 16824 23 1 0 (1)
cs 16825 24 1 0 (1)
cs 16826 25 1 0 (1)
cs 16827 26 1 0 (1)
cs 16828 27 1 0 (1)
cs 16829 28 1 0 (1)
cs 16830 29 1 0 (1)
cs 16831 30 1 0 (1)
cs 16832 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages16801_16832
