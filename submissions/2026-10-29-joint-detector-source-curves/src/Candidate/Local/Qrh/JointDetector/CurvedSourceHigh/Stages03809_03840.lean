/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages03809_03840
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages03809_03840
namespace Qrh.JointDetector.CurvedSourceHigh.Stages03809_03840
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages03809_03840 Qrh.JointDetector.CurvedSourceFractions.Stages03809_03840 $number $index $kind $mode $r)
cs 3809 0 2 1 (0)
cs 3810 1 2 1 (0)
cs 3811 2 2 1 (0)
cs 3812 3 2 1 (0)
cs 3813 4 2 1 (0)
cs 3814 5 2 1 (0)
cs 3815 6 2 1 (0)
cs 3816 7 2 1 (0)
cs 3817 8 2 1 (0)
cs 3818 9 2 1 (0)
cs 3819 10 2 1 (0)
cs 3820 11 2 1 (0)
cs 3821 12 2 1 (0)
cs 3822 13 2 1 (0)
cs 3823 14 2 1 (0)
cs 3824 15 2 1 (0)
cs 3825 16 2 1 (0)
cs 3826 17 2 1 (0)
cs 3827 18 2 1 (0)
cs 3828 19 2 1 (0)
cs 3829 20 2 1 (0)
cs 3830 21 2 1 (0)
cs 3831 22 2 1 (0)
cs 3832 23 2 1 (0)
cs 3833 24 2 1 (0)
cs 3834 25 2 1 (0)
cs 3835 26 2 1 (0)
cs 3836 27 2 1 (0)
cs 3837 28 2 1 (0)
cs 3838 29 2 1 (0)
cs 3839 30 2 1 (0)
cs 3840 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages03809_03840
