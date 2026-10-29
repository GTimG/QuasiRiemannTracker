/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages03873_03904
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages03873_03904
namespace Qrh.JointDetector.CurvedSourceHigh.Stages03873_03904
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages03873_03904 Qrh.JointDetector.CurvedSourceFractions.Stages03873_03904 $number $index $kind $mode $r)
cs 3873 0 2 1 (0)
cs 3874 1 2 1 (0)
cs 3875 2 2 1 (0)
cs 3876 3 2 1 (0)
cs 3877 4 2 1 (0)
cs 3878 5 2 1 (0)
cs 3879 6 2 1 (0)
cs 3880 7 2 1 (0)
cs 3881 8 2 1 (0)
cs 3882 9 2 1 (0)
cs 3883 10 2 1 (0)
cs 3884 11 2 1 (0)
cs 3885 12 2 1 (0)
cs 3886 13 2 1 (0)
cs 3887 14 2 1 (0)
cs 3888 15 2 1 (0)
cs 3889 16 2 1 (0)
cs 3890 17 2 1 (0)
cs 3891 18 2 1 (0)
cs 3892 19 2 1 (0)
cs 3893 20 2 1 (0)
cs 3894 21 2 1 (0)
cs 3895 22 2 1 (0)
cs 3896 23 2 1 (0)
cs 3897 24 2 1 (0)
cs 3898 25 2 1 (0)
cs 3899 26 2 1 (0)
cs 3900 27 2 1 (0)
cs 3901 28 2 1 (0)
cs 3902 29 2 1 (0)
cs 3903 30 2 1 (0)
cs 3904 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages03873_03904
