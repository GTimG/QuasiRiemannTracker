/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages03841_03872
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages03841_03872
namespace Qrh.JointDetector.CurvedSourceHigh.Stages03841_03872
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages03841_03872 Qrh.JointDetector.CurvedSourceFractions.Stages03841_03872 $number $index $kind $mode $r)
cs 3841 0 2 1 (0)
cs 3842 1 2 1 (0)
cs 3843 2 2 1 (0)
cs 3844 3 2 1 (0)
cs 3845 4 2 1 (0)
cs 3846 5 2 1 (0)
cs 3847 6 2 1 (0)
cs 3848 7 2 1 (0)
cs 3849 8 2 1 (0)
cs 3850 9 2 1 (0)
cs 3851 10 2 1 (0)
cs 3852 11 2 1 (0)
cs 3853 12 2 1 (0)
cs 3854 13 2 1 (0)
cs 3855 14 2 1 (0)
cs 3856 15 2 1 (0)
cs 3857 16 2 1 (0)
cs 3858 17 2 1 (0)
cs 3859 18 2 1 (0)
cs 3860 19 2 1 (0)
cs 3861 20 2 1 (0)
cs 3862 21 2 1 (0)
cs 3863 22 2 1 (0)
cs 3864 23 2 1 (0)
cs 3865 24 2 1 (0)
cs 3866 25 2 1 (0)
cs 3867 26 2 1 (0)
cs 3868 27 2 1 (0)
cs 3869 28 2 1 (0)
cs 3870 29 2 1 (0)
cs 3871 30 2 1 (0)
cs 3872 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages03841_03872
