/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages03969_04000
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages03969_04000
namespace Qrh.JointDetector.CurvedSourceHigh.Stages03969_04000
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages03969_04000 Qrh.JointDetector.CurvedSourceFractions.Stages03969_04000 $number $index $kind $mode $r)
cs 3969 0 2 1 (0)
cs 3970 1 2 1 (0)
cs 3971 2 2 1 (0)
cs 3972 3 2 1 (0)
cs 3973 4 2 1 (0)
cs 3974 5 2 1 (0)
cs 3975 6 2 1 (0)
cs 3976 7 2 1 (0)
cs 3977 8 2 1 (0)
cs 3978 9 2 1 (0)
cs 3979 10 2 1 (0)
cs 3980 11 2 1 (0)
cs 3981 12 2 1 (0)
cs 3982 13 2 1 (0)
cs 3983 14 2 1 (0)
cs 3984 15 2 1 (0)
cs 3985 16 2 1 (0)
cs 3986 17 2 1 (0)
cs 3987 18 2 1 (0)
cs 3988 19 2 1 (0)
cs 3989 20 2 1 (0)
cs 3990 21 2 1 (0)
cs 3991 22 2 1 (0)
cs 3992 23 2 1 (0)
cs 3993 24 2 1 (0)
cs 3994 25 2 1 (0)
cs 3995 26 2 1 (0)
cs 3996 27 2 1 (0)
cs 3997 28 2 1 (0)
cs 3998 29 2 1 (0)
cs 3999 30 2 1 (0)
cs 4000 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages03969_04000
