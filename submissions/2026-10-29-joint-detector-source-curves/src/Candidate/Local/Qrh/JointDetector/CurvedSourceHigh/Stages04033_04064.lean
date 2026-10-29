/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04033_04064
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04033_04064
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04033_04064
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04033_04064 Qrh.JointDetector.CurvedSourceFractions.Stages04033_04064 $number $index $kind $mode $r)
cs 4033 0 2 1 (0)
cs 4034 1 2 1 (0)
cs 4035 2 2 1 (0)
cs 4036 3 2 1 (0)
cs 4037 4 2 1 (0)
cs 4038 5 2 1 (0)
cs 4039 6 2 1 (0)
cs 4040 7 2 1 (0)
cs 4041 8 2 1 (0)
cs 4042 9 2 1 (0)
cs 4043 10 2 1 (0)
cs 4044 11 2 1 (0)
cs 4045 12 2 1 (0)
cs 4046 13 2 1 (0)
cs 4047 14 2 1 (0)
cs 4048 15 2 1 (0)
cs 4049 16 2 1 (0)
cs 4050 17 2 1 (0)
cs 4051 18 2 1 (0)
cs 4052 19 2 1 (0)
cs 4053 20 2 1 (0)
cs 4054 21 2 1 (0)
cs 4055 22 2 1 (0)
cs 4056 23 2 1 (0)
cs 4057 24 2 1 (0)
cs 4058 25 2 1 (0)
cs 4059 26 2 1 (0)
cs 4060 27 2 1 (0)
cs 4061 28 2 1 (0)
cs 4062 29 2 1 (0)
cs 4063 30 2 1 (0)
cs 4064 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04033_04064
