/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages05025_05056
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages05025_05056
namespace Qrh.JointDetector.CurvedSourceHigh.Stages05025_05056
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages05025_05056 Qrh.JointDetector.CurvedSourceFractions.Stages05025_05056 $number $index $kind $mode $r)
cs 5025 0 2 1 (0)
cs 5026 1 2 1 (0)
cs 5027 2 2 1 (0)
cs 5028 3 2 1 (0)
cs 5029 4 2 1 (0)
cs 5030 5 2 1 (0)
cs 5031 6 2 1 (0)
cs 5032 7 2 1 (0)
cs 5033 8 2 1 (0)
cs 5034 9 2 1 (0)
cs 5035 10 2 1 (0)
cs 5036 11 2 1 (0)
cs 5037 12 2 1 (0)
cs 5038 13 2 1 (0)
cs 5039 14 2 1 (0)
cs 5040 15 2 1 (0)
cs 5041 16 2 1 (0)
cs 5042 17 2 1 (0)
cs 5043 18 2 1 (0)
cs 5044 19 2 1 (0)
cs 5045 20 2 1 (0)
cs 5046 21 2 1 (0)
cs 5047 22 2 1 (0)
cs 5048 23 2 1 (0)
cs 5049 24 2 1 (0)
cs 5050 25 2 1 (0)
cs 5051 26 2 1 (0)
cs 5052 27 2 1 (0)
cs 5053 28 2 1 (0)
cs 5054 29 2 1 (0)
cs 5055 30 2 1 (0)
cs 5056 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages05025_05056
