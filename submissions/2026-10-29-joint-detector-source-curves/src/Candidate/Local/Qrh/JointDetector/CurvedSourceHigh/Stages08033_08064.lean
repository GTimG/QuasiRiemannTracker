/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08033_08064
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08033_08064
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08033_08064
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08033_08064 Qrh.JointDetector.CurvedSourceFractions.Stages08033_08064 $number $index $kind $mode $r)
cs 8033 0 2 1 (0)
cs 8034 1 2 1 (0)
cs 8035 2 2 1 (0)
cs 8036 3 2 1 (0)
cs 8037 4 2 1 (0)
cs 8038 5 2 1 (0)
cs 8039 6 2 1 (0)
cs 8040 7 2 1 (0)
cs 8041 8 2 1 (0)
cs 8042 9 2 1 (0)
cs 8043 10 2 1 (0)
cs 8044 11 2 1 (0)
cs 8045 12 2 1 (0)
cs 8046 13 2 1 (0)
cs 8047 14 2 1 (0)
cs 8048 15 2 1 (0)
cs 8049 16 2 1 (0)
cs 8050 17 2 1 (0)
cs 8051 18 2 1 (0)
cs 8052 19 2 1 (0)
cs 8053 20 2 1 (0)
cs 8054 21 2 1 (0)
cs 8055 22 2 1 (0)
cs 8056 23 2 1 (0)
cs 8057 24 2 1 (0)
cs 8058 25 2 1 (0)
cs 8059 26 2 1 (0)
cs 8060 27 2 1 (0)
cs 8061 28 2 1 (0)
cs 8062 29 2 1 (0)
cs 8063 30 2 1 (0)
cs 8064 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08033_08064
