/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages15041_15072
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages15041_15072
namespace Qrh.JointDetector.CurvedSourceHigh.Stages15041_15072
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages15041_15072 Qrh.JointDetector.CurvedSourceFractions.Stages15041_15072 $number $index $kind $mode $r)
cs 15041 0 1 0 (1)
cs 15042 1 1 0 (1)
cs 15043 2 1 0 (1)
cs 15044 3 1 0 (1)
cs 15045 4 1 0 (1)
cs 15046 5 1 0 (1)
cs 15047 6 1 0 (1)
cs 15048 7 1 0 (1)
cs 15049 8 1 0 (1)
cs 15050 9 1 0 (1)
cs 15051 10 1 0 (1)
cs 15052 11 1 0 (1)
cs 15053 12 1 0 (1)
cs 15054 13 1 0 (1)
cs 15055 14 1 0 (1)
cs 15056 15 1 0 (1)
cs 15057 16 1 0 (1)
cs 15058 17 1 0 (1)
cs 15059 18 1 0 (1)
cs 15060 19 1 0 (1)
cs 15061 20 1 0 (1)
cs 15062 21 1 0 (1)
cs 15063 22 1 0 (1)
cs 15064 23 1 0 (1)
cs 15065 24 1 0 (1)
cs 15066 25 1 0 (1)
cs 15067 26 1 0 (1)
cs 15068 27 1 0 (1)
cs 15069 28 1 0 (1)
cs 15070 29 1 0 (1)
cs 15071 30 1 0 (1)
cs 15072 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages15041_15072
