/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages09089_09120
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages09089_09120
namespace Qrh.JointDetector.CurvedSourceHigh.Stages09089_09120
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages09089_09120 Qrh.JointDetector.CurvedSourceFractions.Stages09089_09120 $number $index $kind $mode $r)
cs 9089 0 2 1 (0)
cs 9090 1 2 1 (0)
cs 9091 2 2 1 (0)
cs 9092 3 2 1 (0)
cs 9093 4 2 1 (0)
cs 9094 5 2 1 (0)
cs 9095 6 2 1 (0)
cs 9096 7 2 1 (0)
cs 9097 8 2 1 (0)
cs 9098 9 2 1 (0)
cs 9099 10 2 1 (0)
cs 9100 11 2 1 (0)
cs 9101 12 2 1 (0)
cs 9102 13 2 1 (0)
cs 9103 14 2 1 (0)
cs 9104 15 2 1 (0)
cs 9105 16 2 1 (0)
cs 9106 17 2 1 (0)
cs 9107 18 2 1 (0)
cs 9108 19 2 1 (0)
cs 9109 20 2 1 (0)
cs 9110 21 2 1 (0)
cs 9111 22 2 1 (0)
cs 9112 23 2 1 (0)
cs 9113 24 2 1 (0)
cs 9114 25 2 1 (0)
cs 9115 26 2 1 (0)
cs 9116 27 2 1 (0)
cs 9117 28 2 1 (0)
cs 9118 29 2 1 (0)
cs 9119 30 2 1 (0)
cs 9120 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages09089_09120
