/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages16065_16096
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages16065_16096
namespace Qrh.JointDetector.CurvedSourceHigh.Stages16065_16096
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages16065_16096 Qrh.JointDetector.CurvedSourceFractions.Stages16065_16096 $number $index $kind $mode $r)
cs 16065 0 1 0 (1)
cs 16066 1 1 0 (1)
cs 16067 2 1 0 (1)
cs 16068 3 1 0 (1)
cs 16069 4 1 0 (1)
cs 16070 5 1 0 (1)
cs 16071 6 1 0 (1)
cs 16072 7 1 0 (1)
cs 16073 8 1 0 (1)
cs 16074 9 1 0 (1)
cs 16075 10 1 0 (1)
cs 16076 11 1 0 (1)
cs 16077 12 1 0 (1)
cs 16078 13 1 0 (1)
cs 16079 14 1 0 (1)
cs 16080 15 1 0 (1)
cs 16081 16 1 0 (1)
cs 16082 17 1 0 (1)
cs 16083 18 1 0 (1)
cs 16084 19 1 0 (1)
cs 16085 20 1 0 (1)
cs 16086 21 1 0 (1)
cs 16087 22 1 0 (1)
cs 16088 23 1 0 (1)
cs 16089 24 1 0 (1)
cs 16090 25 1 0 (1)
cs 16091 26 1 0 (1)
cs 16092 27 1 0 (1)
cs 16093 28 1 0 (1)
cs 16094 29 1 0 (1)
cs 16095 30 1 0 (1)
cs 16096 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages16065_16096
