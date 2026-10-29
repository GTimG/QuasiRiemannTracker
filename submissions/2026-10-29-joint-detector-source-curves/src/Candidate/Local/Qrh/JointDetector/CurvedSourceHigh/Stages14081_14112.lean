/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages14081_14112
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages14081_14112
namespace Qrh.JointDetector.CurvedSourceHigh.Stages14081_14112
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages14081_14112 Qrh.JointDetector.CurvedSourceFractions.Stages14081_14112 $number $index $kind $mode $r)
cs 14081 0 1 0 (1)
cs 14082 1 1 0 (1)
cs 14083 2 1 0 (1)
cs 14084 3 1 0 (1)
cs 14085 4 1 0 (1)
cs 14086 5 1 0 (1)
cs 14087 6 1 0 (1)
cs 14088 7 1 0 (1)
cs 14089 8 1 0 (1)
cs 14090 9 1 0 (1)
cs 14091 10 1 0 (1)
cs 14092 11 1 0 (1)
cs 14093 12 1 0 (1)
cs 14094 13 1 0 (1)
cs 14095 14 1 0 (1)
cs 14096 15 1 0 (1)
cs 14097 16 1 0 (1)
cs 14098 17 1 0 (1)
cs 14099 18 1 0 (1)
cs 14100 19 1 0 (1)
cs 14101 20 1 0 (1)
cs 14102 21 1 0 (1)
cs 14103 22 1 0 (1)
cs 14104 23 1 0 (1)
cs 14105 24 1 0 (1)
cs 14106 25 1 0 (1)
cs 14107 26 1 0 (1)
cs 14108 27 1 0 (1)
cs 14109 28 1 0 (1)
cs 14110 29 1 0 (1)
cs 14111 30 1 0 (1)
cs 14112 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages14081_14112
