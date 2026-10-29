/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages06081_06112
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages06081_06112
namespace Qrh.JointDetector.CurvedSourceHigh.Stages06081_06112
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages06081_06112 Qrh.JointDetector.CurvedSourceFractions.Stages06081_06112 $number $index $kind $mode $r)
cs 6081 0 2 1 (0)
cs 6082 1 2 1 (0)
cs 6083 2 2 1 (0)
cs 6084 3 2 1 (0)
cs 6085 4 2 1 (0)
cs 6086 5 2 1 (0)
cs 6087 6 2 1 (0)
cs 6088 7 2 1 (0)
cs 6089 8 2 1 (0)
cs 6090 9 2 1 (0)
cs 6091 10 2 1 (0)
cs 6092 11 2 1 (0)
cs 6093 12 2 1 (0)
cs 6094 13 2 1 (0)
cs 6095 14 2 1 (0)
cs 6096 15 2 1 (0)
cs 6097 16 2 1 (0)
cs 6098 17 2 1 (0)
cs 6099 18 2 1 (0)
cs 6100 19 2 1 (0)
cs 6101 20 2 1 (0)
cs 6102 21 2 1 (0)
cs 6103 22 2 1 (0)
cs 6104 23 2 1 (0)
cs 6105 24 2 1 (0)
cs 6106 25 2 1 (0)
cs 6107 26 2 1 (0)
cs 6108 27 2 1 (0)
cs 6109 28 2 1 (0)
cs 6110 29 2 1 (0)
cs 6111 30 2 1 (0)
cs 6112 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages06081_06112
