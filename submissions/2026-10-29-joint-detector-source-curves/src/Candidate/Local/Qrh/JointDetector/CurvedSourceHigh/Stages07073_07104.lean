/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages07073_07104
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages07073_07104
namespace Qrh.JointDetector.CurvedSourceHigh.Stages07073_07104
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages07073_07104 Qrh.JointDetector.CurvedSourceFractions.Stages07073_07104 $number $index $kind $mode $r)
cs 7073 0 2 1 (0)
cs 7074 1 2 1 (0)
cs 7075 2 2 1 (0)
cs 7076 3 2 1 (0)
cs 7077 4 2 1 (0)
cs 7078 5 2 1 (0)
cs 7079 6 2 1 (0)
cs 7080 7 2 1 (0)
cs 7081 8 2 1 (0)
cs 7082 9 2 1 (0)
cs 7083 10 2 1 (0)
cs 7084 11 2 1 (0)
cs 7085 12 2 1 (0)
cs 7086 13 2 1 (0)
cs 7087 14 2 1 (0)
cs 7088 15 2 1 (0)
cs 7089 16 2 1 (0)
cs 7090 17 2 1 (0)
cs 7091 18 2 1 (0)
cs 7092 19 2 1 (0)
cs 7093 20 2 1 (0)
cs 7094 21 2 1 (0)
cs 7095 22 2 1 (0)
cs 7096 23 2 1 (0)
cs 7097 24 2 1 (0)
cs 7098 25 2 1 (0)
cs 7099 26 2 1 (0)
cs 7100 27 2 1 (0)
cs 7101 28 2 1 (0)
cs 7102 29 2 1 (0)
cs 7103 30 2 1 (0)
cs 7104 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages07073_07104
