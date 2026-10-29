/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08065_08096
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08065_08096
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08065_08096
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08065_08096 Qrh.JointDetector.CurvedSourceFractions.Stages08065_08096 $number $index $kind $mode $r)
cs 8065 0 2 1 (0)
cs 8066 1 2 1 (0)
cs 8067 2 2 1 (0)
cs 8068 3 2 1 (0)
cs 8069 4 2 1 (0)
cs 8070 5 2 1 (0)
cs 8071 6 2 1 (0)
cs 8072 7 2 1 (0)
cs 8073 8 2 1 (0)
cs 8074 9 2 1 (0)
cs 8075 10 2 1 (0)
cs 8076 11 2 1 (0)
cs 8077 12 2 1 (0)
cs 8078 13 2 1 (0)
cs 8079 14 2 1 (0)
cs 8080 15 2 1 (0)
cs 8081 16 2 1 (0)
cs 8082 17 2 1 (0)
cs 8083 18 2 1 (0)
cs 8084 19 2 1 (0)
cs 8085 20 2 1 (0)
cs 8086 21 2 1 (0)
cs 8087 22 2 1 (0)
cs 8088 23 2 1 (0)
cs 8089 24 2 1 (0)
cs 8090 25 2 1 (0)
cs 8091 26 2 1 (0)
cs 8092 27 2 1 (0)
cs 8093 28 2 1 (0)
cs 8094 29 2 1 (0)
cs 8095 30 2 1 (0)
cs 8096 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08065_08096
