/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages07041_07072
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages07041_07072
namespace Qrh.JointDetector.CurvedSourceHigh.Stages07041_07072
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages07041_07072 Qrh.JointDetector.CurvedSourceFractions.Stages07041_07072 $number $index $kind $mode $r)
cs 7041 0 2 1 (0)
cs 7042 1 2 1 (0)
cs 7043 2 2 1 (0)
cs 7044 3 2 1 (0)
cs 7045 4 2 1 (0)
cs 7046 5 2 1 (0)
cs 7047 6 2 1 (0)
cs 7048 7 2 1 (0)
cs 7049 8 2 1 (0)
cs 7050 9 2 1 (0)
cs 7051 10 2 1 (0)
cs 7052 11 2 1 (0)
cs 7053 12 2 1 (0)
cs 7054 13 2 1 (0)
cs 7055 14 2 1 (0)
cs 7056 15 2 1 (0)
cs 7057 16 2 1 (0)
cs 7058 17 2 1 (0)
cs 7059 18 2 1 (0)
cs 7060 19 2 1 (0)
cs 7061 20 2 1 (0)
cs 7062 21 2 1 (0)
cs 7063 22 2 1 (0)
cs 7064 23 2 1 (0)
cs 7065 24 2 1 (0)
cs 7066 25 2 1 (0)
cs 7067 26 2 1 (0)
cs 7068 27 2 1 (0)
cs 7069 28 2 1 (0)
cs 7070 29 2 1 (0)
cs 7071 30 2 1 (0)
cs 7072 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages07041_07072
