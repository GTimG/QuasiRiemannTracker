/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages09025_09056
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages09025_09056
namespace Qrh.JointDetector.CurvedSourceHigh.Stages09025_09056
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages09025_09056 Qrh.JointDetector.CurvedSourceFractions.Stages09025_09056 $number $index $kind $mode $r)
cs 9025 0 2 1 (0)
cs 9026 1 2 1 (0)
cs 9027 2 2 1 (0)
cs 9028 3 2 1 (0)
cs 9029 4 2 1 (0)
cs 9030 5 2 1 (0)
cs 9031 6 2 1 (0)
cs 9032 7 2 1 (0)
cs 9033 8 2 1 (0)
cs 9034 9 2 1 (0)
cs 9035 10 2 1 (0)
cs 9036 11 2 1 (0)
cs 9037 12 2 1 (0)
cs 9038 13 2 1 (0)
cs 9039 14 2 1 (0)
cs 9040 15 2 1 (0)
cs 9041 16 2 1 (0)
cs 9042 17 2 1 (0)
cs 9043 18 2 1 (0)
cs 9044 19 2 1 (0)
cs 9045 20 2 1 (0)
cs 9046 21 2 1 (0)
cs 9047 22 2 1 (0)
cs 9048 23 2 1 (0)
cs 9049 24 2 1 (0)
cs 9050 25 2 1 (0)
cs 9051 26 2 1 (0)
cs 9052 27 2 1 (0)
cs 9053 28 2 1 (0)
cs 9054 29 2 1 (0)
cs 9055 30 2 1 (0)
cs 9056 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages09025_09056
