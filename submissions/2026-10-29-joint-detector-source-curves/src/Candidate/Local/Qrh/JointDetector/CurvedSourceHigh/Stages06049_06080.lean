/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages06049_06080
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages06049_06080
namespace Qrh.JointDetector.CurvedSourceHigh.Stages06049_06080
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages06049_06080 Qrh.JointDetector.CurvedSourceFractions.Stages06049_06080 $number $index $kind $mode $r)
cs 6049 0 2 1 (0)
cs 6050 1 2 1 (0)
cs 6051 2 2 1 (0)
cs 6052 3 2 1 (0)
cs 6053 4 2 1 (0)
cs 6054 5 2 1 (0)
cs 6055 6 2 1 (0)
cs 6056 7 2 1 (0)
cs 6057 8 2 1 (0)
cs 6058 9 2 1 (0)
cs 6059 10 2 1 (0)
cs 6060 11 2 1 (0)
cs 6061 12 2 1 (0)
cs 6062 13 2 1 (0)
cs 6063 14 2 1 (0)
cs 6064 15 2 1 (0)
cs 6065 16 2 1 (0)
cs 6066 17 2 1 (0)
cs 6067 18 2 1 (0)
cs 6068 19 2 1 (0)
cs 6069 20 2 1 (0)
cs 6070 21 2 1 (0)
cs 6071 22 2 1 (0)
cs 6072 23 2 1 (0)
cs 6073 24 2 1 (0)
cs 6074 25 2 1 (0)
cs 6075 26 2 1 (0)
cs 6076 27 2 1 (0)
cs 6077 28 2 1 (0)
cs 6078 29 2 1 (0)
cs 6079 30 2 1 (0)
cs 6080 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages06049_06080
