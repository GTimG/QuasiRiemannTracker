/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages06017_06048
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages06017_06048
namespace Qrh.JointDetector.CurvedSourceHigh.Stages06017_06048
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages06017_06048 Qrh.JointDetector.CurvedSourceFractions.Stages06017_06048 $number $index $kind $mode $r)
cs 6017 0 2 1 (0)
cs 6018 1 2 1 (0)
cs 6019 2 2 1 (0)
cs 6020 3 2 1 (0)
cs 6021 4 2 1 (0)
cs 6022 5 2 1 (0)
cs 6023 6 2 1 (0)
cs 6024 7 2 1 (0)
cs 6025 8 2 1 (0)
cs 6026 9 2 1 (0)
cs 6027 10 2 1 (0)
cs 6028 11 2 1 (0)
cs 6029 12 2 1 (0)
cs 6030 13 2 1 (0)
cs 6031 14 2 1 (0)
cs 6032 15 2 1 (0)
cs 6033 16 2 1 (0)
cs 6034 17 2 1 (0)
cs 6035 18 2 1 (0)
cs 6036 19 2 1 (0)
cs 6037 20 2 1 (0)
cs 6038 21 2 1 (0)
cs 6039 22 2 1 (0)
cs 6040 23 2 1 (0)
cs 6041 24 2 1 (0)
cs 6042 25 2 1 (0)
cs 6043 26 2 1 (0)
cs 6044 27 2 1 (0)
cs 6045 28 2 1 (0)
cs 6046 29 2 1 (0)
cs 6047 30 2 1 (0)
cs 6048 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages06017_06048
