/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages06209_06240
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages06209_06240
namespace Qrh.JointDetector.CurvedSourceHigh.Stages06209_06240
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages06209_06240 Qrh.JointDetector.CurvedSourceFractions.Stages06209_06240 $number $index $kind $mode $r)
cs 6209 0 2 1 (0)
cs 6210 1 2 1 (0)
cs 6211 2 2 1 (0)
cs 6212 3 2 1 (0)
cs 6213 4 2 1 (0)
cs 6214 5 2 1 (0)
cs 6215 6 2 1 (0)
cs 6216 7 2 1 (0)
cs 6217 8 2 1 (0)
cs 6218 9 2 1 (0)
cs 6219 10 2 1 (0)
cs 6220 11 2 1 (0)
cs 6221 12 2 1 (0)
cs 6222 13 2 1 (0)
cs 6223 14 2 1 (0)
cs 6224 15 2 1 (0)
cs 6225 16 2 1 (0)
cs 6226 17 2 1 (0)
cs 6227 18 2 1 (0)
cs 6228 19 2 1 (0)
cs 6229 20 2 1 (0)
cs 6230 21 2 1 (0)
cs 6231 22 2 1 (0)
cs 6232 23 2 1 (0)
cs 6233 24 2 1 (0)
cs 6234 25 2 1 (0)
cs 6235 26 2 1 (0)
cs 6236 27 2 1 (0)
cs 6237 28 2 1 (0)
cs 6238 29 2 1 (0)
cs 6239 30 2 1 (0)
cs 6240 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages06209_06240
