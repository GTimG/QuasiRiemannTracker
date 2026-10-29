/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages16225_16256
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages16225_16256
namespace Qrh.JointDetector.CurvedSourceHigh.Stages16225_16256
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages16225_16256 Qrh.JointDetector.CurvedSourceFractions.Stages16225_16256 $number $index $kind $mode $r)
cs 16225 0 1 0 (1)
cs 16226 1 1 0 (1)
cs 16227 2 1 0 (1)
cs 16228 3 1 0 (1)
cs 16229 4 1 0 (1)
cs 16230 5 1 0 (1)
cs 16231 6 1 0 (1)
cs 16232 7 1 0 (1)
cs 16233 8 1 0 (1)
cs 16234 9 1 0 (1)
cs 16235 10 1 0 (1)
cs 16236 11 1 0 (1)
cs 16237 12 1 0 (1)
cs 16238 13 1 0 (1)
cs 16239 14 1 0 (1)
cs 16240 15 1 0 (1)
cs 16241 16 1 0 (1)
cs 16242 17 1 0 (1)
cs 16243 18 1 0 (1)
cs 16244 19 1 0 (1)
cs 16245 20 1 0 (1)
cs 16246 21 1 0 (1)
cs 16247 22 1 0 (1)
cs 16248 23 1 0 (1)
cs 16249 24 1 0 (1)
cs 16250 25 1 0 (1)
cs 16251 26 1 0 (1)
cs 16252 27 1 0 (1)
cs 16253 28 1 0 (1)
cs 16254 29 1 0 (1)
cs 16255 30 1 0 (1)
cs 16256 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages16225_16256
