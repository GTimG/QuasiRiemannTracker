/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04225_04256
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04225_04256
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04225_04256
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04225_04256 Qrh.JointDetector.CurvedSourceFractions.Stages04225_04256 $number $index $kind $mode $r)
cs 4225 0 2 1 (0)
cs 4226 1 2 1 (0)
cs 4227 2 2 1 (0)
cs 4228 3 2 1 (0)
cs 4229 4 2 1 (0)
cs 4230 5 2 1 (0)
cs 4231 6 2 1 (0)
cs 4232 7 2 1 (0)
cs 4233 8 2 1 (0)
cs 4234 9 2 1 (0)
cs 4235 10 2 1 (0)
cs 4236 11 2 1 (0)
cs 4237 12 2 1 (0)
cs 4238 13 2 1 (0)
cs 4239 14 2 1 (0)
cs 4240 15 2 1 (0)
cs 4241 16 2 1 (0)
cs 4242 17 2 1 (0)
cs 4243 18 2 1 (0)
cs 4244 19 2 1 (0)
cs 4245 20 2 1 (0)
cs 4246 21 2 1 (0)
cs 4247 22 2 1 (0)
cs 4248 23 2 1 (0)
cs 4249 24 2 1 (0)
cs 4250 25 2 1 (0)
cs 4251 26 2 1 (0)
cs 4252 27 2 1 (0)
cs 4253 28 2 1 (0)
cs 4254 29 2 1 (0)
cs 4255 30 2 1 (0)
cs 4256 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04225_04256
