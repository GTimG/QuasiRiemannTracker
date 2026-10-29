/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages07201_07232
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages07201_07232
namespace Qrh.JointDetector.CurvedSourceHigh.Stages07201_07232
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages07201_07232 Qrh.JointDetector.CurvedSourceFractions.Stages07201_07232 $number $index $kind $mode $r)
cs 7201 0 2 1 (0)
cs 7202 1 2 1 (0)
cs 7203 2 2 1 (0)
cs 7204 3 2 1 (0)
cs 7205 4 2 1 (0)
cs 7206 5 2 1 (0)
cs 7207 6 2 1 (0)
cs 7208 7 2 1 (0)
cs 7209 8 2 1 (0)
cs 7210 9 2 1 (0)
cs 7211 10 2 1 (0)
cs 7212 11 2 1 (0)
cs 7213 12 2 1 (0)
cs 7214 13 2 1 (0)
cs 7215 14 2 1 (0)
cs 7216 15 2 1 (0)
cs 7217 16 2 1 (0)
cs 7218 17 2 1 (0)
cs 7219 18 2 1 (0)
cs 7220 19 2 1 (0)
cs 7221 20 2 1 (0)
cs 7222 21 2 1 (0)
cs 7223 22 2 1 (0)
cs 7224 23 2 1 (0)
cs 7225 24 2 1 (0)
cs 7226 25 2 1 (0)
cs 7227 26 2 1 (0)
cs 7228 27 2 1 (0)
cs 7229 28 2 1 (0)
cs 7230 29 2 1 (0)
cs 7231 30 2 1 (0)
cs 7232 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages07201_07232
