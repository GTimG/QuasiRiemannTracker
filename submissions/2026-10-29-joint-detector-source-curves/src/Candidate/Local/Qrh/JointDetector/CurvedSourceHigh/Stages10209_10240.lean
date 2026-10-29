/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages10209_10240
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages10209_10240
namespace Qrh.JointDetector.CurvedSourceHigh.Stages10209_10240
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages10209_10240 Qrh.JointDetector.CurvedSourceFractions.Stages10209_10240 $number $index $kind $mode $r)
cs 10209 0 2 1 (0)
cs 10210 1 2 1 (0)
cs 10211 2 2 1 (0)
cs 10212 3 2 1 (0)
cs 10213 4 2 1 (0)
cs 10214 5 2 1 (0)
cs 10215 6 2 1 (0)
cs 10216 7 2 1 (0)
cs 10217 8 2 1 (0)
cs 10218 9 2 1 (0)
cs 10219 10 2 1 (0)
cs 10220 11 2 1 (0)
cs 10221 12 2 1 (0)
cs 10222 13 2 1 (0)
cs 10223 14 2 1 (0)
cs 10224 15 2 1 (0)
cs 10225 16 2 1 (0)
cs 10226 17 2 1 (0)
cs 10227 18 2 1 (0)
cs 10228 19 2 1 (0)
cs 10229 20 2 1 (0)
cs 10230 21 2 1 (0)
cs 10231 22 2 1 (0)
cs 10232 23 2 1 (0)
cs 10233 24 2 1 (0)
cs 10234 25 2 1 (0)
cs 10235 26 2 1 (0)
cs 10236 27 2 1 (0)
cs 10237 28 2 1 (0)
cs 10238 29 2 1 (0)
cs 10239 30 2 1 (0)
cs 10240 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages10209_10240
