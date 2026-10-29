/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08225_08256
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08225_08256
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08225_08256
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08225_08256 Qrh.JointDetector.CurvedSourceFractions.Stages08225_08256 $number $index $kind $mode $r)
cs 8225 0 2 1 (0)
cs 8226 1 2 1 (0)
cs 8227 2 2 1 (0)
cs 8228 3 2 1 (0)
cs 8229 4 2 1 (0)
cs 8230 5 2 1 (0)
cs 8231 6 2 1 (0)
cs 8232 7 2 1 (0)
cs 8233 8 2 1 (0)
cs 8234 9 2 1 (0)
cs 8235 10 2 1 (0)
cs 8236 11 2 1 (0)
cs 8237 12 2 1 (0)
cs 8238 13 2 1 (0)
cs 8239 14 2 1 (0)
cs 8240 15 2 1 (0)
cs 8241 16 2 1 (0)
cs 8242 17 2 1 (0)
cs 8243 18 2 1 (0)
cs 8244 19 2 1 (0)
cs 8245 20 2 1 (0)
cs 8246 21 2 1 (0)
cs 8247 22 2 1 (0)
cs 8248 23 2 1 (0)
cs 8249 24 2 1 (0)
cs 8250 25 2 1 (0)
cs 8251 26 2 1 (0)
cs 8252 27 2 1 (0)
cs 8253 28 2 1 (0)
cs 8254 29 2 1 (0)
cs 8255 30 2 1 (0)
cs 8256 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08225_08256
