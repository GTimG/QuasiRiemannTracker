/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08193_08224
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08193_08224
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08193_08224
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08193_08224 Qrh.JointDetector.CurvedSourceFractions.Stages08193_08224 $number $index $kind $mode $r)
cs 8193 0 2 1 (0)
cs 8194 1 2 1 (0)
cs 8195 2 2 1 (0)
cs 8196 3 2 1 (0)
cs 8197 4 2 1 (0)
cs 8198 5 2 1 (0)
cs 8199 6 2 1 (0)
cs 8200 7 2 1 (0)
cs 8201 8 2 1 (0)
cs 8202 9 2 1 (0)
cs 8203 10 2 1 (0)
cs 8204 11 2 1 (0)
cs 8205 12 2 1 (0)
cs 8206 13 2 1 (0)
cs 8207 14 2 1 (0)
cs 8208 15 2 1 (0)
cs 8209 16 2 1 (0)
cs 8210 17 2 1 (0)
cs 8211 18 2 1 (0)
cs 8212 19 2 1 (0)
cs 8213 20 2 1 (0)
cs 8214 21 2 1 (0)
cs 8215 22 2 1 (0)
cs 8216 23 2 1 (0)
cs 8217 24 2 1 (0)
cs 8218 25 2 1 (0)
cs 8219 26 2 1 (0)
cs 8220 27 2 1 (0)
cs 8221 28 2 1 (0)
cs 8222 29 2 1 (0)
cs 8223 30 2 1 (0)
cs 8224 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08193_08224
