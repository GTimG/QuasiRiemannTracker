/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages15201_15232
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages15201_15232
namespace Qrh.JointDetector.CurvedSourceHigh.Stages15201_15232
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages15201_15232 Qrh.JointDetector.CurvedSourceFractions.Stages15201_15232 $number $index $kind $mode $r)
cs 15201 0 1 0 (1)
cs 15202 1 1 0 (1)
cs 15203 2 1 0 (1)
cs 15204 3 1 0 (1)
cs 15205 4 1 0 (1)
cs 15206 5 1 0 (1)
cs 15207 6 1 0 (1)
cs 15208 7 1 0 (1)
cs 15209 8 1 0 (1)
cs 15210 9 1 0 (1)
cs 15211 10 1 0 (1)
cs 15212 11 1 0 (1)
cs 15213 12 1 0 (1)
cs 15214 13 1 0 (1)
cs 15215 14 1 0 (1)
cs 15216 15 1 0 (1)
cs 15217 16 1 0 (1)
cs 15218 17 1 0 (1)
cs 15219 18 1 0 (1)
cs 15220 19 1 0 (1)
cs 15221 20 1 0 (1)
cs 15222 21 1 0 (1)
cs 15223 22 1 0 (1)
cs 15224 23 1 0 (1)
cs 15225 24 1 0 (1)
cs 15226 25 1 0 (1)
cs 15227 26 1 0 (1)
cs 15228 27 1 0 (1)
cs 15229 28 1 0 (1)
cs 15230 29 1 0 (1)
cs 15231 30 1 0 (1)
cs 15232 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages15201_15232
