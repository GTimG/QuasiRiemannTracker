/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08481_08512
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08481_08512
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08481_08512
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08481_08512 Qrh.JointDetector.CurvedSourceFractions.Stages08481_08512 $number $index $kind $mode $r)
cs 8481 0 2 1 (0)
cs 8482 1 2 1 (0)
cs 8483 2 2 1 (0)
cs 8484 3 2 1 (0)
cs 8485 4 2 1 (0)
cs 8486 5 2 1 (0)
cs 8487 6 2 1 (0)
cs 8488 7 2 1 (0)
cs 8489 8 2 1 (0)
cs 8490 9 2 1 (0)
cs 8491 10 2 1 (0)
cs 8492 11 2 1 (0)
cs 8493 12 2 1 (0)
cs 8494 13 2 1 (0)
cs 8495 14 2 1 (0)
cs 8496 15 2 1 (0)
cs 8497 16 2 1 (0)
cs 8498 17 2 1 (0)
cs 8499 18 2 1 (0)
cs 8500 19 2 1 (0)
cs 8501 20 2 1 (0)
cs 8502 21 2 1 (0)
cs 8503 22 2 1 (0)
cs 8504 23 2 1 (0)
cs 8505 24 2 1 (0)
cs 8506 25 2 1 (0)
cs 8507 26 2 1 (0)
cs 8508 27 2 1 (0)
cs 8509 28 2 1 (0)
cs 8510 29 2 1 (0)
cs 8511 30 2 1 (0)
cs 8512 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08481_08512
