/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages16481_16512
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages16481_16512
namespace Qrh.JointDetector.CurvedSourceHigh.Stages16481_16512
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages16481_16512 Qrh.JointDetector.CurvedSourceFractions.Stages16481_16512 $number $index $kind $mode $r)
cs 16481 0 1 0 (1)
cs 16482 1 1 0 (1)
cs 16483 2 1 0 (1)
cs 16484 3 1 0 (1)
cs 16485 4 1 0 (1)
cs 16486 5 1 0 (1)
cs 16487 6 1 0 (1)
cs 16488 7 1 0 (1)
cs 16489 8 1 0 (1)
cs 16490 9 1 0 (1)
cs 16491 10 1 0 (1)
cs 16492 11 1 0 (1)
cs 16493 12 1 0 (1)
cs 16494 13 1 0 (1)
cs 16495 14 1 0 (1)
cs 16496 15 1 0 (1)
cs 16497 16 1 0 (1)
cs 16498 17 1 0 (1)
cs 16499 18 1 0 (1)
cs 16500 19 1 0 (1)
cs 16501 20 1 0 (1)
cs 16502 21 1 0 (1)
cs 16503 22 1 0 (1)
cs 16504 23 1 0 (1)
cs 16505 24 1 0 (1)
cs 16506 25 1 0 (1)
cs 16507 26 1 0 (1)
cs 16508 27 1 0 (1)
cs 16509 28 1 0 (1)
cs 16510 29 1 0 (1)
cs 16511 30 1 0 (1)
cs 16512 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages16481_16512
