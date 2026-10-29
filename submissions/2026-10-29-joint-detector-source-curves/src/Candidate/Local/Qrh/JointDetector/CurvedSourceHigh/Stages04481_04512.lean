/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04481_04512
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04481_04512
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04481_04512
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04481_04512 Qrh.JointDetector.CurvedSourceFractions.Stages04481_04512 $number $index $kind $mode $r)
cs 4481 0 2 1 (0)
cs 4482 1 2 1 (0)
cs 4483 2 2 1 (0)
cs 4484 3 2 1 (0)
cs 4485 4 2 1 (0)
cs 4486 5 2 1 (0)
cs 4487 6 2 1 (0)
cs 4488 7 2 1 (0)
cs 4489 8 2 1 (0)
cs 4490 9 2 1 (0)
cs 4491 10 2 1 (0)
cs 4492 11 2 1 (0)
cs 4493 12 2 1 (0)
cs 4494 13 2 1 (0)
cs 4495 14 2 1 (0)
cs 4496 15 2 1 (0)
cs 4497 16 2 1 (0)
cs 4498 17 2 1 (0)
cs 4499 18 2 1 (0)
cs 4500 19 2 1 (0)
cs 4501 20 2 1 (0)
cs 4502 21 2 1 (0)
cs 4503 22 2 1 (0)
cs 4504 23 2 1 (0)
cs 4505 24 2 1 (0)
cs 4506 25 2 1 (0)
cs 4507 26 2 1 (0)
cs 4508 27 2 1 (0)
cs 4509 28 2 1 (0)
cs 4510 29 2 1 (0)
cs 4511 30 2 1 (0)
cs 4512 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04481_04512
