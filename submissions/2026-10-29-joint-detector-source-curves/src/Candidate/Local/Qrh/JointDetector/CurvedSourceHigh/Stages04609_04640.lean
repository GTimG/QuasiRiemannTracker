/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04609_04640
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04609_04640
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04609_04640
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04609_04640 Qrh.JointDetector.CurvedSourceFractions.Stages04609_04640 $number $index $kind $mode $r)
cs 4609 0 2 1 (0)
cs 4610 1 2 1 (0)
cs 4611 2 2 1 (0)
cs 4612 3 2 1 (0)
cs 4613 4 2 1 (0)
cs 4614 5 2 1 (0)
cs 4615 6 2 1 (0)
cs 4616 7 2 1 (0)
cs 4617 8 2 1 (0)
cs 4618 9 2 1 (0)
cs 4619 10 2 1 (0)
cs 4620 11 2 1 (0)
cs 4621 12 2 1 (0)
cs 4622 13 2 1 (0)
cs 4623 14 2 1 (0)
cs 4624 15 2 1 (0)
cs 4625 16 2 1 (0)
cs 4626 17 2 1 (0)
cs 4627 18 2 1 (0)
cs 4628 19 2 1 (0)
cs 4629 20 2 1 (0)
cs 4630 21 2 1 (0)
cs 4631 22 2 1 (0)
cs 4632 23 2 1 (0)
cs 4633 24 2 1 (0)
cs 4634 25 2 1 (0)
cs 4635 26 2 1 (0)
cs 4636 27 2 1 (0)
cs 4637 28 2 1 (0)
cs 4638 29 2 1 (0)
cs 4639 30 2 1 (0)
cs 4640 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04609_04640
