/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages15585_15616
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages15585_15616
namespace Qrh.JointDetector.CurvedSourceHigh.Stages15585_15616
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages15585_15616 Qrh.JointDetector.CurvedSourceFractions.Stages15585_15616 $number $index $kind $mode $r)
cs 15585 0 1 0 (1)
cs 15586 1 1 0 (1)
cs 15587 2 1 0 (1)
cs 15588 3 1 0 (1)
cs 15589 4 1 0 (1)
cs 15590 5 1 0 (1)
cs 15591 6 1 0 (1)
cs 15592 7 1 0 (1)
cs 15593 8 1 0 (1)
cs 15594 9 1 0 (1)
cs 15595 10 1 0 (1)
cs 15596 11 1 0 (1)
cs 15597 12 1 0 (1)
cs 15598 13 1 0 (1)
cs 15599 14 1 0 (1)
cs 15600 15 1 0 (1)
cs 15601 16 1 0 (1)
cs 15602 17 1 0 (1)
cs 15603 18 1 0 (1)
cs 15604 19 1 0 (1)
cs 15605 20 1 0 (1)
cs 15606 21 1 0 (1)
cs 15607 22 1 0 (1)
cs 15608 23 1 0 (1)
cs 15609 24 1 0 (1)
cs 15610 25 1 0 (1)
cs 15611 26 1 0 (1)
cs 15612 27 1 0 (1)
cs 15613 28 1 0 (1)
cs 15614 29 1 0 (1)
cs 15615 30 1 0 (1)
cs 15616 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages15585_15616
