/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages06561_06592
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages06561_06592
namespace Qrh.JointDetector.CurvedSourceHigh.Stages06561_06592
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages06561_06592 Qrh.JointDetector.CurvedSourceFractions.Stages06561_06592 $number $index $kind $mode $r)
cs 6561 0 2 1 (0)
cs 6562 1 2 1 (0)
cs 6563 2 2 1 (0)
cs 6564 3 2 1 (0)
cs 6565 4 2 1 (0)
cs 6566 5 2 1 (0)
cs 6567 6 2 1 (0)
cs 6568 7 2 1 (0)
cs 6569 8 2 1 (0)
cs 6570 9 2 1 (0)
cs 6571 10 2 1 (0)
cs 6572 11 2 1 (0)
cs 6573 12 2 1 (0)
cs 6574 13 2 1 (0)
cs 6575 14 2 1 (0)
cs 6576 15 2 1 (0)
cs 6577 16 2 1 (0)
cs 6578 17 2 1 (0)
cs 6579 18 2 1 (0)
cs 6580 19 2 1 (0)
cs 6581 20 2 1 (0)
cs 6582 21 2 1 (0)
cs 6583 22 2 1 (0)
cs 6584 23 2 1 (0)
cs 6585 24 2 1 (0)
cs 6586 25 2 1 (0)
cs 6587 26 2 1 (0)
cs 6588 27 2 1 (0)
cs 6589 28 2 1 (0)
cs 6590 29 2 1 (0)
cs 6591 30 2 1 (0)
cs 6592 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages06561_06592
