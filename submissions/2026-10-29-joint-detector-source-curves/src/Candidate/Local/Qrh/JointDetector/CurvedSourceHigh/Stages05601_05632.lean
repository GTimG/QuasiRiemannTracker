/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages05601_05632
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages05601_05632
namespace Qrh.JointDetector.CurvedSourceHigh.Stages05601_05632
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages05601_05632 Qrh.JointDetector.CurvedSourceFractions.Stages05601_05632 $number $index $kind $mode $r)
cs 5601 0 2 1 (0)
cs 5602 1 2 1 (0)
cs 5603 2 2 1 (0)
cs 5604 3 2 1 (0)
cs 5605 4 2 1 (0)
cs 5606 5 2 1 (0)
cs 5607 6 2 1 (0)
cs 5608 7 2 1 (0)
cs 5609 8 2 1 (0)
cs 5610 9 2 1 (0)
cs 5611 10 2 1 (0)
cs 5612 11 2 1 (0)
cs 5613 12 2 1 (0)
cs 5614 13 2 1 (0)
cs 5615 14 2 1 (0)
cs 5616 15 2 1 (0)
cs 5617 16 2 1 (0)
cs 5618 17 2 1 (0)
cs 5619 18 2 1 (0)
cs 5620 19 2 1 (0)
cs 5621 20 2 1 (0)
cs 5622 21 2 1 (0)
cs 5623 22 2 1 (0)
cs 5624 23 2 1 (0)
cs 5625 24 2 1 (0)
cs 5626 25 2 1 (0)
cs 5627 26 2 1 (0)
cs 5628 27 2 1 (0)
cs 5629 28 2 1 (0)
cs 5630 29 2 1 (0)
cs 5631 30 2 1 (0)
cs 5632 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages05601_05632
