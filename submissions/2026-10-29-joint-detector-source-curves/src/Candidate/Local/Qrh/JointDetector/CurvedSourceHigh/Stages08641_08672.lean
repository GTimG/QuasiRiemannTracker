/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08641_08672
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08641_08672
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08641_08672
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08641_08672 Qrh.JointDetector.CurvedSourceFractions.Stages08641_08672 $number $index $kind $mode $r)
cs 8641 0 2 1 (0)
cs 8642 1 2 1 (0)
cs 8643 2 2 1 (0)
cs 8644 3 2 1 (0)
cs 8645 4 2 1 (0)
cs 8646 5 2 1 (0)
cs 8647 6 2 1 (0)
cs 8648 7 2 1 (0)
cs 8649 8 2 1 (0)
cs 8650 9 2 1 (0)
cs 8651 10 2 1 (0)
cs 8652 11 2 1 (0)
cs 8653 12 2 1 (0)
cs 8654 13 2 1 (0)
cs 8655 14 2 1 (0)
cs 8656 15 2 1 (0)
cs 8657 16 2 1 (0)
cs 8658 17 2 1 (0)
cs 8659 18 2 1 (0)
cs 8660 19 2 1 (0)
cs 8661 20 2 1 (0)
cs 8662 21 2 1 (0)
cs 8663 22 2 1 (0)
cs 8664 23 2 1 (0)
cs 8665 24 2 1 (0)
cs 8666 25 2 1 (0)
cs 8667 26 2 1 (0)
cs 8668 27 2 1 (0)
cs 8669 28 2 1 (0)
cs 8670 29 2 1 (0)
cs 8671 30 2 1 (0)
cs 8672 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08641_08672
