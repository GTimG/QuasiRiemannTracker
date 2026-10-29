/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages06721_06752
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages06721_06752
namespace Qrh.JointDetector.CurvedSourceHigh.Stages06721_06752
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages06721_06752 Qrh.JointDetector.CurvedSourceFractions.Stages06721_06752 $number $index $kind $mode $r)
cs 6721 0 2 1 (0)
cs 6722 1 2 1 (0)
cs 6723 2 2 1 (0)
cs 6724 3 2 1 (0)
cs 6725 4 2 1 (0)
cs 6726 5 2 1 (0)
cs 6727 6 2 1 (0)
cs 6728 7 2 1 (0)
cs 6729 8 2 1 (0)
cs 6730 9 2 1 (0)
cs 6731 10 2 1 (0)
cs 6732 11 2 1 (0)
cs 6733 12 2 1 (0)
cs 6734 13 2 1 (0)
cs 6735 14 2 1 (0)
cs 6736 15 2 1 (0)
cs 6737 16 2 1 (0)
cs 6738 17 2 1 (0)
cs 6739 18 2 1 (0)
cs 6740 19 2 1 (0)
cs 6741 20 2 1 (0)
cs 6742 21 2 1 (0)
cs 6743 22 2 1 (0)
cs 6744 23 2 1 (0)
cs 6745 24 2 1 (0)
cs 6746 25 2 1 (0)
cs 6747 26 2 1 (0)
cs 6748 27 2 1 (0)
cs 6749 28 2 1 (0)
cs 6750 29 2 1 (0)
cs 6751 30 2 1 (0)
cs 6752 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages06721_06752
