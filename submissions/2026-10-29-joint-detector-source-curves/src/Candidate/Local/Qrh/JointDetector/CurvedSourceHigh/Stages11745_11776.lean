/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages11745_11776
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages11745_11776
namespace Qrh.JointDetector.CurvedSourceHigh.Stages11745_11776
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages11745_11776 Qrh.JointDetector.CurvedSourceFractions.Stages11745_11776 $number $index $kind $mode $r)
cs 11745 0 2 1 (0)
cs 11746 1 2 1 (0)
cs 11747 2 2 1 (0)
cs 11748 3 2 1 (0)
cs 11749 4 2 1 (0)
cs 11750 5 2 1 (0)
cs 11751 6 2 1 (0)
cs 11752 7 2 1 (0)
cs 11753 8 2 1 (0)
cs 11754 9 2 1 (0)
cs 11755 10 2 1 (0)
cs 11756 11 2 1 (0)
cs 11757 12 2 1 (0)
cs 11758 13 2 1 (0)
cs 11759 14 2 1 (0)
cs 11760 15 2 1 (0)
cs 11761 16 2 1 (0)
cs 11762 17 2 1 (0)
cs 11763 18 2 1 (0)
cs 11764 19 2 1 (0)
cs 11765 20 2 1 (0)
cs 11766 21 2 1 (0)
cs 11767 22 2 1 (0)
cs 11768 23 2 1 (0)
cs 11769 24 2 1 (0)
cs 11770 25 2 1 (0)
cs 11771 26 2 1 (0)
cs 11772 27 2 1 (0)
cs 11773 28 2 1 (0)
cs 11774 29 2 1 (0)
cs 11775 30 2 1 (0)
cs 11776 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages11745_11776
