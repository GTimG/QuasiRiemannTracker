/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages07809_07840
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages07809_07840
namespace Qrh.JointDetector.CurvedSourceHigh.Stages07809_07840
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages07809_07840 Qrh.JointDetector.CurvedSourceFractions.Stages07809_07840 $number $index $kind $mode $r)
cs 7809 0 2 1 (0)
cs 7810 1 2 1 (0)
cs 7811 2 2 1 (0)
cs 7812 3 2 1 (0)
cs 7813 4 2 1 (0)
cs 7814 5 2 1 (0)
cs 7815 6 2 1 (0)
cs 7816 7 2 1 (0)
cs 7817 8 2 1 (0)
cs 7818 9 2 1 (0)
cs 7819 10 2 1 (0)
cs 7820 11 2 1 (0)
cs 7821 12 2 1 (0)
cs 7822 13 2 1 (0)
cs 7823 14 2 1 (0)
cs 7824 15 2 1 (0)
cs 7825 16 2 1 (0)
cs 7826 17 2 1 (0)
cs 7827 18 2 1 (0)
cs 7828 19 2 1 (0)
cs 7829 20 2 1 (0)
cs 7830 21 2 1 (0)
cs 7831 22 2 1 (0)
cs 7832 23 2 1 (0)
cs 7833 24 2 1 (0)
cs 7834 25 2 1 (0)
cs 7835 26 2 1 (0)
cs 7836 27 2 1 (0)
cs 7837 28 2 1 (0)
cs 7838 29 2 1 (0)
cs 7839 30 2 1 (0)
cs 7840 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages07809_07840
