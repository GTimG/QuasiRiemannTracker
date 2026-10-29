/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages06881_06912
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages06881_06912
namespace Qrh.JointDetector.CurvedSourceHigh.Stages06881_06912
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages06881_06912 Qrh.JointDetector.CurvedSourceFractions.Stages06881_06912 $number $index $kind $mode $r)
cs 6881 0 2 1 (0)
cs 6882 1 2 1 (0)
cs 6883 2 2 1 (0)
cs 6884 3 2 1 (0)
cs 6885 4 2 1 (0)
cs 6886 5 2 1 (0)
cs 6887 6 2 1 (0)
cs 6888 7 2 1 (0)
cs 6889 8 2 1 (0)
cs 6890 9 2 1 (0)
cs 6891 10 2 1 (0)
cs 6892 11 2 1 (0)
cs 6893 12 2 1 (0)
cs 6894 13 2 1 (0)
cs 6895 14 2 1 (0)
cs 6896 15 2 1 (0)
cs 6897 16 2 1 (0)
cs 6898 17 2 1 (0)
cs 6899 18 2 1 (0)
cs 6900 19 2 1 (0)
cs 6901 20 2 1 (0)
cs 6902 21 2 1 (0)
cs 6903 22 2 1 (0)
cs 6904 23 2 1 (0)
cs 6905 24 2 1 (0)
cs 6906 25 2 1 (0)
cs 6907 26 2 1 (0)
cs 6908 27 2 1 (0)
cs 6909 28 2 1 (0)
cs 6910 29 2 1 (0)
cs 6911 30 2 1 (0)
cs 6912 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages06881_06912
