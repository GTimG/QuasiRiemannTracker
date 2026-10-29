/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages11873_11904
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages11873_11904
namespace Qrh.JointDetector.CurvedSourceHigh.Stages11873_11904
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages11873_11904 Qrh.JointDetector.CurvedSourceFractions.Stages11873_11904 $number $index $kind $mode $r)
cs 11873 0 2 1 (0)
cs 11874 1 2 1 (0)
cs 11875 2 2 1 (0)
cs 11876 3 2 1 (0)
cs 11877 4 2 1 (0)
cs 11878 5 2 1 (0)
cs 11879 6 2 1 (0)
cs 11880 7 2 1 (0)
cs 11881 8 2 1 (0)
cs 11882 9 2 1 (0)
cs 11883 10 2 1 (0)
cs 11884 11 2 1 (0)
cs 11885 12 2 1 (0)
cs 11886 13 2 1 (0)
cs 11887 14 2 1 (0)
cs 11888 15 2 1 (0)
cs 11889 16 2 1 (0)
cs 11890 17 2 1 (0)
cs 11891 18 2 1 (0)
cs 11892 19 2 1 (0)
cs 11893 20 2 1 (0)
cs 11894 21 2 1 (0)
cs 11895 22 2 1 (0)
cs 11896 23 2 1 (0)
cs 11897 24 2 1 (0)
cs 11898 25 2 1 (0)
cs 11899 26 2 1 (0)
cs 11900 27 2 1 (0)
cs 11901 28 2 1 (0)
cs 11902 29 2 1 (0)
cs 11903 30 2 1 (0)
cs 11904 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages11873_11904
