/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages07873_07904
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages07873_07904
namespace Qrh.JointDetector.CurvedSourceHigh.Stages07873_07904
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages07873_07904 Qrh.JointDetector.CurvedSourceFractions.Stages07873_07904 $number $index $kind $mode $r)
cs 7873 0 2 1 (0)
cs 7874 1 2 1 (0)
cs 7875 2 2 1 (0)
cs 7876 3 2 1 (0)
cs 7877 4 2 1 (0)
cs 7878 5 2 1 (0)
cs 7879 6 2 1 (0)
cs 7880 7 2 1 (0)
cs 7881 8 2 1 (0)
cs 7882 9 2 1 (0)
cs 7883 10 2 1 (0)
cs 7884 11 2 1 (0)
cs 7885 12 2 1 (0)
cs 7886 13 2 1 (0)
cs 7887 14 2 1 (0)
cs 7888 15 2 1 (0)
cs 7889 16 2 1 (0)
cs 7890 17 2 1 (0)
cs 7891 18 2 1 (0)
cs 7892 19 2 1 (0)
cs 7893 20 2 1 (0)
cs 7894 21 2 1 (0)
cs 7895 22 2 1 (0)
cs 7896 23 2 1 (0)
cs 7897 24 2 1 (0)
cs 7898 25 2 1 (0)
cs 7899 26 2 1 (0)
cs 7900 27 2 1 (0)
cs 7901 28 2 1 (0)
cs 7902 29 2 1 (0)
cs 7903 30 2 1 (0)
cs 7904 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages07873_07904
