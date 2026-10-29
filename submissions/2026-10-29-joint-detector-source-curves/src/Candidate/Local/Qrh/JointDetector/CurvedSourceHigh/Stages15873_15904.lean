/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages15873_15904
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages15873_15904
namespace Qrh.JointDetector.CurvedSourceHigh.Stages15873_15904
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages15873_15904 Qrh.JointDetector.CurvedSourceFractions.Stages15873_15904 $number $index $kind $mode $r)
cs 15873 0 1 0 (1)
cs 15874 1 1 0 (1)
cs 15875 2 1 0 (1)
cs 15876 3 1 0 (1)
cs 15877 4 1 0 (1)
cs 15878 5 1 0 (1)
cs 15879 6 1 0 (1)
cs 15880 7 1 0 (1)
cs 15881 8 1 0 (1)
cs 15882 9 1 0 (1)
cs 15883 10 1 0 (1)
cs 15884 11 1 0 (1)
cs 15885 12 1 0 (1)
cs 15886 13 1 0 (1)
cs 15887 14 1 0 (1)
cs 15888 15 1 0 (1)
cs 15889 16 1 0 (1)
cs 15890 17 1 0 (1)
cs 15891 18 1 0 (1)
cs 15892 19 1 0 (1)
cs 15893 20 1 0 (1)
cs 15894 21 1 0 (1)
cs 15895 22 1 0 (1)
cs 15896 23 1 0 (1)
cs 15897 24 1 0 (1)
cs 15898 25 1 0 (1)
cs 15899 26 1 0 (1)
cs 15900 27 1 0 (1)
cs 15901 28 1 0 (1)
cs 15902 29 1 0 (1)
cs 15903 30 1 0 (1)
cs 15904 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages15873_15904
