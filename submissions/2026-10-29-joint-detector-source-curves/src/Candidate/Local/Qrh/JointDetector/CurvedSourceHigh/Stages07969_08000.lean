/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages07969_08000
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages07969_08000
namespace Qrh.JointDetector.CurvedSourceHigh.Stages07969_08000
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages07969_08000 Qrh.JointDetector.CurvedSourceFractions.Stages07969_08000 $number $index $kind $mode $r)
cs 7969 0 2 1 (0)
cs 7970 1 2 1 (0)
cs 7971 2 2 1 (0)
cs 7972 3 2 1 (0)
cs 7973 4 2 1 (0)
cs 7974 5 2 1 (0)
cs 7975 6 2 1 (0)
cs 7976 7 2 1 (0)
cs 7977 8 2 1 (0)
cs 7978 9 2 1 (0)
cs 7979 10 2 1 (0)
cs 7980 11 2 1 (0)
cs 7981 12 2 1 (0)
cs 7982 13 2 1 (0)
cs 7983 14 2 1 (0)
cs 7984 15 2 1 (0)
cs 7985 16 2 1 (0)
cs 7986 17 2 1 (0)
cs 7987 18 2 1 (0)
cs 7988 19 2 1 (0)
cs 7989 20 2 1 (0)
cs 7990 21 2 1 (0)
cs 7991 22 2 1 (0)
cs 7992 23 2 1 (0)
cs 7993 24 2 1 (0)
cs 7994 25 2 1 (0)
cs 7995 26 2 1 (0)
cs 7996 27 2 1 (0)
cs 7997 28 2 1 (0)
cs 7998 29 2 1 (0)
cs 7999 30 2 1 (0)
cs 8000 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages07969_08000
