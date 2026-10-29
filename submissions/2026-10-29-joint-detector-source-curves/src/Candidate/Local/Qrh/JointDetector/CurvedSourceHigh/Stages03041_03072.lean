/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages03041_03072
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages03041_03072
namespace Qrh.JointDetector.CurvedSourceHigh.Stages03041_03072
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages03041_03072 Qrh.JointDetector.CurvedSourceFractions.Stages03041_03072 $number $index $kind $mode $r)
cs 3041 0 2 1 (0)
cs 3042 1 2 1 (0)
cs 3043 2 2 1 (0)
cs 3044 3 2 1 (0)
cs 3045 4 2 1 (0)
cs 3046 5 2 1 (0)
cs 3047 6 2 1 (0)
cs 3048 7 2 1 (0)
cs 3049 8 2 1 (0)
cs 3050 9 2 1 (0)
cs 3051 10 2 1 (0)
cs 3052 11 2 1 (0)
cs 3053 12 2 1 (0)
cs 3054 13 2 1 (0)
cs 3055 14 2 1 (0)
cs 3056 15 2 1 (0)
cs 3057 16 2 1 (0)
cs 3058 17 2 1 (0)
cs 3059 18 2 1 (0)
cs 3060 19 2 1 (0)
cs 3061 20 2 1 (0)
cs 3062 21 2 1 (0)
cs 3063 22 2 1 (0)
cs 3064 23 2 1 (0)
cs 3065 24 2 1 (0)
cs 3066 25 2 1 (0)
cs 3067 26 2 1 (0)
cs 3068 27 2 1 (0)
cs 3069 28 2 1 (0)
cs 3070 29 2 1 (0)
cs 3071 30 2 1 (0)
cs 3072 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages03041_03072
