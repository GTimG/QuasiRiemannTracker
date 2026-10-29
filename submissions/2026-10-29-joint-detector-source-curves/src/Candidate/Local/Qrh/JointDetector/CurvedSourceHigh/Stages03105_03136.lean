/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages03105_03136
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages03105_03136
namespace Qrh.JointDetector.CurvedSourceHigh.Stages03105_03136
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages03105_03136 Qrh.JointDetector.CurvedSourceFractions.Stages03105_03136 $number $index $kind $mode $r)
cs 3105 0 2 1 (0)
cs 3106 1 2 1 (0)
cs 3107 2 2 1 (0)
cs 3108 3 2 1 (0)
cs 3109 4 2 1 (0)
cs 3110 5 2 1 (0)
cs 3111 6 2 1 (0)
cs 3112 7 2 1 (0)
cs 3113 8 2 1 (0)
cs 3114 9 2 1 (0)
cs 3115 10 2 1 (0)
cs 3116 11 2 1 (0)
cs 3117 12 2 1 (0)
cs 3118 13 2 1 (0)
cs 3119 14 2 1 (0)
cs 3120 15 2 1 (0)
cs 3121 16 2 1 (0)
cs 3122 17 2 1 (0)
cs 3123 18 2 1 (0)
cs 3124 19 2 1 (0)
cs 3125 20 2 1 (0)
cs 3126 21 2 1 (0)
cs 3127 22 2 1 (0)
cs 3128 23 2 1 (0)
cs 3129 24 2 1 (0)
cs 3130 25 2 1 (0)
cs 3131 26 2 1 (0)
cs 3132 27 2 1 (0)
cs 3133 28 2 1 (0)
cs 3134 29 2 1 (0)
cs 3135 30 2 1 (0)
cs 3136 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages03105_03136
