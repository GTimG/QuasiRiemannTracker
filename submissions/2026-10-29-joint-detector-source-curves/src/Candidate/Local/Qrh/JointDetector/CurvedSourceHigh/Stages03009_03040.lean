/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages03009_03040
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages03009_03040
namespace Qrh.JointDetector.CurvedSourceHigh.Stages03009_03040
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages03009_03040 Qrh.JointDetector.CurvedSourceFractions.Stages03009_03040 $number $index $kind $mode $r)
cs 3009 0 2 1 (0)
cs 3010 1 2 1 (0)
cs 3011 2 2 1 (0)
cs 3012 3 2 1 (0)
cs 3013 4 2 1 (0)
cs 3014 5 2 1 (0)
cs 3015 6 2 1 (0)
cs 3016 7 2 1 (0)
cs 3017 8 2 1 (0)
cs 3018 9 2 1 (0)
cs 3019 10 2 1 (0)
cs 3020 11 2 1 (0)
cs 3021 12 2 1 (0)
cs 3022 13 2 1 (0)
cs 3023 14 2 1 (0)
cs 3024 15 2 1 (0)
cs 3025 16 2 1 (0)
cs 3026 17 2 1 (0)
cs 3027 18 2 1 (0)
cs 3028 19 2 1 (0)
cs 3029 20 2 1 (0)
cs 3030 21 2 1 (0)
cs 3031 22 2 1 (0)
cs 3032 23 2 1 (0)
cs 3033 24 2 1 (0)
cs 3034 25 2 1 (0)
cs 3035 26 2 1 (0)
cs 3036 27 2 1 (0)
cs 3037 28 2 1 (0)
cs 3038 29 2 1 (0)
cs 3039 30 2 1 (0)
cs 3040 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages03009_03040
