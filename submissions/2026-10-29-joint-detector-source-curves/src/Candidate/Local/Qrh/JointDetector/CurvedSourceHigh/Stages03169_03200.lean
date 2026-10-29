/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages03169_03200
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages03169_03200
namespace Qrh.JointDetector.CurvedSourceHigh.Stages03169_03200
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages03169_03200 Qrh.JointDetector.CurvedSourceFractions.Stages03169_03200 $number $index $kind $mode $r)
cs 3169 0 2 1 (0)
cs 3170 1 2 1 (0)
cs 3171 2 2 1 (0)
cs 3172 3 2 1 (0)
cs 3173 4 2 1 (0)
cs 3174 5 2 1 (0)
cs 3175 6 2 1 (0)
cs 3176 7 2 1 (0)
cs 3177 8 2 1 (0)
cs 3178 9 2 1 (0)
cs 3179 10 2 1 (0)
cs 3180 11 2 1 (0)
cs 3181 12 2 1 (0)
cs 3182 13 2 1 (0)
cs 3183 14 2 1 (0)
cs 3184 15 2 1 (0)
cs 3185 16 2 1 (0)
cs 3186 17 2 1 (0)
cs 3187 18 2 1 (0)
cs 3188 19 2 1 (0)
cs 3189 20 2 1 (0)
cs 3190 21 2 1 (0)
cs 3191 22 2 1 (0)
cs 3192 23 2 1 (0)
cs 3193 24 2 1 (0)
cs 3194 25 2 1 (0)
cs 3195 26 2 1 (0)
cs 3196 27 2 1 (0)
cs 3197 28 2 1 (0)
cs 3198 29 2 1 (0)
cs 3199 30 2 1 (0)
cs 3200 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages03169_03200
