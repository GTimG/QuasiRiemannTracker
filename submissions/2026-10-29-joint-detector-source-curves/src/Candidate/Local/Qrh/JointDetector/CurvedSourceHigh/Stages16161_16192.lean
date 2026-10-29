/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages16161_16192
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages16161_16192
namespace Qrh.JointDetector.CurvedSourceHigh.Stages16161_16192
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages16161_16192 Qrh.JointDetector.CurvedSourceFractions.Stages16161_16192 $number $index $kind $mode $r)
cs 16161 0 1 0 (1)
cs 16162 1 1 0 (1)
cs 16163 2 1 0 (1)
cs 16164 3 1 0 (1)
cs 16165 4 1 0 (1)
cs 16166 5 1 0 (1)
cs 16167 6 1 0 (1)
cs 16168 7 1 0 (1)
cs 16169 8 1 0 (1)
cs 16170 9 1 0 (1)
cs 16171 10 1 0 (1)
cs 16172 11 1 0 (1)
cs 16173 12 1 0 (1)
cs 16174 13 1 0 (1)
cs 16175 14 1 0 (1)
cs 16176 15 1 0 (1)
cs 16177 16 1 0 (1)
cs 16178 17 1 0 (1)
cs 16179 18 1 0 (1)
cs 16180 19 1 0 (1)
cs 16181 20 1 0 (1)
cs 16182 21 1 0 (1)
cs 16183 22 1 0 (1)
cs 16184 23 1 0 (1)
cs 16185 24 1 0 (1)
cs 16186 25 1 0 (1)
cs 16187 26 1 0 (1)
cs 16188 27 1 0 (1)
cs 16189 28 1 0 (1)
cs 16190 29 1 0 (1)
cs 16191 30 1 0 (1)
cs 16192 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages16161_16192
