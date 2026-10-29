/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08161_08192
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08161_08192
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08161_08192
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08161_08192 Qrh.JointDetector.CurvedSourceFractions.Stages08161_08192 $number $index $kind $mode $r)
cs 8161 0 2 1 (0)
cs 8162 1 2 1 (0)
cs 8163 2 2 1 (0)
cs 8164 3 2 1 (0)
cs 8165 4 2 1 (0)
cs 8166 5 2 1 (0)
cs 8167 6 2 1 (0)
cs 8168 7 2 1 (0)
cs 8169 8 2 1 (0)
cs 8170 9 2 1 (0)
cs 8171 10 2 1 (0)
cs 8172 11 2 1 (0)
cs 8173 12 2 1 (0)
cs 8174 13 2 1 (0)
cs 8175 14 2 1 (0)
cs 8176 15 2 1 (0)
cs 8177 16 2 1 (0)
cs 8178 17 2 1 (0)
cs 8179 18 2 1 (0)
cs 8180 19 2 1 (0)
cs 8181 20 2 1 (0)
cs 8182 21 2 1 (0)
cs 8183 22 2 1 (0)
cs 8184 23 2 1 (0)
cs 8185 24 2 1 (0)
cs 8186 25 2 1 (0)
cs 8187 26 2 1 (0)
cs 8188 27 2 1 (0)
cs 8189 28 2 1 (0)
cs 8190 29 2 1 (0)
cs 8191 30 2 1 (0)
cs 8192 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08161_08192
