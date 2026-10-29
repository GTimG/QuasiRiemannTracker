/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04161_04192
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04161_04192
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04161_04192
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04161_04192 Qrh.JointDetector.CurvedSourceFractions.Stages04161_04192 $number $index $kind $mode $r)
cs 4161 0 2 1 (0)
cs 4162 1 2 1 (0)
cs 4163 2 2 1 (0)
cs 4164 3 2 1 (0)
cs 4165 4 2 1 (0)
cs 4166 5 2 1 (0)
cs 4167 6 2 1 (0)
cs 4168 7 2 1 (0)
cs 4169 8 2 1 (0)
cs 4170 9 2 1 (0)
cs 4171 10 2 1 (0)
cs 4172 11 2 1 (0)
cs 4173 12 2 1 (0)
cs 4174 13 2 1 (0)
cs 4175 14 2 1 (0)
cs 4176 15 2 1 (0)
cs 4177 16 2 1 (0)
cs 4178 17 2 1 (0)
cs 4179 18 2 1 (0)
cs 4180 19 2 1 (0)
cs 4181 20 2 1 (0)
cs 4182 21 2 1 (0)
cs 4183 22 2 1 (0)
cs 4184 23 2 1 (0)
cs 4185 24 2 1 (0)
cs 4186 25 2 1 (0)
cs 4187 26 2 1 (0)
cs 4188 27 2 1 (0)
cs 4189 28 2 1 (0)
cs 4190 29 2 1 (0)
cs 4191 30 2 1 (0)
cs 4192 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04161_04192
