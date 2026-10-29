/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages07169_07200
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages07169_07200
namespace Qrh.JointDetector.CurvedSourceHigh.Stages07169_07200
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages07169_07200 Qrh.JointDetector.CurvedSourceFractions.Stages07169_07200 $number $index $kind $mode $r)
cs 7169 0 2 1 (0)
cs 7170 1 2 1 (0)
cs 7171 2 2 1 (0)
cs 7172 3 2 1 (0)
cs 7173 4 2 1 (0)
cs 7174 5 2 1 (0)
cs 7175 6 2 1 (0)
cs 7176 7 2 1 (0)
cs 7177 8 2 1 (0)
cs 7178 9 2 1 (0)
cs 7179 10 2 1 (0)
cs 7180 11 2 1 (0)
cs 7181 12 2 1 (0)
cs 7182 13 2 1 (0)
cs 7183 14 2 1 (0)
cs 7184 15 2 1 (0)
cs 7185 16 2 1 (0)
cs 7186 17 2 1 (0)
cs 7187 18 2 1 (0)
cs 7188 19 2 1 (0)
cs 7189 20 2 1 (0)
cs 7190 21 2 1 (0)
cs 7191 22 2 1 (0)
cs 7192 23 2 1 (0)
cs 7193 24 2 1 (0)
cs 7194 25 2 1 (0)
cs 7195 26 2 1 (0)
cs 7196 27 2 1 (0)
cs 7197 28 2 1 (0)
cs 7198 29 2 1 (0)
cs 7199 30 2 1 (0)
cs 7200 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages07169_07200
