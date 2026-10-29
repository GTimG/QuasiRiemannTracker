/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages06145_06176
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages06145_06176
namespace Qrh.JointDetector.CurvedSourceHigh.Stages06145_06176
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages06145_06176 Qrh.JointDetector.CurvedSourceFractions.Stages06145_06176 $number $index $kind $mode $r)
cs 6145 0 2 1 (0)
cs 6146 1 2 1 (0)
cs 6147 2 2 1 (0)
cs 6148 3 2 1 (0)
cs 6149 4 2 1 (0)
cs 6150 5 2 1 (0)
cs 6151 6 2 1 (0)
cs 6152 7 2 1 (0)
cs 6153 8 2 1 (0)
cs 6154 9 2 1 (0)
cs 6155 10 2 1 (0)
cs 6156 11 2 1 (0)
cs 6157 12 2 1 (0)
cs 6158 13 2 1 (0)
cs 6159 14 2 1 (0)
cs 6160 15 2 1 (0)
cs 6161 16 2 1 (0)
cs 6162 17 2 1 (0)
cs 6163 18 2 1 (0)
cs 6164 19 2 1 (0)
cs 6165 20 2 1 (0)
cs 6166 21 2 1 (0)
cs 6167 22 2 1 (0)
cs 6168 23 2 1 (0)
cs 6169 24 2 1 (0)
cs 6170 25 2 1 (0)
cs 6171 26 2 1 (0)
cs 6172 27 2 1 (0)
cs 6173 28 2 1 (0)
cs 6174 29 2 1 (0)
cs 6175 30 2 1 (0)
cs 6176 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages06145_06176
