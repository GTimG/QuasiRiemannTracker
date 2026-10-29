/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages06241_06272
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages06241_06272
namespace Qrh.JointDetector.CurvedSourceHigh.Stages06241_06272
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages06241_06272 Qrh.JointDetector.CurvedSourceFractions.Stages06241_06272 $number $index $kind $mode $r)
cs 6241 0 2 1 (0)
cs 6242 1 2 1 (0)
cs 6243 2 2 1 (0)
cs 6244 3 2 1 (0)
cs 6245 4 2 1 (0)
cs 6246 5 2 1 (0)
cs 6247 6 2 1 (0)
cs 6248 7 2 1 (0)
cs 6249 8 2 1 (0)
cs 6250 9 2 1 (0)
cs 6251 10 2 1 (0)
cs 6252 11 2 1 (0)
cs 6253 12 2 1 (0)
cs 6254 13 2 1 (0)
cs 6255 14 2 1 (0)
cs 6256 15 2 1 (0)
cs 6257 16 2 1 (0)
cs 6258 17 2 1 (0)
cs 6259 18 2 1 (0)
cs 6260 19 2 1 (0)
cs 6261 20 2 1 (0)
cs 6262 21 2 1 (0)
cs 6263 22 2 1 (0)
cs 6264 23 2 1 (0)
cs 6265 24 2 1 (0)
cs 6266 25 2 1 (0)
cs 6267 26 2 1 (0)
cs 6268 27 2 1 (0)
cs 6269 28 2 1 (0)
cs 6270 29 2 1 (0)
cs 6271 30 2 1 (0)
cs 6272 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages06241_06272
