/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages06401_06432
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages06401_06432
namespace Qrh.JointDetector.CurvedSourceHigh.Stages06401_06432
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages06401_06432 Qrh.JointDetector.CurvedSourceFractions.Stages06401_06432 $number $index $kind $mode $r)
cs 6401 0 2 1 (0)
cs 6402 1 2 1 (0)
cs 6403 2 2 1 (0)
cs 6404 3 2 1 (0)
cs 6405 4 2 1 (0)
cs 6406 5 2 1 (0)
cs 6407 6 2 1 (0)
cs 6408 7 2 1 (0)
cs 6409 8 2 1 (0)
cs 6410 9 2 1 (0)
cs 6411 10 2 1 (0)
cs 6412 11 2 1 (0)
cs 6413 12 2 1 (0)
cs 6414 13 2 1 (0)
cs 6415 14 2 1 (0)
cs 6416 15 2 1 (0)
cs 6417 16 2 1 (0)
cs 6418 17 2 1 (0)
cs 6419 18 2 1 (0)
cs 6420 19 2 1 (0)
cs 6421 20 2 1 (0)
cs 6422 21 2 1 (0)
cs 6423 22 2 1 (0)
cs 6424 23 2 1 (0)
cs 6425 24 2 1 (0)
cs 6426 25 2 1 (0)
cs 6427 26 2 1 (0)
cs 6428 27 2 1 (0)
cs 6429 28 2 1 (0)
cs 6430 29 2 1 (0)
cs 6431 30 2 1 (0)
cs 6432 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages06401_06432
