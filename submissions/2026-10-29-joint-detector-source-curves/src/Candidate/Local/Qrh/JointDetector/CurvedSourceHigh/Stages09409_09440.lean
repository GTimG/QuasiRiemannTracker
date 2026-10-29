/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages09409_09440
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages09409_09440
namespace Qrh.JointDetector.CurvedSourceHigh.Stages09409_09440
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages09409_09440 Qrh.JointDetector.CurvedSourceFractions.Stages09409_09440 $number $index $kind $mode $r)
cs 9409 0 2 1 (0)
cs 9410 1 2 1 (0)
cs 9411 2 2 1 (0)
cs 9412 3 2 1 (0)
cs 9413 4 2 1 (0)
cs 9414 5 2 1 (0)
cs 9415 6 2 1 (0)
cs 9416 7 2 1 (0)
cs 9417 8 2 1 (0)
cs 9418 9 2 1 (0)
cs 9419 10 2 1 (0)
cs 9420 11 2 1 (0)
cs 9421 12 2 1 (0)
cs 9422 13 2 1 (0)
cs 9423 14 2 1 (0)
cs 9424 15 2 1 (0)
cs 9425 16 2 1 (0)
cs 9426 17 2 1 (0)
cs 9427 18 2 1 (0)
cs 9428 19 2 1 (0)
cs 9429 20 2 1 (0)
cs 9430 21 2 1 (0)
cs 9431 22 2 1 (0)
cs 9432 23 2 1 (0)
cs 9433 24 2 1 (0)
cs 9434 25 2 1 (0)
cs 9435 26 2 1 (0)
cs 9436 27 2 1 (0)
cs 9437 28 2 1 (0)
cs 9438 29 2 1 (0)
cs 9439 30 2 1 (0)
cs 9440 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages09409_09440
