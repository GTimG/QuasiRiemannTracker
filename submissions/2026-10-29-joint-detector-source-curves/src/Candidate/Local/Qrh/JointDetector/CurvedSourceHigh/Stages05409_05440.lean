/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages05409_05440
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages05409_05440
namespace Qrh.JointDetector.CurvedSourceHigh.Stages05409_05440
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages05409_05440 Qrh.JointDetector.CurvedSourceFractions.Stages05409_05440 $number $index $kind $mode $r)
cs 5409 0 2 1 (0)
cs 5410 1 2 1 (0)
cs 5411 2 2 1 (0)
cs 5412 3 2 1 (0)
cs 5413 4 2 1 (0)
cs 5414 5 2 1 (0)
cs 5415 6 2 1 (0)
cs 5416 7 2 1 (0)
cs 5417 8 2 1 (0)
cs 5418 9 2 1 (0)
cs 5419 10 2 1 (0)
cs 5420 11 2 1 (0)
cs 5421 12 2 1 (0)
cs 5422 13 2 1 (0)
cs 5423 14 2 1 (0)
cs 5424 15 2 1 (0)
cs 5425 16 2 1 (0)
cs 5426 17 2 1 (0)
cs 5427 18 2 1 (0)
cs 5428 19 2 1 (0)
cs 5429 20 2 1 (0)
cs 5430 21 2 1 (0)
cs 5431 22 2 1 (0)
cs 5432 23 2 1 (0)
cs 5433 24 2 1 (0)
cs 5434 25 2 1 (0)
cs 5435 26 2 1 (0)
cs 5436 27 2 1 (0)
cs 5437 28 2 1 (0)
cs 5438 29 2 1 (0)
cs 5439 30 2 1 (0)
cs 5440 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages05409_05440
