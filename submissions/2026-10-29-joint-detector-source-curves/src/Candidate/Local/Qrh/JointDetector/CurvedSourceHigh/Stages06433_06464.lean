/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages06433_06464
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages06433_06464
namespace Qrh.JointDetector.CurvedSourceHigh.Stages06433_06464
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages06433_06464 Qrh.JointDetector.CurvedSourceFractions.Stages06433_06464 $number $index $kind $mode $r)
cs 6433 0 2 1 (0)
cs 6434 1 2 1 (0)
cs 6435 2 2 1 (0)
cs 6436 3 2 1 (0)
cs 6437 4 2 1 (0)
cs 6438 5 2 1 (0)
cs 6439 6 2 1 (0)
cs 6440 7 2 1 (0)
cs 6441 8 2 1 (0)
cs 6442 9 2 1 (0)
cs 6443 10 2 1 (0)
cs 6444 11 2 1 (0)
cs 6445 12 2 1 (0)
cs 6446 13 2 1 (0)
cs 6447 14 2 1 (0)
cs 6448 15 2 1 (0)
cs 6449 16 2 1 (0)
cs 6450 17 2 1 (0)
cs 6451 18 2 1 (0)
cs 6452 19 2 1 (0)
cs 6453 20 2 1 (0)
cs 6454 21 2 1 (0)
cs 6455 22 2 1 (0)
cs 6456 23 2 1 (0)
cs 6457 24 2 1 (0)
cs 6458 25 2 1 (0)
cs 6459 26 2 1 (0)
cs 6460 27 2 1 (0)
cs 6461 28 2 1 (0)
cs 6462 29 2 1 (0)
cs 6463 30 2 1 (0)
cs 6464 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages06433_06464
