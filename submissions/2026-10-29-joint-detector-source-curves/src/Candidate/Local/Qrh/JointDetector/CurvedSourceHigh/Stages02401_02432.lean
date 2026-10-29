/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages02401_02432
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages02401_02432
namespace Qrh.JointDetector.CurvedSourceHigh.Stages02401_02432
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages02401_02432 Qrh.JointDetector.CurvedSourceFractions.Stages02401_02432 $number $index $kind $mode $r)
cs 2401 0 2 1 (0)
cs 2402 1 2 1 (0)
cs 2403 2 2 1 (0)
cs 2404 3 2 1 (0)
cs 2405 4 2 1 (0)
cs 2406 5 2 1 (0)
cs 2407 6 2 1 (0)
cs 2408 7 2 1 (0)
cs 2409 8 2 1 (0)
cs 2410 9 2 1 (0)
cs 2411 10 2 1 (0)
cs 2412 11 2 1 (0)
cs 2413 12 2 1 (0)
cs 2414 13 2 1 (0)
cs 2415 14 2 1 (0)
cs 2416 15 2 1 (0)
cs 2417 16 2 1 (0)
cs 2418 17 2 1 (0)
cs 2419 18 2 1 (0)
cs 2420 19 2 1 (0)
cs 2421 20 2 1 (0)
cs 2422 21 2 1 (0)
cs 2423 22 2 1 (0)
cs 2424 23 2 1 (0)
cs 2425 24 2 1 (0)
cs 2426 25 2 1 (0)
cs 2427 26 2 1 (0)
cs 2428 27 2 1 (0)
cs 2429 28 2 1 (0)
cs 2430 29 2 1 (0)
cs 2431 30 2 1 (0)
cs 2432 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages02401_02432
