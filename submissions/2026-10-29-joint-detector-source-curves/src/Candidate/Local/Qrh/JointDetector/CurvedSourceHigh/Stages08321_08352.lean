/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08321_08352
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08321_08352
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08321_08352
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08321_08352 Qrh.JointDetector.CurvedSourceFractions.Stages08321_08352 $number $index $kind $mode $r)
cs 8321 0 2 1 (0)
cs 8322 1 2 1 (0)
cs 8323 2 2 1 (0)
cs 8324 3 2 1 (0)
cs 8325 4 2 1 (0)
cs 8326 5 2 1 (0)
cs 8327 6 2 1 (0)
cs 8328 7 2 1 (0)
cs 8329 8 2 1 (0)
cs 8330 9 2 1 (0)
cs 8331 10 2 1 (0)
cs 8332 11 2 1 (0)
cs 8333 12 2 1 (0)
cs 8334 13 2 1 (0)
cs 8335 14 2 1 (0)
cs 8336 15 2 1 (0)
cs 8337 16 2 1 (0)
cs 8338 17 2 1 (0)
cs 8339 18 2 1 (0)
cs 8340 19 2 1 (0)
cs 8341 20 2 1 (0)
cs 8342 21 2 1 (0)
cs 8343 22 2 1 (0)
cs 8344 23 2 1 (0)
cs 8345 24 2 1 (0)
cs 8346 25 2 1 (0)
cs 8347 26 2 1 (0)
cs 8348 27 2 1 (0)
cs 8349 28 2 1 (0)
cs 8350 29 2 1 (0)
cs 8351 30 2 1 (0)
cs 8352 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08321_08352
