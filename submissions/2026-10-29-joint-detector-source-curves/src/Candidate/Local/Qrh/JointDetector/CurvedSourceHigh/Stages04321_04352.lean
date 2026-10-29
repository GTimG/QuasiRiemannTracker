/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04321_04352
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04321_04352
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04321_04352
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04321_04352 Qrh.JointDetector.CurvedSourceFractions.Stages04321_04352 $number $index $kind $mode $r)
cs 4321 0 2 1 (0)
cs 4322 1 2 1 (0)
cs 4323 2 2 1 (0)
cs 4324 3 2 1 (0)
cs 4325 4 2 1 (0)
cs 4326 5 2 1 (0)
cs 4327 6 2 1 (0)
cs 4328 7 2 1 (0)
cs 4329 8 2 1 (0)
cs 4330 9 2 1 (0)
cs 4331 10 2 1 (0)
cs 4332 11 2 1 (0)
cs 4333 12 2 1 (0)
cs 4334 13 2 1 (0)
cs 4335 14 2 1 (0)
cs 4336 15 2 1 (0)
cs 4337 16 2 1 (0)
cs 4338 17 2 1 (0)
cs 4339 18 2 1 (0)
cs 4340 19 2 1 (0)
cs 4341 20 2 1 (0)
cs 4342 21 2 1 (0)
cs 4343 22 2 1 (0)
cs 4344 23 2 1 (0)
cs 4345 24 2 1 (0)
cs 4346 25 2 1 (0)
cs 4347 26 2 1 (0)
cs 4348 27 2 1 (0)
cs 4349 28 2 1 (0)
cs 4350 29 2 1 (0)
cs 4351 30 2 1 (0)
cs 4352 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04321_04352
