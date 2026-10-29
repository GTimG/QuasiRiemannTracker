/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages15009_15040
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages15009_15040
namespace Qrh.JointDetector.CurvedSourceHigh.Stages15009_15040
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages15009_15040 Qrh.JointDetector.CurvedSourceFractions.Stages15009_15040 $number $index $kind $mode $r)
cs 15009 0 1 0 (1)
cs 15010 1 1 0 (1)
cs 15011 2 1 0 (1)
cs 15012 3 1 0 (1)
cs 15013 4 1 0 (1)
cs 15014 5 1 0 (1)
cs 15015 6 1 0 (1)
cs 15016 7 1 0 (1)
cs 15017 8 1 0 (1)
cs 15018 9 1 0 (1)
cs 15019 10 1 0 (1)
cs 15020 11 1 0 (1)
cs 15021 12 1 0 (1)
cs 15022 13 1 0 (1)
cs 15023 14 1 0 (1)
cs 15024 15 1 0 (1)
cs 15025 16 1 0 (1)
cs 15026 17 1 0 (1)
cs 15027 18 1 0 (1)
cs 15028 19 1 0 (1)
cs 15029 20 1 0 (1)
cs 15030 21 1 0 (1)
cs 15031 22 1 0 (1)
cs 15032 23 1 0 (1)
cs 15033 24 1 0 (1)
cs 15034 25 1 0 (1)
cs 15035 26 1 0 (1)
cs 15036 27 1 0 (1)
cs 15037 28 1 0 (1)
cs 15038 29 1 0 (1)
cs 15039 30 1 0 (1)
cs 15040 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages15009_15040
