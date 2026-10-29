/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages07009_07040
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages07009_07040
namespace Qrh.JointDetector.CurvedSourceHigh.Stages07009_07040
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages07009_07040 Qrh.JointDetector.CurvedSourceFractions.Stages07009_07040 $number $index $kind $mode $r)
cs 7009 0 2 1 (0)
cs 7010 1 2 1 (0)
cs 7011 2 2 1 (0)
cs 7012 3 2 1 (0)
cs 7013 4 2 1 (0)
cs 7014 5 2 1 (0)
cs 7015 6 2 1 (0)
cs 7016 7 2 1 (0)
cs 7017 8 2 1 (0)
cs 7018 9 2 1 (0)
cs 7019 10 2 1 (0)
cs 7020 11 2 1 (0)
cs 7021 12 2 1 (0)
cs 7022 13 2 1 (0)
cs 7023 14 2 1 (0)
cs 7024 15 2 1 (0)
cs 7025 16 2 1 (0)
cs 7026 17 2 1 (0)
cs 7027 18 2 1 (0)
cs 7028 19 2 1 (0)
cs 7029 20 2 1 (0)
cs 7030 21 2 1 (0)
cs 7031 22 2 1 (0)
cs 7032 23 2 1 (0)
cs 7033 24 2 1 (0)
cs 7034 25 2 1 (0)
cs 7035 26 2 1 (0)
cs 7036 27 2 1 (0)
cs 7037 28 2 1 (0)
cs 7038 29 2 1 (0)
cs 7039 30 2 1 (0)
cs 7040 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages07009_07040
