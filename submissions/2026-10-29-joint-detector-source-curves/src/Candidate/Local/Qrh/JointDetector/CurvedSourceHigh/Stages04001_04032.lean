/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04001_04032
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04001_04032
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04001_04032
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04001_04032 Qrh.JointDetector.CurvedSourceFractions.Stages04001_04032 $number $index $kind $mode $r)
cs 4001 0 2 1 (0)
cs 4002 1 2 1 (0)
cs 4003 2 2 1 (0)
cs 4004 3 2 1 (0)
cs 4005 4 2 1 (0)
cs 4006 5 2 1 (0)
cs 4007 6 2 1 (0)
cs 4008 7 2 1 (0)
cs 4009 8 2 1 (0)
cs 4010 9 2 1 (0)
cs 4011 10 2 1 (0)
cs 4012 11 2 1 (0)
cs 4013 12 2 1 (0)
cs 4014 13 2 1 (0)
cs 4015 14 2 1 (0)
cs 4016 15 2 1 (0)
cs 4017 16 2 1 (0)
cs 4018 17 2 1 (0)
cs 4019 18 2 1 (0)
cs 4020 19 2 1 (0)
cs 4021 20 2 1 (0)
cs 4022 21 2 1 (0)
cs 4023 22 2 1 (0)
cs 4024 23 2 1 (0)
cs 4025 24 2 1 (0)
cs 4026 25 2 1 (0)
cs 4027 26 2 1 (0)
cs 4028 27 2 1 (0)
cs 4029 28 2 1 (0)
cs 4030 29 2 1 (0)
cs 4031 30 2 1 (0)
cs 4032 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04001_04032
