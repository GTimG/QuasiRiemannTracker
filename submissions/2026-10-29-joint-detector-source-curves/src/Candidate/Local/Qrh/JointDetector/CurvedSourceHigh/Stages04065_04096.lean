/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04065_04096
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04065_04096
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04065_04096
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04065_04096 Qrh.JointDetector.CurvedSourceFractions.Stages04065_04096 $number $index $kind $mode $r)
cs 4065 0 2 1 (0)
cs 4066 1 2 1 (0)
cs 4067 2 2 1 (0)
cs 4068 3 2 1 (0)
cs 4069 4 2 1 (0)
cs 4070 5 2 1 (0)
cs 4071 6 2 1 (0)
cs 4072 7 2 1 (0)
cs 4073 8 2 1 (0)
cs 4074 9 2 1 (0)
cs 4075 10 2 1 (0)
cs 4076 11 2 1 (0)
cs 4077 12 2 1 (0)
cs 4078 13 2 1 (0)
cs 4079 14 2 1 (0)
cs 4080 15 2 1 (0)
cs 4081 16 2 1 (0)
cs 4082 17 2 1 (0)
cs 4083 18 2 1 (0)
cs 4084 19 2 1 (0)
cs 4085 20 2 1 (0)
cs 4086 21 2 1 (0)
cs 4087 22 2 1 (0)
cs 4088 23 2 1 (0)
cs 4089 24 2 1 (0)
cs 4090 25 2 1 (0)
cs 4091 26 2 1 (0)
cs 4092 27 2 1 (0)
cs 4093 28 2 1 (0)
cs 4094 29 2 1 (0)
cs 4095 30 2 1 (0)
cs 4096 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04065_04096
