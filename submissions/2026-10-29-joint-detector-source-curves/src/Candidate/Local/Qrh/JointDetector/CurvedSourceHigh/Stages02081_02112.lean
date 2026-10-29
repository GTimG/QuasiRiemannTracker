/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages02081_02112
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages02081_02112
namespace Qrh.JointDetector.CurvedSourceHigh.Stages02081_02112
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages02081_02112 Qrh.JointDetector.CurvedSourceFractions.Stages02081_02112 $number $index $kind $mode $r)
cs 2081 0 2 1 (0)
cs 2082 1 2 1 (0)
cs 2083 2 2 1 (0)
cs 2084 3 2 1 (0)
cs 2085 4 2 1 (0)
cs 2086 5 2 1 (0)
cs 2087 6 2 1 (0)
cs 2088 7 2 1 (0)
cs 2089 8 2 1 (0)
cs 2090 9 2 1 (0)
cs 2091 10 2 1 (0)
cs 2092 11 2 1 (0)
cs 2093 12 2 1 (0)
cs 2094 13 2 1 (0)
cs 2095 14 2 1 (0)
cs 2096 15 2 1 (0)
cs 2097 16 2 1 (0)
cs 2098 17 2 1 (0)
cs 2099 18 2 1 (0)
cs 2100 19 2 1 (0)
cs 2101 20 2 1 (0)
cs 2102 21 2 1 (0)
cs 2103 22 2 1 (0)
cs 2104 23 2 1 (0)
cs 2105 24 2 1 (0)
cs 2106 25 2 1 (0)
cs 2107 26 2 1 (0)
cs 2108 27 2 1 (0)
cs 2109 28 2 1 (0)
cs 2110 29 2 1 (0)
cs 2111 30 2 1 (0)
cs 2112 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages02081_02112
