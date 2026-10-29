/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages02145_02176
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages02145_02176
namespace Qrh.JointDetector.CurvedSourceHigh.Stages02145_02176
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages02145_02176 Qrh.JointDetector.CurvedSourceFractions.Stages02145_02176 $number $index $kind $mode $r)
cs 2145 0 2 1 (0)
cs 2146 1 2 1 (0)
cs 2147 2 2 1 (0)
cs 2148 3 2 1 (0)
cs 2149 4 2 1 (0)
cs 2150 5 2 1 (0)
cs 2151 6 2 1 (0)
cs 2152 7 2 1 (0)
cs 2153 8 2 1 (0)
cs 2154 9 2 1 (0)
cs 2155 10 2 1 (0)
cs 2156 11 2 1 (0)
cs 2157 12 2 1 (0)
cs 2158 13 2 1 (0)
cs 2159 14 2 1 (0)
cs 2160 15 2 1 (0)
cs 2161 16 2 1 (0)
cs 2162 17 2 1 (0)
cs 2163 18 2 1 (0)
cs 2164 19 2 1 (0)
cs 2165 20 2 1 (0)
cs 2166 21 2 1 (0)
cs 2167 22 2 1 (0)
cs 2168 23 2 1 (0)
cs 2169 24 2 1 (0)
cs 2170 25 2 1 (0)
cs 2171 26 2 1 (0)
cs 2172 27 2 1 (0)
cs 2173 28 2 1 (0)
cs 2174 29 2 1 (0)
cs 2175 30 2 1 (0)
cs 2176 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages02145_02176
