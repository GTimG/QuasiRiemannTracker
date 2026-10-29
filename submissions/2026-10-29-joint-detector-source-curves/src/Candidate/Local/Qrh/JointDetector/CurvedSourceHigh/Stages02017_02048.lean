/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages02017_02048
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages02017_02048
namespace Qrh.JointDetector.CurvedSourceHigh.Stages02017_02048
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages02017_02048 Qrh.JointDetector.CurvedSourceFractions.Stages02017_02048 $number $index $kind $mode $r)
cs 2017 0 2 1 (0)
cs 2018 1 2 1 (0)
cs 2019 2 2 1 (0)
cs 2020 3 2 1 (0)
cs 2021 4 2 1 (0)
cs 2022 5 2 1 (0)
cs 2023 6 2 1 (0)
cs 2024 7 2 1 (0)
cs 2025 8 2 1 (0)
cs 2026 9 2 1 (0)
cs 2027 10 2 1 (0)
cs 2028 11 2 1 (0)
cs 2029 12 2 1 (0)
cs 2030 13 2 1 (0)
cs 2031 14 2 1 (0)
cs 2032 15 2 1 (0)
cs 2033 16 2 1 (0)
cs 2034 17 2 1 (0)
cs 2035 18 2 1 (0)
cs 2036 19 2 1 (0)
cs 2037 20 2 1 (0)
cs 2038 21 2 1 (0)
cs 2039 22 2 1 (0)
cs 2040 23 2 1 (0)
cs 2041 24 2 1 (0)
cs 2042 25 2 1 (0)
cs 2043 26 2 1 (0)
cs 2044 27 2 1 (0)
cs 2045 28 2 1 (0)
cs 2046 29 2 1 (0)
cs 2047 30 2 1 (0)
cs 2048 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages02017_02048
