/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages16001_16032
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages16001_16032
namespace Qrh.JointDetector.CurvedSourceHigh.Stages16001_16032
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages16001_16032 Qrh.JointDetector.CurvedSourceFractions.Stages16001_16032 $number $index $kind $mode $r)
cs 16001 0 1 0 (1)
cs 16002 1 1 0 (1)
cs 16003 2 1 0 (1)
cs 16004 3 1 0 (1)
cs 16005 4 1 0 (1)
cs 16006 5 1 0 (1)
cs 16007 6 1 0 (1)
cs 16008 7 1 0 (1)
cs 16009 8 1 0 (1)
cs 16010 9 1 0 (1)
cs 16011 10 1 0 (1)
cs 16012 11 1 0 (1)
cs 16013 12 1 0 (1)
cs 16014 13 1 0 (1)
cs 16015 14 1 0 (1)
cs 16016 15 1 0 (1)
cs 16017 16 1 0 (1)
cs 16018 17 1 0 (1)
cs 16019 18 1 0 (1)
cs 16020 19 1 0 (1)
cs 16021 20 1 0 (1)
cs 16022 21 1 0 (1)
cs 16023 22 1 0 (1)
cs 16024 23 1 0 (1)
cs 16025 24 1 0 (1)
cs 16026 25 1 0 (1)
cs 16027 26 1 0 (1)
cs 16028 27 1 0 (1)
cs 16029 28 1 0 (1)
cs 16030 29 1 0 (1)
cs 16031 30 1 0 (1)
cs 16032 31 1 0 (1)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages16001_16032
