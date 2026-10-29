/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages12001_12032
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages12001_12032
namespace Qrh.JointDetector.CurvedSourceHigh.Stages12001_12032
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages12001_12032 Qrh.JointDetector.CurvedSourceFractions.Stages12001_12032 $number $index $kind $mode $r)
cs 12001 0 2 1 (0)
cs 12002 1 2 1 (0)
cs 12003 2 2 1 (0)
cs 12004 3 2 1 (0)
cs 12005 4 2 1 (0)
cs 12006 5 2 1 (0)
cs 12007 6 2 1 (0)
cs 12008 7 2 1 (0)
cs 12009 8 2 1 (0)
cs 12010 9 2 1 (0)
cs 12011 10 2 1 (0)
cs 12012 11 2 1 (0)
cs 12013 12 2 1 (0)
cs 12014 13 2 1 (0)
cs 12015 14 2 1 (0)
cs 12016 15 2 1 (0)
cs 12017 16 2 1 (0)
cs 12018 17 2 1 (0)
cs 12019 18 2 1 (0)
cs 12020 19 2 1 (0)
cs 12021 20 2 1 (0)
cs 12022 21 2 1 (0)
cs 12023 22 2 1 (0)
cs 12024 23 2 1 (0)
cs 12025 24 2 1 (0)
cs 12026 25 2 1 (0)
cs 12027 26 2 1 (0)
cs 12028 27 2 1 (0)
cs 12029 28 2 1 (0)
cs 12030 29 2 1 (0)
cs 12031 30 2 1 (0)
cs 12032 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages12001_12032
