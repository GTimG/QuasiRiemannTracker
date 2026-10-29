/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08001_08032
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08001_08032
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08001_08032
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08001_08032 Qrh.JointDetector.CurvedSourceFractions.Stages08001_08032 $number $index $kind $mode $r)
cs 8001 0 2 1 (0)
cs 8002 1 2 1 (0)
cs 8003 2 2 1 (0)
cs 8004 3 2 1 (0)
cs 8005 4 2 1 (0)
cs 8006 5 2 1 (0)
cs 8007 6 2 1 (0)
cs 8008 7 2 1 (0)
cs 8009 8 2 1 (0)
cs 8010 9 2 1 (0)
cs 8011 10 2 1 (0)
cs 8012 11 2 1 (0)
cs 8013 12 2 1 (0)
cs 8014 13 2 1 (0)
cs 8015 14 2 1 (0)
cs 8016 15 2 1 (0)
cs 8017 16 2 1 (0)
cs 8018 17 2 1 (0)
cs 8019 18 2 1 (0)
cs 8020 19 2 1 (0)
cs 8021 20 2 1 (0)
cs 8022 21 2 1 (0)
cs 8023 22 2 1 (0)
cs 8024 23 2 1 (0)
cs 8025 24 2 1 (0)
cs 8026 25 2 1 (0)
cs 8027 26 2 1 (0)
cs 8028 27 2 1 (0)
cs 8029 28 2 1 (0)
cs 8030 29 2 1 (0)
cs 8031 30 2 1 (0)
cs 8032 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08001_08032
