/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages08705_08736
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages08705_08736
namespace Qrh.JointDetector.CurvedSourceHigh.Stages08705_08736
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages08705_08736 Qrh.JointDetector.CurvedSourceFractions.Stages08705_08736 $number $index $kind $mode $r)
cs 8705 0 2 1 (0)
cs 8706 1 2 1 (0)
cs 8707 2 2 1 (0)
cs 8708 3 2 1 (0)
cs 8709 4 2 1 (0)
cs 8710 5 2 1 (0)
cs 8711 6 2 1 (0)
cs 8712 7 2 1 (0)
cs 8713 8 2 1 (0)
cs 8714 9 2 1 (0)
cs 8715 10 2 1 (0)
cs 8716 11 2 1 (0)
cs 8717 12 2 1 (0)
cs 8718 13 2 1 (0)
cs 8719 14 2 1 (0)
cs 8720 15 2 1 (0)
cs 8721 16 2 1 (0)
cs 8722 17 2 1 (0)
cs 8723 18 2 1 (0)
cs 8724 19 2 1 (0)
cs 8725 20 2 1 (0)
cs 8726 21 2 1 (0)
cs 8727 22 2 1 (0)
cs 8728 23 2 1 (0)
cs 8729 24 2 1 (0)
cs 8730 25 2 1 (0)
cs 8731 26 2 1 (0)
cs 8732 27 2 1 (0)
cs 8733 28 2 1 (0)
cs 8734 29 2 1 (0)
cs 8735 30 2 1 (0)
cs 8736 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages08705_08736
