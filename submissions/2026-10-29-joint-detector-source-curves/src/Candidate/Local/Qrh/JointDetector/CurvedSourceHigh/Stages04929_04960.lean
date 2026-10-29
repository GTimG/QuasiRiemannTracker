/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Commands
import Candidate.Local.Qrh.JointDetector.CurvedSourceGeometry.Stages04929_04960
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Stages04929_04960
namespace Qrh.JointDetector.CurvedSourceHigh.Stages04929_04960
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local macro "cs" number:num index:num kind:num mode:num r:term : command =>
  `(command| curved_stage Qrh.JointDetector.CurvedSourceGeometry.Stages04929_04960 Qrh.JointDetector.CurvedSourceFractions.Stages04929_04960 $number $index $kind $mode $r)
cs 4929 0 2 1 (0)
cs 4930 1 2 1 (0)
cs 4931 2 2 1 (0)
cs 4932 3 2 1 (0)
cs 4933 4 2 1 (0)
cs 4934 5 2 1 (0)
cs 4935 6 2 1 (0)
cs 4936 7 2 1 (0)
cs 4937 8 2 1 (0)
cs 4938 9 2 1 (0)
cs 4939 10 2 1 (0)
cs 4940 11 2 1 (0)
cs 4941 12 2 1 (0)
cs 4942 13 2 1 (0)
cs 4943 14 2 1 (0)
cs 4944 15 2 1 (0)
cs 4945 16 2 1 (0)
cs 4946 17 2 1 (0)
cs 4947 18 2 1 (0)
cs 4948 19 2 1 (0)
cs 4949 20 2 1 (0)
cs 4950 21 2 1 (0)
cs 4951 22 2 1 (0)
cs 4952 23 2 1 (0)
cs 4953 24 2 1 (0)
cs 4954 25 2 1 (0)
cs 4955 26 2 1 (0)
cs 4956 27 2 1 (0)
cs 4957 28 2 1 (0)
cs 4958 29 2 1 (0)
cs 4959 30 2 1 (0)
cs 4960 31 2 1 (0)
end
end Qrh.JointDetector.CurvedSourceHigh.Stages04929_04960
