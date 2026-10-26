import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.Data

set_option autoImplicit false
set_option maxRecDepth 100000

namespace QRH.RepeatedMarks.Faceless

def tree_p3_high_1_01 : IPoly.UTreeI :=
  (.leaf [[(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)]])

theorem p3_high_1_01 : certI (piece3.highU (piece3.endP 1) (0, 1)) tree_p3_high_1_01 = true := by
  decide +kernel

end QRH.RepeatedMarks.Faceless
