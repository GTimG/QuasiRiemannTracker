import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.Data

set_option autoImplicit false
set_option maxRecDepth 100000

namespace QRH.RepeatedMarks.Faceless

def tree_p3_high_0_11 : IPoly.UTreeI :=
  (.leaf [[(0, 0)], [(0, 1), (1, 1)], [(0, 1), (1, 1)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)]])

theorem p3_high_0_11 : certI (piece3.highU (piece3.endP 0) (1, 1)) tree_p3_high_0_11 = true := by
  decide +kernel

end QRH.RepeatedMarks.Faceless
