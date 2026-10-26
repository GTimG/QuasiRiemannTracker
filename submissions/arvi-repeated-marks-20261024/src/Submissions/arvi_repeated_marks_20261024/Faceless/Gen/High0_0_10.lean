import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.Data

set_option autoImplicit false
set_option maxRecDepth 100000

namespace QRH.RepeatedMarks.Faceless

def tree_p0_high_0_10 : IPoly.UTreeI :=
  (.leaf [[(0, 0)], [(0, 0)], [(0, 0)], [(0, 2), (1, 2), (1, 1)], [(0, 0)], [(0, 0)], [(0, 1), (1, 1)], [(0, 2), (1, 2), (1, 1)], [(0, 0)], [(0, 0)], [(0, 1), (1, 1)], [(0, 2), (1, 2), (1, 1)], [(0, 0)], [(0, 0)], [(0, 1), (1, 1)], [(0, 2), (1, 2), (1, 1)]])

theorem p0_high_0_10 : certI (piece0.highU (piece0.endP 0) (1, 0)) tree_p0_high_0_10 = true := by
  decide +kernel

end QRH.RepeatedMarks.Faceless
