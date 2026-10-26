import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.Data

set_option autoImplicit false
set_option maxRecDepth 100000

namespace QRH.RepeatedMarks.Faceless

def tree_p4_high_1_00 : IPoly.UTreeI :=
  (.leaf [[(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)], [(0, 0)]])

theorem p4_high_1_00 : certI (piece4.highU (piece4.endP 1) (0, 0)) tree_p4_high_1_00 = true := by
  decide +kernel

end QRH.RepeatedMarks.Faceless
