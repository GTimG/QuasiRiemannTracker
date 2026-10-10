import Cycle25.Assembly.HighData

namespace Cycle25
/-- A common reserve halfway across the assumed supremum gap. -/
noncomputable def weightedTarget : ℝ :=
  signal OAI.SevenEighths.HeckeZeroSupremum.beta -
    (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/2
end Cycle25
