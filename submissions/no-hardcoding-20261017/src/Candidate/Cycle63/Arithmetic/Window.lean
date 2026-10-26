/- The plain-length window of Collet's affine moment and the slot width that the old capacity
allows below it. Released under Apache 2.0. -/
import Mathlib.Tactic
import Candidate.Cycle63.Optimization.Slacks

set_option autoImplicit false

namespace Cycle63.CountAffine

noncomputable section

/-- Upper end of the plain window used with the affine moment. -/
def plainTop : ℝ := 264/625

/-- Lower end of the plain window of the affine moment. -/
def windowBottom : ℝ := 41/100

/-- Upper end of the plain lengths in Collet's affine moment. -/
def plainLengthTop : ℝ := 44/100

theorem windowBottom_pos : 0 < windowBottom := by norm_num [windowBottom]

/-- The first comparison length `M/4` lies below the plain lengths of the moment. -/
theorem quarter_le_windowBottom : 1/4 ≤ windowBottom := by norm_num [windowBottom]

/-- The plain window of the capacity argument lies inside the plain lengths of the moment. -/
theorem plainTop_le_plainLengthTop : plainTop ≤ plainLengthTop := by
  norm_num [plainTop, plainLengthTop]

end

end Cycle63.CountAffine

namespace Cycle63.Physical

noncomputable section

/-- The largest slot width for which the old capacity `n1 + n2 + (9/2) z ≤ 1` holds when the plain
lengths lie below the window, `n1 ≤ windowBottom` and `n2 ≤ plainTop`. -/
def smallPlainCap : ℝ := (1 - CountAffine.windowBottom - CountAffine.plainTop)/(9/2)

/-- Below the windows the old capacity holds: two plain lengths at the plain top and a slot sum at
the window bottom fit in `n1 + n2 + (9/2) z ≤ 1`. -/
theorem small_slot_complement :
    (2 : ℝ) * CountAffine.plainTop + (9 / 2) * Cycle63.Optimization.slotFloor ≤ 1 := by
  norm_num [CountAffine.plainTop, Cycle63.Optimization.slotFloor]

/-- The share of a width `M` left for the padding in the comparison branch of Collet's moment,
after the lengths `M/4` and `M/2` and the slot capacity `(9/2) slotTop M`. -/
def comparisonPadding : ℝ := 1/4 - (9/2)*Cycle63.Optimization.slotTop

/-- The padding share covers the padding `M/100` of the comparison branch. -/
theorem comparisonPadding_ge : 1/100 ≤ comparisonPadding := by
  norm_num [comparisonPadding, Cycle63.Optimization.slotTop]

end

end Cycle63.Physical
