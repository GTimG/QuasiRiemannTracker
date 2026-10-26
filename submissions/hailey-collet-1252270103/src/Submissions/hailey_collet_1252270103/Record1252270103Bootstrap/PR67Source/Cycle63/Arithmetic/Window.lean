import Mathlib.Tactic
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.Slacks
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The plain-length window of Collet's affine moment and the slot width that the old capacity
allows below it. Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.CountAffine

noncomputable section

/-- Upper end of the plain window used with the affine moment. -/
def plainTop : ℝ := 264/625

/-- Lower end of the plain window of the affine moment. The bound does not depend on it: any window
bottom from `1/4` up to the one at which the junction row `dMinus` reaches the row length `h`
(about `0.4096` at the computed plane) meets every gate. -/
def windowBottom : ℝ := 81/200

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

end

end Cycle63.Physical

end Record1252270103Bootstrap.PR67
