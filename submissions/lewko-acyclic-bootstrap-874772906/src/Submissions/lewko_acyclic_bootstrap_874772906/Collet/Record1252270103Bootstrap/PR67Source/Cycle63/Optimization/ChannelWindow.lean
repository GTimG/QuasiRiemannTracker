import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.TwoLevelLedger
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The region of the LOW children of the channel ledger and the cells of its slot window. Released under Apache 2.0.
-/
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Certificate

/-- The slot price of the region into which the ledger's LOW children are deleted: the region of the second
step at the second junction. -/
def lowRegionPrice : ℝ := regionPrice secondJunction

/-- The intercept of that region. -/
def lowRegionIntercept : ℝ := regionIntercept secondJunction regionMargin

bracket lowRegionPrice_bounds (digits := 12) : lowRegionPrice unfolding *

bracket lowRegionIntercept_bounds (digits := 12) : lowRegionIntercept unfolding *

theorem slotTop_le_one : slotTop ≤ 1 := by norm_num [slotTop]

/-- The number of cells of the slot window. -/
def cellCount : ℕ := ⌈(slotTop - slotFloor)/cellMesh⌉₊

/-- The cells tile the slot window. -/
theorem cellCount_mul : (cellCount : ℝ)*cellMesh = slotTop - slotFloor := by
  unfold cellCount
  norm_num [slotTop, slotFloor, cellMesh, allowanceUnit, Nat.ceil_ofNat]

theorem one_le_cellCount : 1 ≤ cellCount := by
  have h := cellCount_mul
  have hm := cellMesh_pos
  have hpos : (0:ℝ) < cellCount := by
    by_contra hc
    have h0 : (cellCount : ℝ) ≤ 0 := not_lt.mp hc
    have : (cellCount : ℝ)*cellMesh ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0 hm.le
    unfold slotTop slotFloor at h
    linarith
  exact_mod_cast hpos

end

end Cycle63.Optimization

namespace Cycle63.Physical

noncomputable section

/-- The share of a width `M` left for the padding in the comparison branch of Collet's moment,
after the lengths `M/4` and `M/2` and the slot capacity `(9/2) slotTop M`. -/
def comparisonPadding : ℝ := 1/4 - (9/2)*Cycle63.Optimization.slotTop

/-- The padding share covers the padding `M/100` of the comparison branch. -/
theorem comparisonPadding_ge : 1/100 ≤ comparisonPadding := by
  norm_num [comparisonPadding, Cycle63.Optimization.slotTop]

end

end Cycle63.Physical

end Record1252270103Bootstrap.PR67
