/- The price of the region of the second step is below the slot price of the old region, so the LOW rate of the first
step of the two-level ledger exceeds the rate at the slot price. Released under Apache 2.0. -/
import Candidate.Cycle63.Optimization.TwoLevelHigh

set_option autoImplicit false

namespace Cycle63.Optimization

noncomputable section

/-- The second junction lies below the slot price. -/
theorem secondJunction_lt_slotPrice : secondJunction < slotPrice := by
  linarith [secondJunction_mem.2, slotPrice_mem.1]

/-- The second junction is positive. -/
theorem secondJunction_pos : 0 < secondJunction := by
  linarith [secondJunction_mem.1]

/-- The amplifier cost at the second junction is positive. -/
theorem amplifierCost_secondJunction_pos : 0 < amplifierCost secondJunction := by
  have h1 := secondJunction_mem.1
  have h2 := secondJunction_mem.2
  have hden : 0 < 3 * (5 - 2 * secondJunction) := by linarith
  have hx : 1 / 6 < 10 * secondJunction / (3 * (5 - 2 * secondJunction)) := by
    rw [lt_div_iff₀ hden]
    linarith
  unfold amplifierCost density
  linarith

/-- The ratio of the LOW overshoot to the HIGH reserve at the second junction is positive. -/
theorem secondRatio_secondJunction_pos : 0 < secondRatio secondJunction := by
  unfold secondRatio
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr secondJunction_lt_slotPrice))
    (mul_pos secondJunction_pos amplifierCost_secondJunction_pos)

/-- The slope of the region of the second step is positive and below `6 slotPrice - 1`. -/
theorem regionSlope_secondJunction_bounds :
    0 < regionSlope secondJunction ∧ regionSlope secondJunction < 6 * slotPrice - 1 := by
  have hκ : 0 < 6 * slotPrice - 1 := by linarith [slotPrice_mem.1]
  have hR : 0 < secondRatio secondJunction * secondJunction :=
    mul_pos secondRatio_secondJunction_pos secondJunction_pos
  unfold regionSlope
  exact ⟨div_pos hκ (by linarith), div_lt_self hκ (by linarith)⟩

/-- The slot price of the region of the second step is positive. -/
theorem twoLevelPrice_pos : 0 < twoLevelPrice := by
  unfold twoLevelPrice regionPrice
  linarith [regionSlope_secondJunction_bounds.1]

/-- The slot price of the region of the second step is below the slot price of the old region. -/
theorem twoLevelPrice_lt_slotPrice : twoLevelPrice < slotPrice := by
  unfold twoLevelPrice regionPrice
  linarith [regionSlope_secondJunction_bounds.2]

/-- The LOW rate of the first step of the two-level ledger, at the price of the region of the second step, exceeds the
rate at the slot price. -/
theorem firstJunction_div_slotPrice_lt :
    firstJunction / (6 * slotPrice) < firstJunction / (6 * twoLevelPrice) := by
  have hq : 0 < firstJunction := by linarith [firstJunction_mem.1]
  exact div_lt_div_of_pos_left hq (by linarith [twoLevelPrice_pos]) (by linarith [twoLevelPrice_lt_slotPrice])

end

end Cycle63.Optimization
