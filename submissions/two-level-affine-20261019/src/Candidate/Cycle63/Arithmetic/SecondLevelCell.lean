/- The cell of a state in the ledger of the second step at a grid position: the single cell of the slot window, with the
amplifier and the total length of the position. Released under Apache 2.0. -/
import Candidate.Cycle63.Arithmetic.SecondLevelFamily

set_option autoImplicit false

namespace Cycle63

noncomputable section
open Cycle63.Optimization

variable (N : ℕ) (i : SecondIndex N)

/-- The LOW children of the ledger of the second step at a grid position are deleted into the old region: their
price and intercept are the old region's. -/
theorem secondFamily_deletesIntoOldRegion : @AffineLedger.DeletesIntoOldRegion (secondFamily N i) :=
  @AffineLedger.DeletesIntoOldRegion.mk (secondFamily N i) rfl rfl

/-- A slot length in the window of the ledger at a grid position selects its single cell. -/
theorem secondFamily_originalCell {z : ℝ}
    (hz : (gridPosition N i.1).slotTop - (gridPosition N i.1).mesh ≤ z ∧ z ≤ (gridPosition N i.1).slotTop) :
    @AffineLedger.originalCell (secondFamily N i) z = 1 := by
  obtain ⟨h₁, h₂, -, -⟩ := @AffineLedger.originalCell_mem (secondFamily N i) z hz
  exact le_antisymm h₂ h₁

/-- The upper edge of the single cell of the ledger at a grid position is the top of its slot window. -/
theorem secondFamily_cellUpper_one :
    @AffineLedger.cellUpper (secondFamily N i) 1 = (gridPosition N i.1).slotTop := by
  show (gridPosition N i.1).slotTop - (gridPosition N i.1).mesh + ((1 : ℕ) : ℝ) * (gridPosition N i.1).mesh = _
  push_cast
  ring

/-- The amplifier of the cell of a slot length in the window of the ledger at a grid position is the amplifier of the
position. -/
theorem secondFamily_cell_amp {z : ℝ}
    (hz : (gridPosition N i.1).slotTop - (gridPosition N i.1).mesh ≤ z ∧ z ≤ (gridPosition N i.1).slotTop) :
    @AffineLedger.amp (secondFamily N i)
      (@AffineLedger.cellUpper (secondFamily N i) (@AffineLedger.originalCell (secondFamily N i) z)) =
      (gridPosition N i.1).amp := by
  rw [secondFamily_originalCell N i hz, secondFamily_cellUpper_one]
  rfl

/-- The bound of the total length of the cell of a slot length in the window of the ledger at a grid position is the
bound of the position. -/
theorem secondFamily_cell_totalA {z : ℝ}
    (hz : (gridPosition N i.1).slotTop - (gridPosition N i.1).mesh ≤ z ∧ z ≤ (gridPosition N i.1).slotTop) :
    @AffineLedger.totalA (secondFamily N i)
      (@AffineLedger.cellUpper (secondFamily N i) (@AffineLedger.originalCell (secondFamily N i) z)) =
      (gridPosition N i.1).totalA := by
  rw [secondFamily_originalCell N i hz, secondFamily_cellUpper_one]
  rfl

/-- The amplifier floor of the ledger at a grid position is the amplifier of the position. -/
theorem secondFamily_amplifierFloor :
    @AffineLedger.amplifierFloor (secondFamily N i) = (gridPosition N i.1).amp := by
  have h : @AffineLedger.firstCellTop (secondFamily N i) = (gridPosition N i.1).slotTop := by
    show (gridPosition N i.1).slotTop - (gridPosition N i.1).mesh + (gridPosition N i.1).mesh = _
    ring
  show @AffineLedger.amp (secondFamily N i) (@AffineLedger.firstCellTop (secondFamily N i)) = _
  rw [h]
  rfl

/-- The amplifier of a position whose facts hold is at least the weight of the LOW reserve. -/
theorem SecondPosition.lowReserveWeight_le_amp {P : SecondPosition} (h : P.Facts) : lowReserveWeight ≤ P.amp := by
  have hK := secondAmplifierRatio_bounds
  have hamp : P.amp = amplifierRatio slotPrice 1 secondJunction * P.oldGap + lowReserveWeight := by
    unfold SecondPosition.amp SecondPosition.oldGap planeAmplifier planeGap
    rfl
  rw [hamp]
  have hK0 : 0 ≤ amplifierRatio slotPrice 1 secondJunction := by linarith [hK.1]
  nlinarith [mul_nonneg hK0 h.oldGap_pos.le]

/-- The amplifier floor of the ledger at every grid position is at least the weight of the LOW reserve, a positive
number that does not depend on the grid. -/
theorem lowReserveWeight_le_secondFamily_amplifierFloor :
    lowReserveWeight ≤ @AffineLedger.amplifierFloor (secondFamily N i) := by
  rw [secondFamily_amplifierFloor]
  exact SecondPosition.lowReserveWeight_le_amp i.2

/-- The LOW reserve of the ledger at every grid position is at least `10⁻¹⁰`: it is the reserve of the old region at
the second junction, `lowReserveWeight (1 - secondJunction/slotPrice)`, the same at every position. -/
theorem secondFamily_lowReserve_ge : 1/10^10 ≤ @AffineLedger.lowReserve (secondFamily N i) := by
  show 1/10^10 ≤ lowReserveAt slotPrice 1 secondJunction
  have hw : lowReserveWeight = 1/100000000 := by norm_num [lowReserveWeight, allowanceUnit]
  have hk := slotPrice_bounds
  have hq := secondJunction_mem
  unfold lowReserveAt
  rw [hw, mul_one, mul_sub, mul_one, ← mul_div_assoc]
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by linarith [hk.1])]
  nlinarith [hq.2, hk.1]

end

end Cycle63
