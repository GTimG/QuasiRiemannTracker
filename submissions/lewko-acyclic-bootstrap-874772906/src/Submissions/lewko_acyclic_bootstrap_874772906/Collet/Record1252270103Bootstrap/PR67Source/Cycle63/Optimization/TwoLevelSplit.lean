import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.TwoLevelHigh
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The per-cell inequalities of the split of the first step's LOW children at the two-level ledger: the overshoot of
the zero-extraction child is positive, and the direct deletion has room. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Certificate

/-! A LOW child of the first step in the cell `b` that is neither in the old region after the fixed deletion, nor
reflected into it, nor wide enough for the second step, is deleted directly into the old region at the price
`directDeletionRate = q₀/(6κ)` per unit of overshoot (branch D). Its reserve is at least
`κ_q (2v - (1 - 6a₁)) - D₀(b) - L` for a width reduction `v > 1 - 6a₁ - M*`, where `D₀(b)` is the deficit of
that deletion at zero extraction and `L` the losses (`direct_deletion_selection`). The certificate below gives the
room `κ_q (1 - 6a₁ - 2M*) - D₀(b)` in every cell, with `M* = 2/5`. -/

/-- The least width of a child that the second step bounds. -/
def secondStepWidthFloor : ℝ := 2/5

/-- The rate of the direct deletion: the first junction over six times the slot price. -/
def directDeletionRate : ℝ := firstJunction/(6*slotPrice)

/-- The gap over the old region of the cell `b` of the first step's plane. -/
def twoLevelOldGap (b : ℝ) : ℝ := planeGap slotPrice 1 twoLevelSlope twoLevelPlaneIntercept b

/-- The deficit of the direct deletion of the zero-extraction child of the cell `b`. -/
def directDeletionDeficit (b : ℝ) : ℝ :=
  directDeletionRate*(twoLevelOldGap b + 6*firstAmp b) - firstAmp b

/-- The room of the direct deletion in the cell `b`: the rate times the width below `1 - 6a₁` at twice the least
second-step width, less the deficit. -/
def directDeletionRoom (b : ℝ) : ℝ :=
  directDeletionRate*(1 - 6*firstAmp b - 2*secondStepWidthFloor) - directDeletionDeficit b

/-- The least room of the direct deletion over the cells of the window. -/
def directDeletionMargin : ℝ := min (directDeletionRoom firstCellTop) (directDeletionRoom slotTop)

bracket childOvershootFirst_enclosure (digits := 9) : childOvershoot firstCellTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [childOvershoot, twoLevelSlope, twoLevelPlaneIntercept, fixedDeletion, firstAmp, planeTotalLength,
    regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio, twoLevelPrice, twoLevelIntercept,
    regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density, regionMargin, allowanceUnit,
    lowReserveWeight, slotPrice, betaBound, secondJunction, firstJunction, firstCellTop, slotFloor, cellMesh]

bracket childOvershootTop_enclosure (digits := 9) : childOvershoot slotTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [childOvershoot, twoLevelSlope, twoLevelPlaneIntercept, fixedDeletion, firstAmp, planeTotalLength,
    regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio, twoLevelPrice, twoLevelIntercept,
    regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density, regionMargin, allowanceUnit,
    lowReserveWeight, slotPrice, betaBound, secondJunction, firstJunction, slotTop]

bracket directDeletionRoomFirst_enclosure (digits := 9) : directDeletionRoom firstCellTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [directDeletionRoom, directDeletionDeficit, directDeletionRate, secondStepWidthFloor, twoLevelOldGap,
    twoLevelSlope, twoLevelPlaneIntercept, firstAmp, planeGap, planeAmplifier, amplifierRatio, twoLevelPrice,
    twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density, regionMargin,
    allowanceUnit, lowReserveWeight, slotPrice, betaBound, secondJunction, firstJunction, firstCellTop, slotFloor,
    cellMesh]

bracket directDeletionRoomTop_enclosure (digits := 9) : directDeletionRoom slotTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [directDeletionRoom, directDeletionDeficit, directDeletionRate, secondStepWidthFloor, twoLevelOldGap,
    twoLevelSlope, twoLevelPlaneIntercept, firstAmp, planeGap, planeAmplifier, amplifierRatio, twoLevelPrice,
    twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density, regionMargin,
    allowanceUnit, lowReserveWeight, slotPrice, betaBound, secondJunction, firstJunction, slotTop]

/-- The overshoot of the zero-extraction child is affine in the cell. -/
theorem childOvershoot_affine (x : ℝ) :
    childOvershoot x = childOvershoot 0 + (childOvershoot 1 - childOvershoot 0)*x := by
  unfold childOvershoot fixedDeletion firstAmp planeTotalLength regionDeletion planeGap planeAmplifier oldOvershoot
  ring

/-- The room of the direct deletion is affine in the cell. -/
theorem directDeletionRoom_affine (x : ℝ) :
    directDeletionRoom x = directDeletionRoom 0 + (directDeletionRoom 1 - directDeletionRoom 0)*x := by
  unfold directDeletionRoom directDeletionDeficit twoLevelOldGap firstAmp planeGap planeAmplifier
  ring

/-- In every cell of the window the zero-extraction child overshoots the old region after the fixed deletion, so
the second step has work to do. -/
theorem childOvershoot_pos {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) : 0 < childOvershoot b := by
  have h := min_le_of_affine (f := childOvershoot) childOvershoot_affine hb.1 hb.2
  have h₁ := childOvershootFirst_enclosure
  have h₂ := childOvershootTop_enclosure
  exact lt_of_lt_of_le (lt_min (by linarith [h₁.1]) (by linarith [h₂.1])) h

/-- The least room of the direct deletion is positive. -/
theorem directDeletionMargin_pos : 0 < directDeletionMargin := by
  have h₁ := directDeletionRoomFirst_enclosure
  have h₂ := directDeletionRoomTop_enclosure
  unfold directDeletionMargin
  exact lt_min (by linarith [h₁.1]) (by linarith [h₂.1])

/-- In every cell of the window the direct deletion has room at least `directDeletionMargin`. -/
theorem directDeletion_certificate {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) :
    directDeletionMargin ≤ directDeletionRoom b :=
  min_le_of_affine (f := directDeletionRoom) directDeletionRoom_affine hb.1 hb.2

end

end Cycle63.Optimization

end Record1252270103Bootstrap.PR67
