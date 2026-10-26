import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.SecondLevelLedger
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.TwoLevelSplit
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The position of the second step for a first-level LOW child on a grid, and the facts of its ledger from the
conditions of the second step's branch. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Certificate

/-! A first-level LOW child of the cell `b` with width `M₁` goes to the second step when it overshoots the old
region, is not reflected into it, and has width at least `2/5`. In units of its width its plain lengths are `n₁, n₂`
and its slot length is `ζ`. Its position rounds these to a grid of mesh `g`: the plane's intercept and the slot
length up, the plain floors down. The facts of the position follow from five inequalities of the child: its
overshoot `n₁ + n₂ + 6κζ - 1` over the old region is positive and at most the zero-extraction child's over `M₁`; its
total length leaves at least the zero-extraction reserve `childReserve b` of the cell over `M₁` (extraction never
removes more width than length); its plain lengths differ by at most `6κζ` plus a slack `s ≤ 1/100` (it is not
reflected); it lies in the second step's region; and its slot length is at most the cell's after the fixed deletion.

The per-cell inequalities used are affine in the cell, so they are certified at the two ends of the window. -/

/-- The reserve of the zero-extraction child of the cell `b`: its width less its total length. -/
def childReserve (b : ℝ) : ℝ := 1 - 6*firstAmp b - twoLevelTotalA b + fixedDeletion b

/-- The largest normalized slot length of a child of the cell `b` of width at least `2/5`. -/
def childSlotCap (b : ℝ) : ℝ := (b - fixedDeletion b)/secondStepWidthFloor

/-- The slack of the balance of the plain lengths that the certificates allow. -/
def positionSlack : ℝ := 1/100

/-- The slack of the grid rounding and of the overshoot padding that the certificates allow. -/
def gridSlack : ℝ := 1/100000

/-- The floor of the shorter plain length of a child of the cell `b`. -/
def childShortFloor (b : ℝ) : ℝ := 1/2 - 6*slotPrice*childSlotCap b - positionSlack/2 - gridSlack

/-- The floor of the plain sum less the comparison's slot capacity and padding for a child of the cell `b`. -/
def childComparisonFloor (b : ℝ) : ℝ :=
  (1 - 6*slotPrice*childSlotCap b - gridSlack) - (9/2)*(childSlotCap b + gridSlack) - 1/100

/-- The fixed-inducing room against the plain loss of the short plain length. -/
def fixedShortRoom (b : ℝ) : ℝ := childReserve b - 4*secondAmp b - (1/50 + 2/3*(1/4 - childShortFloor b))

/-- The fixed-inducing room against the plain loss of the comparison length. -/
def fixedComparisonRoom (b : ℝ) : ℝ :=
  childReserve b - 4*secondAmp b - (1/50 + 2/3*(1/4 - childComparisonFloor b/2))

/-- The exceptional room against the plain loss of the short plain length. -/
def exceptionalShortRoom (b : ℝ) : ℝ :=
  childReserve b - (9/2)*secondAmp b - (1/50 + 2/3*(1/4 - childShortFloor b))

/-- The exceptional room against the plain loss of the comparison length. -/
def exceptionalComparisonRoom (b : ℝ) : ℝ :=
  childReserve b - (9/2)*secondAmp b - (1/50 + 2/3*(1/4 - childComparisonFloor b/2))

/-- The room of the second zero. -/
def zeroRoom (b : ℝ) : ℝ := childReserve b - 6*secondAmp b - (1/380 + 1/20)

bracket fixedShortRoomFirst_enclosure (digits := 6) : fixedShortRoom firstCellTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [fixedShortRoom, childReserve, childSlotCap, childShortFloor, childComparisonFloor, positionSlack, gridSlack,
    secondStepWidthFloor, secondAmp, childOvershoot, twoLevelTotalA, fixedDeletion, firstAmp, twoLevelSlope,
    twoLevelPlaneIntercept, planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio,
    twoLevelPrice, twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density,
    regionMargin, allowanceUnit, lowReserveWeight, cellMesh, slotPrice, betaBound, secondJunction, firstJunction,
    firstCellTop, slotFloor]

bracket fixedShortRoomTop_enclosure (digits := 6) : fixedShortRoom slotTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [fixedShortRoom, childReserve, childSlotCap, childShortFloor, childComparisonFloor, positionSlack, gridSlack,
    secondStepWidthFloor, secondAmp, childOvershoot, twoLevelTotalA, fixedDeletion, firstAmp, twoLevelSlope,
    twoLevelPlaneIntercept, planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio,
    twoLevelPrice, twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density,
    regionMargin, allowanceUnit, lowReserveWeight, cellMesh, slotPrice, betaBound, secondJunction, firstJunction,
    slotTop]

bracket fixedComparisonRoomFirst_enclosure (digits := 6) : fixedComparisonRoom firstCellTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [fixedComparisonRoom, childReserve, childSlotCap, childShortFloor, childComparisonFloor, positionSlack, gridSlack,
    secondStepWidthFloor, secondAmp, childOvershoot, twoLevelTotalA, fixedDeletion, firstAmp, twoLevelSlope,
    twoLevelPlaneIntercept, planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio,
    twoLevelPrice, twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density,
    regionMargin, allowanceUnit, lowReserveWeight, cellMesh, slotPrice, betaBound, secondJunction, firstJunction,
    firstCellTop, slotFloor]

bracket fixedComparisonRoomTop_enclosure (digits := 6) : fixedComparisonRoom slotTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [fixedComparisonRoom, childReserve, childSlotCap, childShortFloor, childComparisonFloor, positionSlack, gridSlack,
    secondStepWidthFloor, secondAmp, childOvershoot, twoLevelTotalA, fixedDeletion, firstAmp, twoLevelSlope,
    twoLevelPlaneIntercept, planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio,
    twoLevelPrice, twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density,
    regionMargin, allowanceUnit, lowReserveWeight, cellMesh, slotPrice, betaBound, secondJunction, firstJunction,
    slotTop]

bracket exceptionalShortRoomFirst_enclosure (digits := 6) : exceptionalShortRoom firstCellTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [exceptionalShortRoom, childReserve, childSlotCap, childShortFloor, childComparisonFloor, positionSlack, gridSlack,
    secondStepWidthFloor, secondAmp, childOvershoot, twoLevelTotalA, fixedDeletion, firstAmp, twoLevelSlope,
    twoLevelPlaneIntercept, planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio,
    twoLevelPrice, twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density,
    regionMargin, allowanceUnit, lowReserveWeight, cellMesh, slotPrice, betaBound, secondJunction, firstJunction,
    firstCellTop, slotFloor]

bracket exceptionalShortRoomTop_enclosure (digits := 6) : exceptionalShortRoom slotTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [exceptionalShortRoom, childReserve, childSlotCap, childShortFloor, childComparisonFloor, positionSlack, gridSlack,
    secondStepWidthFloor, secondAmp, childOvershoot, twoLevelTotalA, fixedDeletion, firstAmp, twoLevelSlope,
    twoLevelPlaneIntercept, planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio,
    twoLevelPrice, twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density,
    regionMargin, allowanceUnit, lowReserveWeight, cellMesh, slotPrice, betaBound, secondJunction, firstJunction,
    slotTop]

bracket exceptionalComparisonRoomFirst_enclosure (digits := 6) : exceptionalComparisonRoom firstCellTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [exceptionalComparisonRoom, childReserve, childSlotCap, childShortFloor, childComparisonFloor,
    positionSlack, gridSlack, secondStepWidthFloor, secondAmp, childOvershoot, twoLevelTotalA, fixedDeletion, firstAmp,
    twoLevelSlope, twoLevelPlaneIntercept, planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot,
    amplifierRatio, twoLevelPrice, twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio,
    amplifierCost, density, regionMargin, allowanceUnit, lowReserveWeight, cellMesh, slotPrice, betaBound,
    secondJunction, firstJunction, firstCellTop, slotFloor]

bracket exceptionalComparisonRoomTop_enclosure (digits := 6) : exceptionalComparisonRoom slotTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [exceptionalComparisonRoom, childReserve, childSlotCap, childShortFloor, childComparisonFloor,
    positionSlack, gridSlack, secondStepWidthFloor, secondAmp, childOvershoot, twoLevelTotalA, fixedDeletion, firstAmp,
    twoLevelSlope, twoLevelPlaneIntercept, planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot,
    amplifierRatio, twoLevelPrice, twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio,
    amplifierCost, density, regionMargin, allowanceUnit, lowReserveWeight, cellMesh, slotPrice, betaBound,
    secondJunction, firstJunction, slotTop]

bracket zeroRoomFirst_enclosure (digits := 6) : zeroRoom firstCellTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [zeroRoom, childReserve, childSlotCap, childShortFloor, childComparisonFloor, positionSlack, gridSlack,
    secondStepWidthFloor, secondAmp, childOvershoot, twoLevelTotalA, fixedDeletion, firstAmp, twoLevelSlope,
    twoLevelPlaneIntercept, planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio,
    twoLevelPrice, twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density,
    regionMargin, allowanceUnit, lowReserveWeight, cellMesh, slotPrice, betaBound, secondJunction, firstJunction,
    firstCellTop, slotFloor]

bracket zeroRoomTop_enclosure (digits := 6) : zeroRoom slotTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [zeroRoom, childReserve, childSlotCap, childShortFloor, childComparisonFloor, positionSlack, gridSlack,
    secondStepWidthFloor, secondAmp, childOvershoot, twoLevelTotalA, fixedDeletion, firstAmp, twoLevelSlope,
    twoLevelPlaneIntercept, planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio,
    twoLevelPrice, twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density,
    regionMargin, allowanceUnit, lowReserveWeight, cellMesh, slotPrice, betaBound, secondJunction, firstJunction,
    slotTop]

bracket childSlotCapFirst_enclosure (digits := 6) : childSlotCap firstCellTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [childReserve, childSlotCap, childShortFloor, childComparisonFloor, positionSlack, gridSlack, secondStepWidthFloor,
    secondAmp, childOvershoot, twoLevelTotalA, fixedDeletion, firstAmp, twoLevelSlope, twoLevelPlaneIntercept,
    planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio, twoLevelPrice,
    twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density, regionMargin,
    allowanceUnit, lowReserveWeight, cellMesh, slotPrice, betaBound, secondJunction, firstJunction, firstCellTop,
    slotFloor]

bracket childSlotCapTop_enclosure (digits := 6) : childSlotCap slotTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [childReserve, childSlotCap, childShortFloor, childComparisonFloor, positionSlack, gridSlack, secondStepWidthFloor,
    secondAmp, childOvershoot, twoLevelTotalA, fixedDeletion, firstAmp, twoLevelSlope, twoLevelPlaneIntercept,
    planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio, twoLevelPrice,
    twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density, regionMargin,
    allowanceUnit, lowReserveWeight, cellMesh, slotPrice, betaBound, secondJunction, firstJunction, slotTop]

/-- `fixedShortRoom` is affine in the cell. -/
theorem fixedShortRoom_affine (x : ℝ) :
    fixedShortRoom x = fixedShortRoom 0 + (fixedShortRoom 1 - fixedShortRoom 0)*x := by
  simp only [fixedShortRoom, childReserve, childShortFloor, childSlotCap, secondAmp, childOvershoot, twoLevelTotalA,
    fixedDeletion, firstAmp, planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot]
  ring

/-- `fixedComparisonRoom` is affine in the cell. -/
theorem fixedComparisonRoom_affine (x : ℝ) :
    fixedComparisonRoom x = fixedComparisonRoom 0 + (fixedComparisonRoom 1 - fixedComparisonRoom 0)*x := by
  simp only [fixedComparisonRoom, childReserve, childComparisonFloor, childSlotCap, secondAmp, childOvershoot,
    twoLevelTotalA, fixedDeletion, firstAmp, planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot]
  ring

/-- `exceptionalShortRoom` is affine in the cell. -/
theorem exceptionalShortRoom_affine (x : ℝ) :
    exceptionalShortRoom x = exceptionalShortRoom 0 + (exceptionalShortRoom 1 - exceptionalShortRoom 0)*x := by
  simp only [exceptionalShortRoom, childReserve, childShortFloor, childSlotCap, secondAmp, childOvershoot,
    twoLevelTotalA, fixedDeletion, firstAmp, planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot]
  ring

/-- `exceptionalComparisonRoom` is affine in the cell. -/
theorem exceptionalComparisonRoom_affine (x : ℝ) :
    exceptionalComparisonRoom x = exceptionalComparisonRoom 0 + (exceptionalComparisonRoom 1 - exceptionalComparisonRoom 0)*x := by
  simp only [exceptionalComparisonRoom, childReserve, childComparisonFloor, childSlotCap, secondAmp, childOvershoot,
    twoLevelTotalA, fixedDeletion, firstAmp, planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot]
  ring

/-- `zeroRoom` is affine in the cell. -/
theorem zeroRoom_affine (x : ℝ) :
    zeroRoom x = zeroRoom 0 + (zeroRoom 1 - zeroRoom 0)*x := by
  simp only [zeroRoom, childReserve, secondAmp, childOvershoot, twoLevelTotalA, fixedDeletion, firstAmp,
    planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot]
  ring

/-- `childSlotCap` is affine in the cell. -/
theorem childSlotCap_affine (x : ℝ) :
    childSlotCap x = childSlotCap 0 + (childSlotCap 1 - childSlotCap 0)*x := by
  simp only [childSlotCap, fixedDeletion, firstAmp, regionDeletion, planeGap, planeAmplifier]
  ring


end

end Cycle63.Optimization

namespace Cycle63.Optimization

noncomputable section

/-- On the window the slot cap of a child is at most `681/10000`. -/
theorem childSlotCap_le {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) : childSlotCap b ≤ 681/10000 := by
  have h := min_le_of_affine (f := fun x => -childSlotCap x)
    (fun x => by linarith [childSlotCap_affine x, childSlotCap_affine 0, childSlotCap_affine 1]) hb.1 hb.2
  have h₁ := childSlotCapFirst_enclosure
  have h₂ := childSlotCapTop_enclosure
  have hmin : -(681/10000 : ℝ) ≤ min (-childSlotCap firstCellTop) (-childSlotCap slotTop) :=
    le_min (by linarith [h₁.2]) (by linarith [h₂.2])
  linarith [hmin.trans h]

/-- On the window the slot cap of a child is at least `648/10000`. -/
theorem childSlotCap_ge {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) : 648/10000 ≤ childSlotCap b := by
  have h := min_le_of_affine (f := childSlotCap) childSlotCap_affine hb.1 hb.2
  have h₁ := childSlotCapFirst_enclosure
  have h₂ := childSlotCapTop_enclosure
  exact le_trans (le_min (by linarith [h₁.1]) (by linarith [h₂.1])) h

/-- On the window every room of the second step's position is at least `1/1000`. -/
theorem position_rooms {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) :
    1/1000 ≤ fixedShortRoom b ∧ 1/1000 ≤ fixedComparisonRoom b ∧ 1/1000 ≤ exceptionalShortRoom b ∧
      1/1000 ≤ exceptionalComparisonRoom b ∧ 1/1000 ≤ zeroRoom b := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := min_le_of_affine (f := fixedShortRoom) fixedShortRoom_affine hb.1 hb.2
    exact le_trans (le_min (by linarith [fixedShortRoomFirst_enclosure.1])
      (by linarith [fixedShortRoomTop_enclosure.1])) h
  · have h := min_le_of_affine (f := fixedComparisonRoom) fixedComparisonRoom_affine hb.1 hb.2
    exact le_trans (le_min (by linarith [fixedComparisonRoomFirst_enclosure.1])
      (by linarith [fixedComparisonRoomTop_enclosure.1])) h
  · have h := min_le_of_affine (f := exceptionalShortRoom) exceptionalShortRoom_affine hb.1 hb.2
    exact le_trans (le_min (by linarith [exceptionalShortRoomFirst_enclosure.1])
      (by linarith [exceptionalShortRoomTop_enclosure.1])) h
  · have h := min_le_of_affine (f := exceptionalComparisonRoom) exceptionalComparisonRoom_affine hb.1 hb.2
    exact le_trans (le_min (by linarith [exceptionalComparisonRoomFirst_enclosure.1])
      (by linarith [exceptionalComparisonRoomTop_enclosure.1])) h
  · have h := min_le_of_affine (f := zeroRoom) zeroRoom_affine hb.1 hb.2
    exact le_trans (le_min (by linarith [zeroRoomFirst_enclosure.1]) (by linarith [zeroRoomTop_enclosure.1])) h

end

end Cycle63.Optimization

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Certificate

bracket twoLevelIntercept_bounds (digits := 9) : twoLevelIntercept
  unfolding [twoLevelIntercept, regionIntercept, secondRatio, amplifierCost, density, regionMargin, allowanceUnit,
    slotPrice, betaBound, secondJunction]

end

end Cycle63.Optimization

namespace Cycle63

noncomputable section
open Cycle63.Optimization

/-- The grid point of mesh `g` at or above `x`. -/
def gridUp (g x : ℝ) : ℝ := (⌈x/g⌉ : ℝ)*g

/-- The grid point of mesh `g` at or below `x`. -/
def gridDown (g x : ℝ) : ℝ := (⌊x/g⌋ : ℝ)*g

theorem le_gridUp {g : ℝ} (hg : 0 < g) (x : ℝ) : x ≤ gridUp g x := by
  unfold gridUp
  calc x = (x/g)*g := by field_simp
    _ ≤ (⌈x/g⌉ : ℝ)*g := mul_le_mul_of_nonneg_right (Int.le_ceil (x/g)) hg.le

theorem gridUp_le {g : ℝ} (hg : 0 < g) (x : ℝ) : gridUp g x ≤ x + g := by
  unfold gridUp
  calc (⌈x/g⌉ : ℝ)*g ≤ (x/g + 1)*g := mul_le_mul_of_nonneg_right (Int.ceil_lt_add_one (x/g)).le hg.le
    _ = x + g := by field_simp

theorem gridDown_le {g : ℝ} (hg : 0 < g) (x : ℝ) : gridDown g x ≤ x := by
  unfold gridDown
  calc (⌊x/g⌋ : ℝ)*g ≤ (x/g)*g := mul_le_mul_of_nonneg_right (Int.floor_le (x/g)) hg.le
    _ = x := by field_simp

theorem le_gridDown {g : ℝ} (hg : 0 < g) (x : ℝ) : x - g ≤ gridDown g x := by
  unfold gridDown
  calc x - g = (x/g - 1)*g := by field_simp
    _ ≤ (⌊x/g⌋ : ℝ)*g := mul_le_mul_of_nonneg_right (by linarith [Int.lt_floor_add_one (x/g)]) hg.le

/-- A real whose product with a width in `(0, 1]` is at least a nonnegative real is itself at least that real. -/
theorem le_of_le_mul_width {N Y M : ℝ} (hN : 0 ≤ N) (hM : 0 < M) (hM₁ : M ≤ 1) (h : N ≤ Y*M) : N ≤ Y := by
  rcases le_total 0 Y with hY | hY
  · nlinarith
  · nlinarith

/-- The position of the second step for a child of plain lengths `n₁, n₂` and slot length `ζ` in units of its
width, on the grid of mesh `g`. -/
def childPosition (g n₁ n₂ ζ : ℝ) : SecondPosition where
  intercept := gridUp g (n₁ + n₂ + secondSlope*ζ)
  slotTop := gridUp g ζ
  mesh := g
  windowBottom := gridDown g (min n₁ n₂)
  sumBottom := gridDown g (n₁ + n₂)
  plainLossCap := max 0 (max (1/4 - gridDown g (min n₁ n₂))
    (1/4 - (gridDown g (n₁ + n₂) - (9/2)*gridUp g ζ - 1/100)/2))

/-- The position of a child of the cell `b` to which the second step applies has the facts of the second step's
ledger. The child has width `M₁ ∈ [2/5, 1]`, plain lengths `n₁, n₂` and slot length `ζ` in units of its width; it
overshoots the old region, by at most the zero-extraction child's overshoot plus `ω`; its total length leaves the
zero-extraction reserve up to `ω`; its plain lengths differ by at most `6κζ` plus `s`; it lies in the second step's
region up to `3ω`; and its slot length is at most the cell's after the fixed deletion. -/
theorem childPosition_facts {b M₁ n₁ n₂ ζ g s ω : ℝ}
    (hb : firstCellTop ≤ b ∧ b ≤ slotTop) (hM : 2/5 ≤ M₁ ∧ M₁ ≤ 1)
    (hg : 0 < g) (hg' : g ≤ 1/1000000) (hs' : s ≤ positionSlack) (hω : 0 ≤ ω) (hω' : ω ≤ 1/1000000)
    (hζ : 0 ≤ ζ) (hζcell : ζ*M₁ ≤ b - fixedDeletion b)
    (hover : 0 < n₁ + n₂ + 6*slotPrice*ζ - 1)
    (hoverle : (n₁ + n₂ + 6*slotPrice*ζ - 1)*M₁ ≤ childOvershoot b + ω)
    (hreserve : childReserve b ≤ (1 - (n₁ + n₂ + ζ))*M₁ + ω)
    (hbal : |n₁ - n₂| ≤ 6*slotPrice*ζ + s)
    (hregion : n₁ + n₂ + secondSlope*ζ ≤ twoLevelIntercept + 3*ω) :
    (childPosition g n₁ n₂ ζ).Facts := by
  have hκ := slotPrice_bounds
  have hlam := secondSlope_bounds
  have hK := secondAmplifierRatio_bounds
  have hI := twoLevelIntercept_bounds
  have hcap := childSlotCap_le hb
  have hcapge := childSlotCap_ge hb
  have hrooms := position_rooms hb
  have hα : lowReserveWeight = 1/100000000 := by norm_num [lowReserveWeight, allowanceUnit]
  have hps : positionSlack = 1/100 := rfl
  have hgs : gridSlack = 1/100000 := rfl
  set κ := slotPrice with hκdef
  set lam₂ := secondSlope with hlamdef
  set K := amplifierRatio slotPrice 1 secondJunction with hKdef
  set F := n₁ + n₂ + 6*κ*ζ - 1 with hFdef
  -- The child's slot length is at most the slot cap of the cell.
  have hζcap : ζ ≤ childSlotCap b := by
    unfold childSlotCap secondStepWidthFloor
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hM.1]
  have hζtop : ζ ≤ 681/10000 := hζcap.trans hcap
  have hκpos : 0 ≤ κ := by linarith [hκ.1]
  have hκζ : κ*ζ ≤ κ*childSlotCap b := mul_le_mul_of_nonneg_left hζcap hκpos
  have hκζtop : κ*ζ ≤ (3/4)*(681/10000) := mul_le_mul hκ.2 hζtop hζ (by norm_num)
  have hκcap : (37/50)*(648/10000) ≤ κ*childSlotCap b :=
    mul_le_mul hκ.1.le hcapge (by norm_num) hκpos
  -- Both plain lengths are at least half the width less the slot capacity and half the slack.
  have hb₁ := (abs_le.mp hbal).1
  have hb₂ := (abs_le.mp hbal).2
  have hmin : 1/2 - 6*κ*ζ - s/2 ≤ min n₁ n₂ := le_min (by linarith) (by linarith)
  -- The grid points of the position.
  have hu₁ := le_gridUp hg (n₁ + n₂ + lam₂*ζ)
  have hu₂ := gridUp_le hg (n₁ + n₂ + lam₂*ζ)
  have hz₁ := le_gridUp hg ζ
  have hz₂ := gridUp_le hg ζ
  have hw₁ := le_gridDown hg (min n₁ n₂)
  have hs₁ := le_gridDown hg (n₁ + n₂)
  have hslope : 0 ≤ 6*κ - lam₂ := by linarith [hκ.1, hlam.2]
  have hlam₁ : 0 ≤ lam₂ - 1 := by linarith [hlam.1]
  have hp₁ : (6*κ - lam₂)*ζ ≤ (6*κ - lam₂)*gridUp g ζ := mul_le_mul_of_nonneg_left hz₁ hslope
  have hp₂ : (6*κ - lam₂)*gridUp g ζ ≤ (6*κ - lam₂)*(ζ + g) := mul_le_mul_of_nonneg_left hz₂ hslope
  have hp₃ : (lam₂ - 1)*ζ ≤ (lam₂ - 1)*gridUp g ζ := mul_le_mul_of_nonneg_left hz₁ hlam₁
  have hκζ' : κ*ζ ≤ 3/4*ζ := mul_le_mul_of_nonneg_right hκ.2 hζ
  have hslopeζ : 0 ≤ (6*κ - lam₂)*ζ := mul_nonneg hslope hζ
  have hlg : lam₂*g ≤ 5*(1/1000000) := mul_le_mul (by linarith [hlam.2]) hg' hg.le (by norm_num)
  -- The plain-loss cap is at most the cap of the cell.
  have hshort : childShortFloor b ≤ gridDown g (min n₁ n₂) := by
    unfold childShortFloor
    rw [hps, hgs]
    rw [hps] at hs'
    linarith
  have hcomp : childComparisonFloor b ≤ gridDown g (n₁ + n₂) - (9/2)*gridUp g ζ - 1/100 := by
    unfold childComparisonFloor
    rw [hgs]
    linarith
  have hshortpos : 0 ≤ 1/4 - childShortFloor b := by
    unfold childShortFloor
    rw [hps, hgs]
    linarith
  have hcap₂ : (childPosition g n₁ n₂ ζ).plainLossCap ≤
      max (1/4 - childShortFloor b) (1/4 - childComparisonFloor b/2) := by
    show max 0 (max (1/4 - gridDown g (min n₁ n₂))
      (1/4 - (gridDown g (n₁ + n₂) - (9/2)*gridUp g ζ - 1/100)/2)) ≤ _
    exact max_le (le_max_of_le_left hshortpos) (max_le_max (by linarith) (by linarith))
  -- The total length, the gap and the amplifier of the position.
  have htotal : (childPosition g n₁ n₂ ζ).totalA ≤ n₁ + n₂ + ζ + lam₂*g := by
    show planeTotalLength lam₂ (gridUp g (n₁ + n₂ + lam₂*ζ)) g (gridUp g ζ) ≤ _
    unfold planeTotalLength
    linarith
  have hgap₁ : F ≤ (childPosition g n₁ n₂ ζ).oldGap := by
    show _ ≤ planeGap κ 1 lam₂ (gridUp g (n₁ + n₂ + lam₂*ζ)) (gridUp g ζ)
    unfold planeGap
    linarith
  have hgap₂ : (childPosition g n₁ n₂ ζ).oldGap ≤ F + (1 + 6*κ - lam₂)*g := by
    show planeGap κ 1 lam₂ (gridUp g (n₁ + n₂ + lam₂*ζ)) (gridUp g ζ) ≤ _
    unfold planeGap
    linarith
  have hamp : (childPosition g n₁ n₂ ζ).amp = K*(childPosition g n₁ n₂ ζ).oldGap + lowReserveWeight := by
    show planeAmplifier slotPrice 1 secondJunction secondSlope _ _ = _
    unfold planeAmplifier SecondPosition.oldGap planeGap
    rfl
  have hKpos : 0 ≤ K := by linarith [hK.1]
  have hc : 1 + 6*κ - lam₂ ≤ 3/2 := by linarith [hκ.2, hlam.1]
  have hc₀ : 0 ≤ 1 + 6*κ - lam₂ := by linarith
  have hKg : K*((1 + 6*κ - lam₂)*g) ≤ 3*(3/2*(1/1000000)) :=
    mul_le_mul (by linarith [hK.2]) (mul_le_mul hc hg' hg.le (by norm_num)) (mul_nonneg hc₀ hg.le) (by norm_num)
  have hKω : K*ω ≤ 3*(1/1000000) := mul_le_mul (by linarith [hK.2]) hω' hω (by norm_num)
  have hampup : (childPosition g n₁ n₂ ζ).amp ≤ K*F + K*((1 + 6*κ - lam₂)*g) + lowReserveWeight := by
    rw [hamp]
    have := mul_le_mul_of_nonneg_left hgap₂ hKpos
    linarith
  have hsecond : secondAmp b = K*childOvershoot b + lowReserveWeight := rfl
  -- The reserve of the child through its width, against `c` amplifiers.
  have hroom (c : ℝ) (hc0 : 0 ≤ c) (hpos : 0 ≤ childReserve b - ω - c*K*(childOvershoot b + ω)) :
      childReserve b - ω - c*K*(childOvershoot b + ω) ≤ 1 - (n₁ + n₂ + ζ) - c*K*F := by
    apply le_of_le_mul_width hpos (by linarith [hM.1]) hM.2
    have hcK : 0 ≤ c*K := mul_nonneg hc0 hKpos
    have := mul_le_mul_of_nonneg_left hoverle hcK
    linarith
  have hroomFixed := hrooms.1
  have hroomFixedC := hrooms.2.1
  have hroomExc := hrooms.2.2.1
  have hroomExcC := hrooms.2.2.2.1
  have hroomZero := hrooms.2.2.2.2
  unfold fixedShortRoom at hroomFixed
  unfold fixedComparisonRoom at hroomFixedC
  unfold exceptionalShortRoom at hroomExc
  unfold exceptionalComparisonRoom at hroomExcC
  unfold zeroRoom at hroomZero
  rw [hsecond] at hroomFixed hroomFixedC hroomExc hroomExcC hroomZero
  refine ⟨hg, ?_, ?_, ?_, le_max_left _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show gridUp g ζ ≤ 1
    linarith
  · show 0 < gridDown g (min n₁ n₂)
    rw [hps] at hs'
    linarith
  · show gridUp g (n₁ + n₂ + lam₂*ζ) ≤ 1
    linarith [hI.2]
  · show 1/100 + (9/2)*gridUp g ζ ≤ gridDown g (n₁ + n₂)
    linarith
  · show 1 ≤ gridDown g (n₁ + n₂) + (9/2)*(gridUp g ζ - g) + 1/100
    linarith
  · show 1/4 - gridDown g (min n₁ n₂) ≤ (childPosition g n₁ n₂ ζ).plainLossCap
    exact le_max_of_le_right (le_max_left _ _)
  · show 1/4 - (gridDown g (n₁ + n₂) - (9/2)*gridUp g ζ - 1/100)/2 ≤ (childPosition g n₁ n₂ ζ).plainLossCap
    exact le_max_of_le_right (le_max_right _ _)
  · exact lt_of_lt_of_le hover hgap₁
  · have hF₀ : F ≤ 1/10 := by
      have hsz : (6*κ - lam₂)*ζ ≤ (1/2)*(681/10000) :=
        mul_le_mul (by linarith [hκ.2, hlam.1]) hζtop hζ (by norm_num)
      linarith [hI.2]
    have hKF : K*F ≤ 3*(1/10) := mul_le_mul (by linarith [hK.2]) hF₀ hover.le (by norm_num)
    linarith
  · have hmax : max (1/4 - childShortFloor b) (1/4 - childComparisonFloor b/2) ≤
        (3/2)*(childReserve b - 4*(K*childOvershoot b + lowReserveWeight) - 1/50 - 1/1000) :=
      max_le (by linarith) (by linarith)
    have hpos : 0 ≤ childReserve b - ω - 4*K*(childOvershoot b + ω) := by
      have : 0 ≤ lowReserveWeight := by rw [hα]; norm_num
      linarith
    have h := hroom 4 (by norm_num) hpos
    have : 0 ≤ (childPosition g n₁ n₂ ζ).plainLossCap := le_max_left _ _
    linarith
  · have hmax : max (1/4 - childShortFloor b) (1/4 - childComparisonFloor b/2) ≤
        (3/2)*(childReserve b - (9/2)*(K*childOvershoot b + lowReserveWeight) - 1/50 - 1/1000) :=
      max_le (by linarith) (by linarith)
    have hpos : 0 ≤ childReserve b - ω - (9/2)*K*(childOvershoot b + ω) := by
      have : 0 ≤ lowReserveWeight := by rw [hα]; norm_num
      linarith
    have h := hroom (9/2) (by norm_num) hpos
    linarith
  · have hpos : 0 ≤ childReserve b - ω - 6*K*(childOvershoot b + ω) := by
      have : 0 ≤ lowReserveWeight := by rw [hα]; norm_num
      linarith
    have h := hroom 6 (by norm_num) hpos
    show _ ≤ 1 - _ - 5*_
    linarith


end

end Cycle63

end Record1252270103Bootstrap.PR67
