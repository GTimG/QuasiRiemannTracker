import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.AffineLedger
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.TwoLevelLedger
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The cell functions of the first step of the two-level ledger and the margin of its depth-two HIGH rows.
Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Certificate

/-! The first step of the two-level ledger runs at the junction `firstJunction` on the plane of
`TwoLevelLedger`, and deletes its LOW children into the region of the second step at `secondJunction`.
A LOW child of zero extraction in the cell `b` loses the slot width `fixedDeletion b`, which puts it on the
region's boundary (`region_deletion_boundary`); its overshoot over the old region is then `childOvershoot b`,
and the second step amplifies it by `secondAmp b`. The joint count of the depth-two HIGH rows pays
`highTwoAt δ b` in the bin `δ` (`joint_high_split`); it is affine in the cell and increases in the bin, so its
least value over the HIGH bins of the second step and the cells of the window is `highTwoMargin`, attained at
the second junction and an end of the window. -/

/-- The slot price of the region into which the first step deletes its LOW children. -/
def twoLevelPrice : ℝ := regionPrice secondJunction

/-- The intercept of that region. -/
def twoLevelIntercept : ℝ := regionIntercept secondJunction regionMargin

/-- The slope of the plane of the first step. -/
def twoLevelSlope : ℝ := planeSlope twoLevelPrice twoLevelIntercept firstJunction

/-- The intercept of the plane of the first step. -/
def twoLevelPlaneIntercept : ℝ := planeIntercept twoLevelPrice twoLevelIntercept firstJunction slotTop

/-- The amplifier width of the first step in the cell `b`. -/
def firstAmp (b : ℝ) : ℝ :=
  planeAmplifier twoLevelPrice twoLevelIntercept firstJunction twoLevelSlope twoLevelPlaneIntercept b

/-- The bound of the total plain and slot length of the first step in the cell of upper edge `b`. -/
def twoLevelTotalA (b : ℝ) : ℝ := planeTotalLength twoLevelSlope twoLevelPlaneIntercept cellMesh b

/-- The slot width whose deletion puts a LOW child of zero extraction in the cell `b` on the boundary of the
second step's region. -/
def fixedDeletion (b : ℝ) : ℝ :=
  regionDeletion twoLevelPrice twoLevelIntercept
    (planeGap twoLevelPrice twoLevelIntercept twoLevelSlope twoLevelPlaneIntercept b) (firstAmp b)

/-- The overshoot over the old region, after the fixed deletion, of the LOW child of zero extraction at the
upper corner of the cell `b`: slot length `b` and total length on the plane. The overshoot of every child of
the cell is at most this, because it grows with the slot length along the plane. -/
def childOvershoot (b : ℝ) : ℝ :=
  oldOvershoot (planeTotalLength twoLevelSlope twoLevelPlaneIntercept 0 b - fixedDeletion b) (b - fixedDeletion b)
    (1 - 6*firstAmp b)

/-- The amplifier width of the second step for the LOW child of zero extraction in the cell `b`. -/
def secondAmp (b : ℝ) : ℝ := amplifierRatio slotPrice 1 secondJunction*childOvershoot b + lowReserveWeight

/-- The exponent reserve of the joint count of the depth-two HIGH rows in the bin `δ` and the cell `b`. -/
def highTwoAt (δ b : ℝ) : ℝ :=
  (1 - density δ) - δ*twoLevelTotalA b + (δ - firstJunction)*fixedDeletion b -
    (firstAmp b + secondAmp b)*amplifierCost δ

/-- The least exponent reserve of the depth-two HIGH rows over the HIGH bins of the second step and the cells
of the window. -/
def highTwoMargin : ℝ := min (highTwoAt secondJunction firstCellTop) (highTwoAt secondJunction slotTop)

/-- The growth of the reserve in the bin, per unit of bin above the second junction, at its least rate. -/
def highTwoGrowth (b : ℝ) : ℝ :=
  (50/3)*(1 - 6*(firstAmp b + secondAmp b))/(5 - 2*secondJunction)^2 - (twoLevelTotalA b - fixedDeletion b)

bracket highTwoFirst_enclosure (digits := 12) : highTwoAt secondJunction firstCellTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding
      [highTwoAt, twoLevelSlope, twoLevelPlaneIntercept, twoLevelTotalA, fixedDeletion, firstAmp, childOvershoot,
      secondAmp, planeTotalLength,
    regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio, amplifierCost, density, twoLevelPrice,
    twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, regionMargin, allowanceUnit,
    lowReserveWeight, cellMesh, slotPrice, betaBound, secondJunction, firstJunction, firstCellTop, slotFloor]

bracket highTwoTop_enclosure (digits := 12) : highTwoAt secondJunction slotTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding
      [highTwoAt, twoLevelSlope, twoLevelPlaneIntercept, twoLevelTotalA, fixedDeletion, firstAmp, childOvershoot,
      secondAmp, planeTotalLength,
    regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio, amplifierCost, density, twoLevelPrice,
    twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, regionMargin, allowanceUnit,
    lowReserveWeight, cellMesh, slotPrice, betaBound, secondJunction, firstJunction, slotTop]

bracket highTwoGrowthFirst_enclosure (digits := 6) : highTwoGrowth firstCellTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding
      [highTwoGrowth, twoLevelSlope, twoLevelPlaneIntercept, twoLevelTotalA, fixedDeletion, firstAmp, childOvershoot,
      secondAmp, planeTotalLength,
    regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio, twoLevelPrice, twoLevelIntercept,
    regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density, regionMargin, allowanceUnit,
    lowReserveWeight, cellMesh, slotPrice, betaBound, secondJunction, firstJunction, firstCellTop, slotFloor]

bracket highTwoGrowthTop_enclosure (digits := 6) : highTwoGrowth slotTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding
      [highTwoGrowth, twoLevelSlope, twoLevelPlaneIntercept, twoLevelTotalA, fixedDeletion, firstAmp, childOvershoot,
      secondAmp, planeTotalLength,
    regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio, twoLevelPrice, twoLevelIntercept,
    regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density, regionMargin, allowanceUnit,
    lowReserveWeight, cellMesh, slotPrice, betaBound, secondJunction, firstJunction, slotTop]

bracket highTwoAmpFirst_enclosure (digits := 6) : firstAmp firstCellTop + secondAmp firstCellTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [twoLevelSlope, twoLevelPlaneIntercept, fixedDeletion, firstAmp, childOvershoot, secondAmp,
    planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio, twoLevelPrice,
    twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density, regionMargin,
    allowanceUnit, lowReserveWeight, slotPrice, betaBound, secondJunction, firstJunction, firstCellTop, slotFloor,
    cellMesh]

bracket highTwoAmpTop_enclosure (digits := 6) : firstAmp slotTop + secondAmp slotTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [twoLevelSlope, twoLevelPlaneIntercept, fixedDeletion, firstAmp, childOvershoot, secondAmp,
    planeTotalLength, regionDeletion, planeGap, planeAmplifier, oldOvershoot, amplifierRatio, twoLevelPrice,
    twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density, regionMargin,
    allowanceUnit, lowReserveWeight, slotPrice, betaBound, secondJunction, firstJunction, slotTop]

/-- An affine function on an interval is at least the smaller of its values at the ends. -/
theorem min_le_of_affine {f : ℝ → ℝ} (hf : ∀ x, f x = f 0 + (f 1 - f 0)*x) {lo hi x : ℝ} (hlo : lo ≤ x)
    (hhi : x ≤ hi) : min (f lo) (f hi) ≤ f x := by
  rw [hf lo, hf hi, hf x]
  rcases le_total 0 (f 1 - f 0) with h | h
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

/-- The reserve at the second junction is affine in the cell. -/
theorem highTwoAt_affine (x : ℝ) :
    highTwoAt secondJunction x =
      highTwoAt secondJunction 0 + (highTwoAt secondJunction 1 - highTwoAt secondJunction 0)*x := by
  unfold highTwoAt secondAmp childOvershoot twoLevelTotalA fixedDeletion firstAmp planeTotalLength regionDeletion
    planeGap planeAmplifier oldOvershoot
  ring

/-- The least growth rate of the reserve in the bin is affine in the cell. -/
theorem highTwoGrowth_affine (x : ℝ) :
    highTwoGrowth x = highTwoGrowth 0 + (highTwoGrowth 1 - highTwoGrowth 0)*x := by
  unfold highTwoGrowth secondAmp childOvershoot twoLevelTotalA fixedDeletion firstAmp planeTotalLength
    regionDeletion planeGap planeAmplifier oldOvershoot
  ring

/-- The total amplifier width of the two steps is affine in the cell. -/
theorem highTwoAmp_affine (x : ℝ) :
    firstAmp x + secondAmp x = (firstAmp 0 + secondAmp 0) +
        ((firstAmp 1 + secondAmp 1) - (firstAmp 0 + secondAmp 0))*x := by
  unfold secondAmp childOvershoot fixedDeletion firstAmp planeTotalLength regionDeletion planeGap planeAmplifier
    oldOvershoot
  ring

/-- The difference of the densities of two bins. -/
theorem density_sub {x y : ℝ} (hx : 5 - 2*x ≠ 0) (hy : 5 - 2*y ≠ 0) :
    density x - density y = (50/3)*(y - x)/((5 - 2*y)*(5 - 2*x)) := by
  have h3x : (3:ℝ)*(5 - 2*x) ≠ 0 := mul_ne_zero three_ne_zero hx
  have h3y : (3:ℝ)*(5 - 2*y) ≠ 0 := mul_ne_zero three_ne_zero hy
  unfold density
  rw [show (1 - 10*x/(3*(5 - 2*x))) - (1 - 10*y/(3*(5 - 2*y))) = 10*y/(3*(5 - 2*y)) - 10*x/(3*(5 - 2*x)) by ring,
    div_sub_div _ _ h3y h3x, div_eq_div_iff (mul_ne_zero h3y h3x) (mul_ne_zero hy hx)]
  ring

/-- The least reserve of the depth-two HIGH rows is positive. -/
theorem highTwoMargin_pos : 0 < highTwoMargin := by
  have h₁ := highTwoFirst_enclosure
  have h₂ := highTwoTop_enclosure
  unfold highTwoMargin
  exact lt_min (by linarith [h₁.1]) (by linarith [h₂.1])

/-- The reserve of the depth-two HIGH rows is at least `highTwoMargin` in every HIGH bin of the second step and
every cell of the window. -/
theorem highTwo_certificate {δ b : ℝ} (hδ : secondJunction ≤ δ ∧ δ ≤ 3/4)
    (hb : firstCellTop ≤ b ∧ b ≤ slotTop) : highTwoMargin ≤ highTwoAt δ b := by
  have hfirst : highTwoMargin ≤ highTwoAt secondJunction b :=
    min_le_of_affine (f := fun x => highTwoAt secondJunction x) highTwoAt_affine hb.1 hb.2
  have hgrowth : 0 ≤ highTwoGrowth b := by
    have h := min_le_of_affine (f := highTwoGrowth) highTwoGrowth_affine hb.1 hb.2
    have h₁ := highTwoGrowthFirst_enclosure
    have h₂ := highTwoGrowthTop_enclosure
    exact le_trans (le_min (by linarith [h₁.1]) (by linarith [h₂.1])) h
  have hamp : firstAmp b + secondAmp b ≤ 1/6 := by
    have h := min_le_of_affine (f := fun x => -(firstAmp x + secondAmp x))
      (fun x => by linarith [highTwoAmp_affine x, highTwoAmp_affine 0, highTwoAmp_affine 1]) hb.1 hb.2
    have h₁ := highTwoAmpFirst_enclosure
    have h₂ := highTwoAmpTop_enclosure
    have hmin : -(1/6 : ℝ) ≤ min (-(firstAmp firstCellTop + secondAmp firstCellTop))
        (-(firstAmp slotTop + secondAmp slotTop)) :=
      le_min (by linarith [h₁.2]) (by linarith [h₂.2])
    have := hmin.trans h
    linarith
  set q := secondJunction with hqdef
  set a := firstAmp b + secondAmp b with hadef
  set A := twoLevelTotalA b with hAdef
  set d := fixedDeletion b with hddef
  have h5δ : 0 < 5 - 2*δ := by linarith [hδ.2]
  have h5q : 0 < 5 - 2*q := by linarith [secondJunction_mem.2]
  have hρ : density q - density δ = (50/3)*(δ - q)/((5 - 2*δ)*(5 - 2*q)) := density_sub h5q.ne' h5δ.ne'
  have hdiff : highTwoAt δ b - highTwoAt q b =
      (δ - q)*((50/3)*(1 - 6*a)/((5 - 2*δ)*(5 - 2*q)) - (A - d)) := by
    have hscaled : (δ - q)*((50/3)*(1 - 6*a)/((5 - 2*δ)*(5 - 2*q))) = (density q - density δ)*(1 - 6*a) := by
      rw [hρ]
      ring
    unfold highTwoAt amplifierCost
    rw [← hadef, ← hAdef, ← hddef]
    linear_combination (-1 : ℝ)*hscaled
  have hratio : (50/3)*(1 - 6*a)/(5 - 2*q)^2 ≤ (50/3)*(1 - 6*a)/((5 - 2*δ)*(5 - 2*q)) := by
    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    rw [sq]
    exact mul_le_mul_of_nonneg_right (by linarith [hδ.1]) h5q.le
  have hgrowth' : 0 ≤ (50/3)*(1 - 6*a)/((5 - 2*δ)*(5 - 2*q)) - (A - d) := by
    unfold highTwoGrowth at hgrowth
    rw [← hadef, ← hAdef, ← hddef] at hgrowth
    linarith
  have hstep : 0 ≤ highTwoAt δ b - highTwoAt q b := by
    rw [hdiff]
    exact mul_nonneg (by linarith [hδ.1]) hgrowth'
  linarith

end

end Cycle63.Optimization

end Record1252270103Bootstrap.PR67
