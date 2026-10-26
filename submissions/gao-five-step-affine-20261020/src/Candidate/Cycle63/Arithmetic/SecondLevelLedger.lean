/- The ledger of the second step at one position of a first-level child: Collet's plane at the second junction
through the child, a slot window of one cell at the child's slot length, and the old region for its LOW children.
Released under Apache 2.0. -/
import Candidate.Cycle63.Arithmetic.AffineLedger
import Candidate.Cycle63.Optimization.TwoLevelHigh

set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Certificate

/-! The second step bounds one first-level LOW child at a time, so its ledger is taken at the child's own
position: the plane of slope `secondSlope = 1 + c_H` at the second junction passes through the child (in units
of the child's width), the slot window is the one cell containing the child's slot length, and the plain
windows start at the child's plain lengths. Its amplifier `K_L (B - 1 + (6κ - λ₂) b) + α` is then the second
step's amplifier of the child, `K_L F_O + α`. -/

/-- The slope of the second step's plane: one plus the slope of the region at the second junction. -/
def secondSlope : ℝ := 1 + regionSlope secondJunction

/-- The comparison length of the second step for plain lengths `n₁, n₂` and slot length `z`: a quarter of the
width, or less when the reflected daughter would not fit in the old region. -/
def secondComparisonLength (n₁ n₂ z : ℝ) : ℝ := min (1/4) ((n₁ + n₂ - (9/2)*z - 1/100)/2)

bracket secondSlope_bounds (digits := 9) : secondSlope
  unfolding [secondSlope, regionSlope, secondRatio, amplifierCost, density, slotPrice, betaBound, secondJunction]

bracket secondAmplifierRatio_bounds (digits := 9) : amplifierRatio slotPrice 1 secondJunction
  unfolding [amplifierRatio, slotPrice, betaBound, secondJunction]

theorem slotPrice_bounds : 37/50 < slotPrice ∧ slotPrice ≤ 3/4 := slotPrice_mem

end

end Cycle63.Optimization

namespace Cycle63

noncomputable section
open Cycle63.Optimization

/-- A position of the second step, in units of the child's width: the intercept of the plane through the child,
the top and the width of its one-cell slot window, the bottom of each plain length and of their sum, and the
plain-loss cap of its comparison. -/
structure SecondPosition where
  intercept : ℝ
  slotTop : ℝ
  mesh : ℝ
  windowBottom : ℝ
  sumBottom : ℝ
  plainLossCap : ℝ

namespace SecondPosition

/-- The gap over the old region of the position's cell. -/
def oldGap (P : SecondPosition) : ℝ := planeGap slotPrice 1 secondSlope P.intercept P.slotTop

/-- The amplifier width of the second step at the position. -/
def amp (P : SecondPosition) : ℝ := planeAmplifier slotPrice 1 secondJunction secondSlope P.intercept P.slotTop

/-- The bound of the total length of the position's cell. -/
def totalA (P : SecondPosition) : ℝ := planeTotalLength secondSlope P.intercept P.mesh P.slotTop

/-- The inequalities between the data of a position that the second step's ledger needs. -/
structure Facts (P : SecondPosition) : Prop where
  mesh_pos : 0 < P.mesh
  slotTop_le_one : P.slotTop ≤ 1
  windowBottom_pos : 0 < P.windowBottom
  intercept_le_one : P.intercept ≤ 1
  plainLossCap_nonneg : 0 ≤ P.plainLossCap
  comparison_room : 1/100 + (9/2)*P.slotTop ≤ P.sumBottom
  long_room : 1 ≤ P.sumBottom + (9/2)*(P.slotTop - P.mesh) + 1/100
  plain_loss : 1/4 - P.windowBottom ≤ P.plainLossCap
  comparison_loss : 1/4 - (P.sumBottom - (9/2)*P.slotTop - 1/100)/2 ≤ P.plainLossCap
  oldGap_pos : 0 < P.oldGap
  amp_le_one : P.amp ≤ 1
  fixedInducing : 1/50 + 2/3*P.plainLossCap ≤ 1 - P.totalA - 4*P.amp
  exceptional : 1/50 + 2/3*P.plainLossCap ≤ 1 - P.totalA - (9/2)*P.amp
  zero : P.amp + 1/380 + 1/20 ≤ 1 - P.totalA - 5*P.amp

end SecondPosition

/-- The comparison length of a state in the window of a position is at least the room left by the window. -/
theorem secondComparisonLength_ge {P : SecondPosition} {n₁ n₂ z : ℝ}
    (hw : PlainWindow P.windowBottom P.sumBottom (P.slotTop - P.mesh) P.slotTop secondSlope P.intercept n₁ n₂ z) :
    min (1/4) ((P.sumBottom - (9/2)*P.slotTop - 1/100)/2) ≤ secondComparisonLength n₁ n₂ z := by
  unfold secondComparisonLength
  apply min_le_min le_rfl
  have h₁ := hw.sum_ge
  have h₂ := hw.slots_le
  linarith

/-- The ledger of the second step at a position whose facts hold. -/
@[instance_reducible]
def secondLedger (P : SecondPosition) (h : P.Facts) : AffineLedger where
  q := secondJunction
  lam := secondSlope
  B := P.intercept
  price := slotPrice
  intercept := 1
  slotFloor := P.slotTop - P.mesh
  slotTop := P.slotTop
  cellMesh := P.mesh
  cellCount := 1
  windowBottom := P.windowBottom
  sumBottom := P.sumBottom
  comparisonLength := secondComparisonLength
  plainLossCap := P.plainLossCap
  zeroSaving := 1/20
  primeFraction := 3/4
  q_pos := by linarith [secondJunction_mem.1]
  one_fiftieth_le_q := by linarith [secondJunction_mem.1]
  price_pos := slotPrice_pos
  price_le_one := by linarith [slotPrice_bounds.2]
  q_le_price := by linarith [secondJunction_mem.2, slotPrice_bounds.1]
  q_intercept_lt_price := by rw [mul_one]; linarith [secondJunction_mem.2, slotPrice_bounds.1]
  one_le_lam := by linarith [secondSlope_bounds.1]
  lam_le_six_price := by linarith [secondSlope_bounds.2, slotPrice_bounds.1]
  lam_le_six_slotPrice := by linarith [secondSlope_bounds.2, slotPrice_bounds.1]
  cellMesh_pos := h.mesh_pos
  one_le_cellCount := le_rfl
  cellCount_mul := by push_cast; ring
  slotTop_le_one := h.slotTop_le_one
  windowBottom_pos := h.windowBottom_pos
  B_le_one := h.intercept_le_one
  plainLossCap_nonneg := h.plainLossCap_nonneg
  comparisonLength_nonneg := by
    intro n₁ n₂ z hw
    exact le_trans (le_min (by norm_num) (by linarith [h.comparison_room])) (secondComparisonLength_ge hw)
  comparisonLength_le := fun n₁ n₂ z _ => min_le_left _ _
  long_factor := by
    intro n₁ n₂ z hw
    have hc : secondComparisonLength n₁ n₂ z ≤ (n₁ + n₂ - (9/2)*z - 1/100)/2 := min_le_right _ _
    have h₁ := hw.sum_ge
    have h₂ := hw.slots_ge
    linarith [h.long_room]
  daughter_fits := by
    intro n₁ n₂ z _
    have hc : secondComparisonLength n₁ n₂ z ≤ (n₁ + n₂ - (9/2)*z - 1/100)/2 := min_le_right _ _
    linarith
  plainLoss_le := by
    intro n₁ n₂ z hw
    have hc := secondComparisonLength_ge hw
    refine ⟨by linarith [hw.left_ge, h.plain_loss], by linarith [hw.right_ge, h.plain_loss], ?_⟩
    rcases le_total (1/4 : ℝ) ((P.sumBottom - (9/2)*P.slotTop - 1/100)/2) with hle | hle
    · rw [min_eq_left hle] at hc
      linarith [h.plainLossCap_nonneg]
    · rw [min_eq_right hle] at hc
      linarith [h.comparison_loss]
  zeroSaving_pos := by norm_num
  half_lt_primeFraction := by norm_num
  primeFraction_lt_one := by norm_num
  oldGap_first_pos := by
    have h := h.oldGap_pos
    unfold SecondPosition.oldGap at h
    rwa [sub_add_cancel]
  amp_first_pos := by
    have hg := h.oldGap_pos
    have hr := secondAmplifierRatio_bounds
    unfold SecondPosition.oldGap planeGap at hg
    rw [sub_add_cancel]
    unfold planeAmplifier
    have hw := lowReserveWeight_pos
    nlinarith [hr.1]
  amp_top_le_one := h.amp_le_one
  lowReserveAt_le := by
    have hw : lowReserveWeight = 1/100000000 := by norm_num [lowReserveWeight, allowanceUnit]
    unfold lowReserveAt
    rw [hw, mul_one]
    have hq : 0 ≤ secondJunction/slotPrice := div_nonneg (by linarith [secondJunction_mem.1]) slotPrice_pos.le
    nlinarith
  errorReserve_edges := by
    intro b hb
    have hbt : b = P.slotTop := by
      rcases hb with hb | hb
      · rw [hb]; ring
      · exact hb
    subst hbt
    have hg := h.oldGap_pos
    have hr := secondAmplifierRatio_bounds
    have hw := lowReserveWeight_pos
    have hk : secondJunction/slotPrice ≥ 3/4 := by
      rw [ge_iff_le, le_div_iff₀ slotPrice_pos]
      linarith [secondJunction_mem.1, slotPrice_bounds.2]
    unfold SecondPosition.oldGap planeGap at hg
    unfold lowReserveAt planeAmplifier planeGap
    rw [mul_one]
    have hlow : lowReserveWeight*(1 - secondJunction/slotPrice) ≤ lowReserveWeight/4 := by nlinarith
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hr.1]
  fixedInducing_edges := by
    intro b hb
    have hbt : b = P.slotTop := by
      rcases hb with hb | hb
      · rw [hb]; ring
      · exact hb
    subst hbt
    exact h.fixedInducing
  exceptional_edges := by
    intro b hb
    have hbt : b = P.slotTop := by
      rcases hb with hb | hb
      · rw [hb]; ring
      · exact hb
    subst hbt
    exact h.exceptional
  zero_edges := by
    intro b hb
    have hbt : b = P.slotTop := by
      rcases hb with hb | hb
      · rw [hb]; ring
      · exact hb
    subst hbt
    exact h.zero

end

end Cycle63
