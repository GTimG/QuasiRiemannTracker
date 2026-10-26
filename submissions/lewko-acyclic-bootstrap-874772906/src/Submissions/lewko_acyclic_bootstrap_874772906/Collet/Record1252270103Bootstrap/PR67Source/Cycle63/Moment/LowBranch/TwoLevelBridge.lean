import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.SecondLevelFamily
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The first step's ledger as the first step of the two-level ledger: the deletion that pays the LOW reserve, and the
overshoot, the reserve and the region boundary of a child of zero extraction. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open Cycle63 Cycle63.Optimization

section Generic
variable [L : AffineLedger]

/-- The fixed deletion of the cell `b` of a ledger: the slot width that puts a child of zero extraction on the
boundary of the region of the ledger's LOW children. -/
def fixedDel (b : ℝ) : ℝ := regionDeletion L.price L.intercept (AffineLedger.regionGap b) (AffineLedger.amp b)

/-- The fixed deletion is paid by the amplifier less the LOW reserve, at the junction. -/
theorem fixedDel_pays (b : ℝ) : L.q * fixedDel b = AffineLedger.amp b - AffineLedger.lowReserve := by
  have h := AffineLedger.low_reserve b
  have hk : L.price ≠ 0 := L.price_pos.ne'
  rw [← h]
  unfold fixedDel regionDeletion AffineLedger.lowRate
  field_simp
  ring

/-- The LOW reserve is at most the amplifier width of every cell of the window. -/
theorem lowReserve_le_amp {b : ℝ} (hb : AffineLedger.firstCellTop ≤ b ∧ b ≤ L.slotTop) :
    AffineLedger.lowReserve ≤ AffineLedger.amp b := by
  have h1 := (AffineLedger.lowReserve_le_errorReserves).1
  have h2 : AffineLedger.firstErrorReserve ≤ (L.primeFraction - 1 / 2) * AffineLedger.amp AffineLedger.firstCellTop -
      AffineLedger.g AffineLedger.firstCellTop / 6 := min_le_left _ _
  have hfirst : AffineLedger.firstCellTop ≤ L.slotTop := AffineLedger.firstCellTop_le_slotTop
  have hg := AffineLedger.g_pos (b := AffineLedger.firstCellTop) ⟨le_rfl, hfirst⟩
  have hamp := AffineLedger.amp_pos (b := AffineLedger.firstCellTop) ⟨le_rfl, hfirst⟩
  have hpf := L.primeFraction_lt_one
  have hfloor := (AffineLedger.amp_bounds hb).1
  unfold AffineLedger.amplifierFloor at hfloor
  nlinarith [mul_pos hamp (by linarith : 0 < 1 - L.primeFraction)]

end Generic

/-- The ledger of the first step is the first step of the two-level ledger. -/
class IsTwoLevelFirstStep (L : AffineLedger) : Prop where
  q_eq : L.q = firstJunction
  lam_eq : L.lam = twoLevelSlope
  B_eq : L.B = twoLevelPlaneIntercept
  price_eq : L.price = twoLevelPrice
  intercept_eq : L.intercept = twoLevelIntercept
  slotFloor_eq : L.slotFloor = slotFloor
  slotTop_eq : L.slotTop = slotTop
  cellMesh_eq : L.cellMesh = cellMesh

section TwoLevel
variable [L : AffineLedger] [h : IsTwoLevelFirstStep L]

/-- The amplifier width of the first step's ledger is that of the two-level ledger. -/
theorem amp_eq (b : ℝ) : AffineLedger.amp b = firstAmp b := by
  unfold AffineLedger.amp AffineLedger.Ka AffineLedger.regionGap planeGap firstAmp planeAmplifier
  rw [h.price_eq, h.intercept_eq, h.q_eq, h.lam_eq, h.B_eq]

/-- The gap over the old region of the first step's ledger is that of the two-level ledger. -/
theorem g_eq (b : ℝ) : AffineLedger.g b = twoLevelOldGap b := by
  unfold AffineLedger.g twoLevelOldGap
  rw [h.lam_eq, h.B_eq]

/-- The bound of the total length of the first step's ledger is that of the two-level ledger. -/
theorem totalA_eq (b : ℝ) : AffineLedger.totalA b = twoLevelTotalA b := by
  unfold AffineLedger.totalA twoLevelTotalA
  rw [h.lam_eq, h.B_eq, h.cellMesh_eq]

/-- The fixed deletion of the first step's ledger is that of the two-level ledger. -/
theorem fixedDel_eq (b : ℝ) : fixedDel b = fixedDeletion b := by
  unfold fixedDel fixedDeletion AffineLedger.regionGap
  rw [h.price_eq, h.intercept_eq, h.lam_eq, h.B_eq, amp_eq]

/-- The cells of the window of the first step's ledger are those of the two-level ledger. -/
theorem cell_range {b : ℝ} (hb : AffineLedger.firstCellTop ≤ b ∧ b ≤ L.slotTop) :
    firstCellTop ≤ b ∧ b ≤ slotTop := by
  unfold AffineLedger.firstCellTop at hb
  rw [h.slotFloor_eq, h.cellMesh_eq, h.slotTop_eq] at hb
  exact hb

/-- The LOW reserve of the first step's ledger is that of the two-level ledger. -/
theorem lowReserve_eq : AffineLedger.lowReserve = lowReserveAt twoLevelPrice twoLevelIntercept firstJunction := by
  unfold AffineLedger.lowReserve
  rw [h.price_eq, h.intercept_eq, h.q_eq]

/-- The rate of the direct deletion is the junction over six times the slot price. -/
theorem directRate_eq : L.q / (6 * slotPrice) = directDeletionRate := by
  unfold directDeletionRate
  rw [h.q_eq]

omit h in
/-- The fixed deletion of the cells of the window is not negative. -/
theorem fixedDel_nonneg {b : ℝ} (hb : AffineLedger.firstCellTop ≤ b ∧ b ≤ L.slotTop) : 0 ≤ fixedDel b := by
  have h1 := fixedDel_pays b
  have h2 := lowReserve_le_amp hb
  have h3 := L.q_pos
  by_contra hneg
  push Not at hneg
  nlinarith [mul_pos h3 (neg_pos.mpr hneg)]

/-- The first cell top of the first step's ledger is that of the two-level ledger. -/
theorem firstCellTop_eq : AffineLedger.firstCellTop = firstCellTop := by
  unfold AffineLedger.firstCellTop firstCellTop
  rw [h.slotFloor_eq, h.cellMesh_eq]

/-- The amplifier width grows with the cell: the first cell has the least. -/
theorem firstAmp_mono {b : ℝ} (hb : AffineLedger.firstCellTop ≤ b ∧ b ≤ L.slotTop) :
    firstAmp firstCellTop ≤ firstAmp b := by
  have h' := (AffineLedger.amp_bounds hb).1
  unfold AffineLedger.amplifierFloor at h'
  rw [amp_eq, amp_eq, firstCellTop_eq] at h'
  exact h'

end TwoLevel

/-- The overshoot of the zero-extraction child of a cell is the gap over the old region plus six amplifiers less the
slot price times the fixed deletion. -/
theorem childOvershoot_eq (b : ℝ) :
    childOvershoot b = twoLevelOldGap b + 6 * firstAmp b - 6 * slotPrice * fixedDeletion b := by
  unfold childOvershoot oldOvershoot planeTotalLength twoLevelOldGap planeGap
  ring

/-- The fixed deletion puts a child of zero extraction on the boundary of the second step's region, up to the mesh of
the cell. -/
theorem fixedDeletion_boundary (b : ℝ) :
    twoLevelTotalA b - fixedDeletion b + (secondSlope - 1) * (b - fixedDeletion b) =
      twoLevelIntercept * (1 - 6 * firstAmp b) + (twoLevelSlope - 1) * cellMesh := by
  have hprice : 6 * twoLevelPrice = 1 + regionSlope secondJunction := by
    unfold twoLevelPrice regionPrice; ring
  have hp : twoLevelPrice ≠ 0 := by
    have h := secondSlope_bounds
    unfold twoLevelPrice regionPrice
    unfold secondSlope at h
    intro h0
    linarith [h.1]
  have hb := region_deletion_boundary (intercept := twoLevelIntercept) hprice hp
    (planeTotalLength twoLevelSlope twoLevelPlaneIntercept 0 b) b (firstAmp b)
  have hd : regionDeletion twoLevelPrice twoLevelIntercept
      (planeTotalLength twoLevelSlope twoLevelPlaneIntercept 0 b + regionSlope secondJunction * b -
        twoLevelIntercept) (firstAmp b) = fixedDeletion b := by
    unfold fixedDeletion
    congr 1
    unfold planeGap planeTotalLength
    rw [hprice]
    ring
  dsimp only at hb
  rw [hd] at hb
  unfold twoLevelTotalA planeTotalLength at *
  unfold secondSlope
  linarith

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
