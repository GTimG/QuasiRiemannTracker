import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.AffineLedger
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.CellGeometry
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The ledger of the first step of Collet's affine moment: its data are the computed constants of the
proof, and its facts are certified at them. Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.Arithmetic

noncomputable section
open Cycle63.Optimization

/-- The upper edge of the first cell of the slot window lies below the top of the window. -/
theorem firstCellTop_le_slotTop : firstCellTop ≤ slotTop := by
  have hf := firstCellTop_bounds
  have ht := slotTop_bounds
  linarith [hf.2, ht.1]

/-- The two edges of the cell range lie in it. -/
theorem mem_cellRange_of_onCellEdge {b : ℝ} (hb : OnCellEdge slotFloor cellMesh slotTop b) :
    firstCellTop ≤ b ∧ b ≤ slotTop := by
  rcases hb with rfl | rfl
  · exact ⟨le_rfl, firstCellTop_le_slotTop⟩
  · exact ⟨firstCellTop_le_slotTop, le_rfl⟩

/-- The main fixed-inducing reserve is at least `1/50`. -/
theorem mainFixedReserve_ge : (1/50 : ℝ) ≤ mainFixedReserve := by
  have hq := q0_bounds
  unfold mainFixedReserve
  apply le_of_lt
  apply lt_cellMin <;>
    (unfold totalA amp regionGap
     unfold_parameters
     rat_pos [hq, lambda_enclosure, B_enclosure])

/-- The exceptional reserve `1 - totalA - (9/2) amp` is at least `1/50` on the cell range. -/
theorem exceptionalReserve_ge :
    (1/50 : ℝ) ≤ cellMin (fun b => 1 - totalA b - (9/2) * amp b) := by
  have hq := q0_bounds
  apply le_of_lt
  apply lt_cellMin <;>
    (unfold totalA amp regionGap
     unfold_parameters
     rat_pos [hq, lambda_enclosure, B_enclosure])

/-- The second-zero reserve exceeds the amplifier cap by `1/380` and by the saving `1/20` of the second
zero. -/
theorem zeroReserve_ge : amplifierCap + 1/380 + 1/20 ≤ zeroReserve := by
  have hq := q0_bounds
  have hc := amplifierCap_bounds
  unfold zeroReserve
  apply le_of_lt
  apply lt_cellMin <;>
    (unfold totalA amp regionGap
     unfold_parameters
     rat_pos [hq, hc, lambda_enclosure, B_enclosure])

/-- The LOW reserve of the channel ledger at the region of the first step is `lowReserve`. -/
theorem lowReserveAt_eq : lowReserveAt lowRegionPrice lowRegionIntercept q0 = lowReserve := rfl

/-- The ledger of the first step. -/
instance firstLevelLedger : AffineLedger where
  q := q0
  lam := lambda
  B := Arithmetic.B
  price := Optimization.lowRegionPrice
  intercept := Optimization.lowRegionIntercept
  slotFloor := Optimization.slotFloor
  slotTop := Optimization.slotTop
  cellMesh := Optimization.cellMesh
  cellCount := Optimization.cellCount
  windowBottom := CountAffine.windowBottom
  sumBottom := 2 * CountAffine.windowBottom
  comparisonLength := fun _ _ _ => 1 / 4
  plainLossCap := 0
  zeroSaving := 1 / 20
  primeFraction := firstPrimeFraction
  q_pos := q0_pos
  one_fiftieth_le_q := by linarith [q0_bounds.1]
  price_pos := by linarith [Optimization.lowRegionPrice_bounds.1]
  price_le_one := by linarith [Optimization.lowRegionPrice_bounds.2]
  q_le_price := by linarith [q0_bounds.2, Optimization.lowRegionPrice_bounds.1]
  q_intercept_lt_price :=
    (div_lt_one (by linarith [Optimization.lowRegionPrice_bounds.1])).mp
      (lt_of_le_of_lt lowRegionRatio_bounds.2 (by norm_num))
  one_le_lam := by linarith [lambda_bounds.1]
  lam_le_six_price := by linarith [lambda_bounds.2, Optimization.lowRegionPrice_bounds.1]
  lam_le_six_slotPrice := by linarith [lambda_bounds.2, Optimization.slotPrice_mem.1]
  cellMesh_pos := Optimization.cellMesh_pos
  one_le_cellCount := Optimization.one_le_cellCount
  cellCount_mul := Optimization.cellCount_mul
  slotTop_le_one := Optimization.slotTop_le_one
  windowBottom_pos := CountAffine.windowBottom_pos
  B_le_one := by linarith [B_bounds.2]
  plainLossCap_nonneg := le_rfl
  comparisonLength_nonneg := fun _ _ _ _ => by norm_num
  comparisonLength_le := fun _ _ _ _ => le_rfl
  long_factor := fun n₁ n₂ z h => by
    obtain ⟨-, -, hs, -, -, -⟩ := h
    norm_num [CountAffine.windowBottom] at hs ⊢
    linarith
  daughter_fits := fun n₁ n₂ z h => by
    obtain ⟨-, -, hs, -, hz, -⟩ := h
    norm_num [CountAffine.windowBottom] at hs
    norm_num [Optimization.slotTop] at hz ⊢
    linarith
  plainLoss_le := fun n₁ n₂ z h => by
    obtain ⟨h1, h2, -, -, -, -⟩ := h
    have hq := CountAffine.quarter_le_windowBottom
    exact ⟨by linarith, by linarith, by norm_num⟩
  zeroSaving_pos := by norm_num
  half_lt_primeFraction := by norm_num [firstPrimeFraction]
  primeFraction_lt_one := by norm_num [firstPrimeFraction]
  oldGap_first_pos := g_pos (b := Optimization.firstCellTop) ⟨le_rfl, firstCellTop_le_slotTop⟩
  amp_first_pos := amplifierFloor_pos
  amp_top_le_one := by
    show Optimization.amplifierCap ≤ 1
    linarith [Optimization.amplifierCap_bounds.2]
  lowReserveAt_le := by
    rw [lowReserveAt_eq]
    exact lowReserve_le
  errorReserve_edges := by
    intro b hb
    have hrange := mem_cellRange_of_onCellEdge hb
    have h := lowReserve_lt_errorReserves
    have h1 := h.1.le.trans (first_error_reserve hrange)
    have h6 := h.2.1.le.trans (sixth_error_reserve hrange)
    have h7 := h.2.2.le.trans (seventh_error_reserve hrange)
    rw [lowReserveAt_eq]
    show lowReserve ≤ (firstPrimeFraction - 1 / 2) * amp b - g b / 6 ∧
      lowReserve ≤ (5 * firstPrimeFraction - 1 / 2) * amp b - g b / 6 ∧
      lowReserve ≤ (6 * firstPrimeFraction - 1 / 2) * amp b - g b / 6
    exact ⟨by linarith, by linarith, by linarith⟩
  fixedInducing_edges := by
    intro b hb
    rw [mul_zero, add_zero]
    exact mainFixedReserve_ge.trans (main_fixed_reserve (mem_cellRange_of_onCellEdge hb))
  exceptional_edges := by
    intro b hb
    rw [mul_zero, add_zero]
    exact exceptionalReserve_ge.trans
      (cellMin_le (fun b => 1 - totalA b - (9/2) * amp b)
        (fun b => by unfold totalA amp regionGap; ring) (mem_cellRange_of_onCellEdge hb))
  zero_edges := by
    intro b hb
    exact zeroReserve_ge.trans (second_zero_reserve (mem_cellRange_of_onCellEdge hb))

/-- The LOW reserve of the first step is the one of its ledger. -/
theorem lowReserve_eq_ledger : lowReserve = AffineLedger.lowReserve := rfl

end

end Cycle63.Arithmetic

end Record1252270103Bootstrap.PR67
