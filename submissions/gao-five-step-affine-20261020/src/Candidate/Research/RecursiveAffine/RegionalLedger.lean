/- Copyright (c) 2026 Hailey Collet; modifications (c) 2026 Zhongpai Gao.
Released under Apache 2.0. -/
import Candidate.Cycle63.Arithmetic.AffineLedger

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Cycle153
noncomputable section
open Cycle63.Optimization

/-- Parameters of one of the finitely many regional steps. The old source
price remains the native `slotPrice`; the output LOW region may vary. -/
structure RegionalStage where
  q : ℝ
  lam : ℝ
  price : ℝ
  intercept : ℝ
  zeroSaving : ℝ
  primeFraction : ℝ
  q_pos : 0 < q
  q_floor : 1/50 ≤ q
  price_pos : 0 < price
  price_le_one : price ≤ 1
  q_le_price : q ≤ price
  q_intercept_lt_price : q*intercept < price
  one_le_lam : 1 ≤ lam
  lam_le_six_price : lam ≤ 6*price
  lam_le_six_old : lam ≤ 6*slotPrice
  zeroSaving_pos : 0 < zeroSaving
  primeFraction_half : 1/2 < primeFraction
  primeFraction_one : primeFraction < 1
  low_reserve_cap : lowReserveAt price intercept q ≤ 1/50

/-- A one-cell position. The plane intercept need not be the intercept of
the output region. This distinction is essential at intermediate depths. -/
structure RegionalPosition where
  B : ℝ
  slotTop : ℝ
  mesh : ℝ
  windowBottom : ℝ
  sumBottom : ℝ
  plainLossCap : ℝ

def RegionalStage.amp (S : RegionalStage) (P : RegionalPosition) : ℝ :=
  planeAmplifier S.price S.intercept S.q S.lam P.B P.slotTop

def RegionalStage.oldGap (S : RegionalStage) (P : RegionalPosition) : ℝ :=
  planeGap slotPrice 1 S.lam P.B P.slotTop

def RegionalStage.totalA (S : RegionalStage) (P : RegionalPosition) : ℝ :=
  planeTotalLength S.lam P.B P.mesh P.slotTop

def regionalComparison (n₁ n₂ z : ℝ) : ℝ :=
  min (1/4) ((n₁+n₂-(9/2)*z-1/100)/2)

/-- These are physical-domain facts, not the conclusion of a returned
source estimate. They must be proved for the actual rounded position. -/
structure RegionalPosition.Facts (S : RegionalStage) (P : RegionalPosition) : Prop where
  mesh_pos : 0 < P.mesh
  slotTop_le_one : P.slotTop ≤ 1
  windowBottom_pos : 0 < P.windowBottom
  B_le_one : P.B ≤ 1
  loss_nonneg : 0 ≤ P.plainLossCap
  comparison_room : 1/100+(9/2)*P.slotTop ≤ P.sumBottom
  long_room : 1 ≤ P.sumBottom+(9/2)*(P.slotTop-P.mesh)+1/100
  plain_loss : 1/4-P.windowBottom ≤ P.plainLossCap
  comparison_loss : 1/4-(P.sumBottom-(9/2)*P.slotTop-1/100)/2 ≤ P.plainLossCap
  oldGap_pos : 0 < S.oldGap P
  amp_pos : 0 < S.amp P
  amp_le_one : S.amp P ≤ 1
  first_error : lowReserveAt S.price S.intercept S.q ≤
    (S.primeFraction-1/2)*S.amp P-S.oldGap P/6
  fixedInducing : 1/50+2/3*P.plainLossCap ≤ 1-S.totalA P-4*S.amp P
  exceptional : 1/50+2/3*P.plainLossCap ≤ 1-S.totalA P-(9/2)*S.amp P
  zero : S.amp P+1/380+S.zeroSaving ≤ 1-S.totalA P-5*S.amp P

theorem regionalComparison_ge {S : RegionalStage} {P : RegionalPosition} {n₁ n₂ z : ℝ}
    (hw : PlainWindow P.windowBottom P.sumBottom (P.slotTop-P.mesh) P.slotTop S.lam P.B n₁ n₂ z) :
    min (1/4) ((P.sumBottom-(9/2)*P.slotTop-1/100)/2) ≤ regionalComparison n₁ n₂ z := by
  unfold regionalComparison
  apply min_le_min le_rfl
  linarith [hw.sum_ge, hw.slots_le]

/-- The complete native affine interface at an arbitrary regional junction.
There is no hard-coded second junction, .75 prime fraction, or .05 zero
saving. The physical facts, including the first error payment, are retained. -/
@[instance_reducible]
def regionalLedger (S : RegionalStage) (P : RegionalPosition) (h : P.Facts S) : Cycle63.AffineLedger where
  q := S.q
  lam := S.lam
  B := P.B
  price := S.price
  intercept := S.intercept
  slotFloor := P.slotTop-P.mesh
  slotTop := P.slotTop
  cellMesh := P.mesh
  cellCount := 1
  windowBottom := P.windowBottom
  sumBottom := P.sumBottom
  comparisonLength := regionalComparison
  plainLossCap := P.plainLossCap
  zeroSaving := S.zeroSaving
  primeFraction := S.primeFraction
  q_pos := S.q_pos
  one_fiftieth_le_q := S.q_floor
  price_pos := S.price_pos
  price_le_one := S.price_le_one
  q_le_price := S.q_le_price
  q_intercept_lt_price := S.q_intercept_lt_price
  one_le_lam := S.one_le_lam
  lam_le_six_price := S.lam_le_six_price
  lam_le_six_slotPrice := S.lam_le_six_old
  cellMesh_pos := h.mesh_pos
  one_le_cellCount := le_rfl
  cellCount_mul := by push_cast; ring
  slotTop_le_one := h.slotTop_le_one
  windowBottom_pos := h.windowBottom_pos
  B_le_one := h.B_le_one
  plainLossCap_nonneg := h.loss_nonneg
  comparisonLength_nonneg := by
    intro n₁ n₂ z hw
    exact le_trans (le_min (by norm_num) (by linarith [h.comparison_room])) (regionalComparison_ge hw)
  comparisonLength_le := fun _ _ _ _ => min_le_left _ _
  long_factor := by
    intro n₁ n₂ z hw
    have hc : regionalComparison n₁ n₂ z ≤ (n₁+n₂-(9/2)*z-1/100)/2 := min_le_right _ _
    linarith [hw.sum_ge, hw.slots_ge, h.long_room]
  daughter_fits := by
    intro n₁ n₂ z _
    have hc : regionalComparison n₁ n₂ z ≤ (n₁+n₂-(9/2)*z-1/100)/2 := min_le_right _ _
    linarith
  plainLoss_le := by
    intro n₁ n₂ z hw
    have hc := regionalComparison_ge hw
    refine ⟨by linarith [hw.left_ge, h.plain_loss], by linarith [hw.right_ge, h.plain_loss], ?_⟩
    rcases le_total (1/4 : ℝ) ((P.sumBottom-(9/2)*P.slotTop-1/100)/2) with hle | hle
    · rw [min_eq_left hle] at hc
      linarith [h.loss_nonneg]
    · rw [min_eq_right hle] at hc
      linarith [h.comparison_loss]
  zeroSaving_pos := S.zeroSaving_pos
  half_lt_primeFraction := S.primeFraction_half
  primeFraction_lt_one := S.primeFraction_one
  oldGap_first_pos := by
    simpa only [RegionalStage.oldGap, sub_add_cancel] using h.oldGap_pos
  amp_first_pos := by
    simpa only [RegionalStage.amp, sub_add_cancel] using h.amp_pos
  amp_top_le_one := h.amp_le_one
  lowReserveAt_le := S.low_reserve_cap
  errorReserve_edges := by
    intro b hb
    have hb' : b=P.slotTop := by rcases hb with hb | hb <;> linarith
    subst b
    have hm : 0 ≤ S.primeFraction*S.amp P := mul_nonneg (by linarith [S.primeFraction_half]) h.amp_pos.le
    refine ⟨h.first_error, ?_, ?_⟩ <;>
      change lowReserveAt S.price S.intercept S.q ≤ _*S.amp P-S.oldGap P/6 <;>
      nlinarith [h.first_error]
  fixedInducing_edges := by
    intro b hb
    have hb' : b=P.slotTop := by rcases hb with hb | hb <;> linarith
    subst b
    exact h.fixedInducing
  exceptional_edges := by
    intro b hb
    have hb' : b=P.slotTop := by rcases hb with hb | hb <;> linarith
    subst b
    exact h.exceptional
  zero_edges := by
    intro b hb
    have hb' : b=P.slotTop := by rcases hb with hb | hb <;> linarith
    subst b
    exact h.zero

end
end Cycle153

#print axioms Cycle153.regionalLedger
