/- Copyright (c) 2026 Hailey Collet; fixed-price instance (c) 2026 Zhongpai Gao.
Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.MarkedRange.PricedParameters

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Cycle153.Root
noncomputable section
open Cycle63.Optimization MarkedRootPrice

def floor : ℝ := 17/500
def mesh : ℝ := 1/100000000
def cellCount : ℕ := 638098

macro "root_physical_price" : tactic => `(tactic|
  (have hp:=MarkedRootPrice.price_bounds
   have hi:=MarkedRootPrice.intercept_bounds
   have hq:=MarkedRootPrice.q_bounds
   have hl:=MarkedRootPrice.lambda_bounds
   have hb:=MarkedRootPrice.B_bounds
   simp only [Cycle63.Optimization.planeGap,Cycle63.Optimization.planeTotalLength,
     Cycle63.Optimization.planeAmplifier,Cycle63.Optimization.amplifierRatio,
     Cycle63.Optimization.lowReserveAt,Cycle63.Optimization.lowReserveWeight,
     Cycle63.Optimization.allowanceUnit,Cycle63.Optimization.slotPrice,
     Cycle63.Optimization.betaBound,Cycle153.Root.floor,Cycle153.Root.mesh,
     Cycle153.MarkedRootPrice.top]
   rat_pos (depth:=25) [hp,hi,hq,hl,hb]))

/-- The full initial window at the fixed source-compatible price.
The LOW region is the first continuing region; the instance does not
assert a recursive source estimate. -/
@[instance_reducible]
def rootLedger : Cycle63.AffineLedger where
  q := MarkedRootPrice.q
  lam := MarkedRootPrice.lambda
  B := MarkedRootPrice.B
  price := MarkedRootPrice.price
  intercept := MarkedRootPrice.intercept
  slotFloor := floor
  slotTop := MarkedRootPrice.top
  cellMesh := mesh
  cellCount := cellCount
  windowBottom := 81/200
  sumBottom := 81/100
  comparisonLength := fun _ _ _=>1/4
  plainLossCap := 0
  zeroSaving := 1/20
  primeFraction := 99/100
  q_pos := FixedStages.stage0.q_pos
  one_fiftieth_le_q := FixedStages.stage0.q_floor
  price_pos := FixedStages.stage0.price_pos
  price_le_one := FixedStages.stage0.price_le_one
  q_le_price := FixedStages.stage0.q_le_price
  q_intercept_lt_price := FixedStages.stage0.q_intercept_lt_price
  one_le_lam := FixedStages.stage0.one_le_lam
  lam_le_six_price := FixedStages.stage0.lam_le_six_price
  lam_le_six_slotPrice := FixedStages.stage0.lam_le_six_old
  cellMesh_pos := by norm_num [mesh]
  one_le_cellCount := by norm_num [cellCount]
  cellCount_mul := by norm_num [cellCount,mesh,floor,MarkedRootPrice.top]
  slotTop_le_one := by norm_num [MarkedRootPrice.top]
  windowBottom_pos := by norm_num
  B_le_one := by linarith [MarkedRootPrice.B_bounds.2]
  plainLossCap_nonneg := le_rfl
  comparisonLength_nonneg := fun _ _ _ _=>by norm_num
  comparisonLength_le := fun _ _ _ _=>le_rfl
  long_factor := by
    intro n1 n2 z h
    linarith [h.sum_ge]
  daughter_fits := by
    intro n1 n2 z h
    have hz:=h.slots_le
    norm_num [MarkedRootPrice.top] at hz
    linarith [h.sum_ge]
  plainLoss_le := by
    intro n1 n2 z h
    exact ⟨by linarith [h.left_ge],by linarith [h.right_ge],by norm_num⟩
  zeroSaving_pos := by norm_num
  half_lt_primeFraction := by norm_num
  primeFraction_lt_one := by norm_num
  oldGap_first_pos := by root_physical_price
  amp_first_pos := by root_physical_price
  amp_top_le_one := by apply le_of_lt;root_physical_price
  lowReserveAt_le := FixedStages.stage0.low_reserve_cap
  errorReserve_edges := by
    intro b hb
    rcases hb with rfl|rfl <;>
      refine ⟨?_,?_,?_⟩ <;> apply le_of_lt <;> root_physical_price
  fixedInducing_edges := by
    intro b hb
    rcases hb with rfl|rfl <;> apply le_of_lt <;> root_physical_price
  exceptional_edges := by
    intro b hb
    rcases hb with rfl|rfl <;> apply le_of_lt <;> root_physical_price
  zero_edges := by
    intro b hb
    rcases hb with rfl|rfl <;> apply le_of_lt <;> root_physical_price

theorem root_q : @Cycle63.AffineLedger.q rootLedger=FixedStages.stage0.q := rfl
theorem root_B : @Cycle63.AffineLedger.B rootLedger=MarkedRootPrice.B := rfl
theorem root_top : @Cycle63.AffineLedger.slotTop rootLedger=MarkedRootPrice.top := rfl

end
end Cycle153.Root
#print axioms Cycle153.Root.rootLedger
