/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.SourceContextFee
import Candidate.Research.RecursiveAffine.ActualHighNodeProducer

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Cycle153SourceSchedule
noncomputable section
open Cycle63InitialMass Cycle153RecursiveHighProvider Cycle153.RegionalSchedule

/-- The native HIGH producer's early loss unit uses the frozen first
ledger. The primitive loss is small enough that this is exactly the same
mu as the actual root and all rounded continuing ledgers. -/
theorem actual_high_primitive_mu : highSourceLossUnit primitiveError=nativeMu := by
  have hr := Cycle63.Arithmetic.lowRegionRatio_bounds
  have hlow : primitiveError≤@Cycle63.AffineLedger.lowReserve Cycle63.Arithmetic.firstLevelLedger := by
    change primitiveError≤Cycle63.Arithmetic.lowReserve
    unfold Cycle63.Arithmetic.lowReserve Cycle63.Optimization.lowReserveAt
      Cycle63.Optimization.lowReserveWeight Cycle63.Optimization.allowanceUnit
    norm_num only [primitiveError]
    nlinarith only [hr.2]
  unfold highSourceLossUnit geometryLossUnit nativeMu
  apply min_eq_left
  apply le_min (by simpa only [mul_one] using
    div_le_div_of_nonneg_right hlow (by norm_num : (0:ℝ)≤128))
  norm_num [primitiveError]

/-- The actual native producer's affine-loss domain is satisfied. -/
theorem actual_high_primitive_upper : primitiveError≤ secondStepAffineLoss := by
  norm_num [primitiveError,secondStepAffineLoss]

/-- Its literal returned-loss floor is uniformly at most two primitive
mu, even as the ambient Fourier cardinality grows. The source driver
continues to use its physical cap130. -/
theorem actual_high_primitive_loss (N : ℕ) :
    highSourceLossNeeded primitiveError N≤2*nativeMu := by
  rw [highSourceLossNeeded,actual_high_primitive_mu]
  have hdelta := (nativeDriverRate_budgets N).1
  have hs : nativeDriverRate N≤nativeMu/(2048*((N:ℝ)+1)) := by
    have h : nativeDriverRate N≤nativeMu/(64*((31:ℝ)+1)*((N:ℝ)+1)) := by
      unfold nativeDriverRate geometryFinalDictionaryRate
      exact min_le_right _ _
    simpa only [show (64:ℝ)*(31+1)=2048 by norm_num] using h
  have hden : 0<2048*((N:ℝ)+1) := by positivity
  have hprod:=(le_div_iff₀ hden).mp hs
  have hN : (0:ℝ)≤N := Nat.cast_nonneg N
  change 13/8*nativeMu+(9*(N:ℝ)+282)*nativeDriverRate N≤2*nativeMu
  nlinarith only [hprod,hdelta,mul_nonneg hN hdelta.le]
end
end OAI.SevenEighths.Cycle153SourceSchedule
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.actual_high_primitive_mu
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.actual_high_primitive_upper
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.actual_high_primitive_loss
