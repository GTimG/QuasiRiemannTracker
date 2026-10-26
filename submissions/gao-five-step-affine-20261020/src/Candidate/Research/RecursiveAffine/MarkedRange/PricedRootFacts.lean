/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.MarkedRange.PricedParameters
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Cycle153.MarkedRootPrice
noncomputable section
open Cycle63.Optimization

/-- The original actual source's root cutoff covers the enlarged marked range. -/
theorem native_root_dominates {d : ℝ} (hd : d∈Set.Icc q (2/3)) :
    capCoefficient d*(1-6*markedRootCutoff) ≤ markedRootCutoff*(6*density d-1-tailSlack) := by
  exact OAI.SevenEighths.Cycle153MarkedPlain.native_ledger_dominance
    ⟨q_native.trans hd.1,hd.2⟩

/-- The literal large-root source tail remains positive on the full marked range. -/
theorem large_root_tail_positive {d : ℝ} (hd : d∈Set.Icc q (2/3)) :
    0<6*density d-1-tailSlack := by
  have hq:=q_bounds
  simp only [density,tailSlack,allowanceUnit]
  rat_pos [hd,hq]

/-- Positivity and exact gain-slope gates for the actual source payment. -/
theorem gain_facts {d : ℝ} (hd : d∈Set.Icc q (2/3)) :
    0< halfGain d ∧ 0< inverseCapAt d ∧ 0< plainCapAt d ∧
      2*capCoefficient d< commonRateAt d := by
  have hq:=q_bounds
  have hmax : (3/19:ℝ) ≤ 4*density d-5/4 := by
    apply le_of_lt
    simp only [density]
    rat_pos [hd,hq]
  refine ⟨?_,?_,?_,?_⟩ <;> (try simp only [capCoefficient,commonRateAt,max_eq_right hmax]) <;> priced_channels <;> rat_pos (depth:=30) [hd,hq]

/-- The supplied width and literal native frequency satisfy the source's payment gate. -/
theorem supply_le_frequency {b : ℝ} (hb : b∈Set.Icc bottom top) :
    2*suppliedAt b ≤ planeFrequency price intercept q lambda B markedRootCutoff b := by
  have hk:=price_bounds;have hi:=intercept_bounds;have hq:=q_bounds
  have hl:=lambda_bounds;have hB:=B_bounds;have hr:=markedRootCutoff_enclosure
  have hcell : b∈Set.Icc (3400001/100000000:ℝ) (2019049/50000000) := by
    convert hb using 1 <;> norm_num [bottom,top,firstCellTop,slotFloor,cellMesh,allowanceUnit]
  apply le_of_lt
  priced_channels
  rat_pos (depth:=30) [hcell,hk,hi,hq,hl,hB,hr]
end
end Cycle153.MarkedRootPrice

#print axioms Cycle153.MarkedRootPrice.native_root_dominates
#print axioms Cycle153.MarkedRootPrice.large_root_tail_positive
#print axioms Cycle153.MarkedRootPrice.gain_facts
#print axioms Cycle153.MarkedRootPrice.supply_le_frequency
