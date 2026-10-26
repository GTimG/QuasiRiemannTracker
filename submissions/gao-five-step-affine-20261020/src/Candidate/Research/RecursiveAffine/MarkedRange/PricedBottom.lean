/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.MarkedRange.PricedParameters
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Cycle153.MarkedRootPrice
noncomputable section
open Cycle63.Optimization

theorem rate_bottom {d : ℝ} (hd : d∈Set.Icc q (2/3)) :
    highFee price intercept q top < rateChannel price intercept q lambda B d bottom := by
  have hk:=price_bounds;have hi:=intercept_bounds;have hq:=q_bounds
  have hl:=lambda_bounds;have hb:=B_bounds;have hr:=markedRootCutoff_enclosure
  have hmax : (3/19:ℝ) ≤ 4*density d-5/4 := by
    apply le_of_lt
    simp only [density]
    rat_pos [hd,hq]
  simp only [rateChannel,commonRateAt,max_eq_right hmax]
  priced_channels
  rat_pos (depth := 30) [hd,hk,hi,hq,hl,hb,hr]

theorem linear_bottom {d : ℝ} (hd : d∈Set.Icc q (2/3)) :
    highFee price intercept q top < linearChannel price intercept q lambda B d bottom := by
  have hk:=price_bounds;have hi:=intercept_bounds;have hq:=q_bounds
  have hl:=lambda_bounds;have hb:=B_bounds;have hr:=markedRootCutoff_enclosure
  priced_channels
  rat_pos (depth := 30) [hd,hk,hi,hq,hl,hb,hr]

theorem mixed_bottom {d : ℝ} (hd : d∈Set.Icc q (2/3)) :
    highFee price intercept q top < mixedChannel price intercept q lambda B markedRootCutoff d bottom := by
  have hk:=price_bounds;have hi:=intercept_bounds;have hq:=q_bounds
  have hl:=lambda_bounds;have hb:=B_bounds;have hr:=markedRootCutoff_enclosure
  priced_channels
  rat_pos (depth := 30) [hd,hk,hi,hq,hl,hb,hr]

theorem inverse_bottom {d : ℝ} (hd : d∈Set.Icc q (2/3)) :
    highFee price intercept q top < inverseChannel price intercept q lambda B markedRootCutoff d bottom := by
  have hk:=price_bounds;have hi:=intercept_bounds;have hq:=q_bounds
  have hl:=lambda_bounds;have hb:=B_bounds;have hr:=markedRootCutoff_enclosure
  priced_channels
  rat_pos (depth := 30) [hd,hk,hi,hq,hl,hb,hr]

theorem capped_bottom {d : ℝ} (hd : d∈Set.Icc q (2/3)) :
    highFee price intercept q top < cappedChannel price intercept q lambda B markedRootCutoff d bottom := by
  have hk:=price_bounds;have hi:=intercept_bounds;have hq:=q_bounds
  have hl:=lambda_bounds;have hb:=B_bounds;have hr:=markedRootCutoff_enclosure
  priced_channels
  rat_pos (depth := 30) [hd,hk,hi,hq,hl,hb,hr]

theorem unmarked_bottom {d : ℝ} (hd : d∈Set.Icc (2/3) (3/4)) :
    highFee price intercept q top < planeHigh price intercept q lambda B d bottom := by
  have hk:=price_bounds;have hi:=intercept_bounds;have hq:=q_bounds
  have hl:=lambda_bounds;have hb:=B_bounds
  priced_channels
  rat_pos (depth := 30) [hd,hk,hi,hq,hl,hb]
end
end Cycle153.MarkedRootPrice

#print axioms Cycle153.MarkedRootPrice.rate_bottom

#print axioms Cycle153.MarkedRootPrice.linear_bottom

#print axioms Cycle153.MarkedRootPrice.mixed_bottom

#print axioms Cycle153.MarkedRootPrice.inverse_bottom

#print axioms Cycle153.MarkedRootPrice.capped_bottom

#print axioms Cycle153.MarkedRootPrice.unmarked_bottom
