/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.MarkedRange.PricedBottom
import Candidate.Research.RecursiveAffine.MarkedRange.PricedTop
import Candidate.Research.RecursiveAffine.MarkedRange.PricedRootFacts
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Cycle153.MarkedRootPrice
noncomputable section
open Cycle63.Optimization

/-- Native marked channels at the actual new plane and actual supplied-width cap. -/
theorem ledger_channels {d b : ℝ} (hd : d∈Set.Icc q (2/3))
    (hb : b∈Set.Icc bottom top) :
    highFee price intercept q top ≤ rateChannel price intercept q lambda B d b ∧
    highFee price intercept q top ≤ linearChannel price intercept q lambda B d b ∧
    highFee price intercept q top ≤ mixedChannel price intercept q lambda B markedRootCutoff d b ∧
    highFee price intercept q top ≤ inverseChannel price intercept q lambda B markedRootCutoff d b ∧
    highFee price intercept q top ≤ cappedChannel price intercept q lambda B markedRootCutoff d b := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact affine_between (by cell_affine) hb window_ends (rate_bottom hd).le (rate_top hd).le
  · exact affine_between (by cell_affine) hb window_ends (linear_bottom hd).le (linear_top hd).le
  · exact affine_between (by cell_affine) hb window_ends (mixed_bottom hd).le (mixed_top hd).le
  · exact affine_between (by cell_affine) hb window_ends (inverse_bottom hd).le (inverse_top hd).le
  · exact affine_between (by cell_affine) hb window_ends (capped_bottom hd).le (capped_top hd).le

/-- Above 2/3 the actual unmarked source pays the same fee. -/
theorem ledger_unmarked {d b : ℝ} (hd : d∈Set.Icc (2/3) (3/4))
    (hb : b∈Set.Icc bottom top) :
    highFee price intercept q top ≤ planeHigh price intercept q lambda B d b := by
  apply affine_between (f:=fun b=>planeHigh price intercept q lambda B d b)
    (lo:=bottom) (hi:=top) (b:=b)
  · simp only [planeHigh,planeAmplifier];ring
  · exact hb
  · exact window_ends
  · exact (unmarked_bottom hd).le
  · exact (unmarked_top hd).le

/-- Native common deletion plus the native exact marked gain pays the source fee
for every actual retained live width and frequency. -/
theorem marked_allocation_payment {d b removed live frequency : ℝ}
    (hd : d∈Set.Icc q (2/3)) (hb : b∈Set.Icc bottom top)
    (hremoved : 0≤ removed) (hlive : 0≤ live)
    (hsupply : suppliedAt b≤ removed+live)
    (hfrequency : (1-6*planeAmplifier price intercept q lambda B b-frequencyLossCap)-2*removed≤ frequency) :
    highFee price intercept q top ≤ planeHigh price intercept q lambda B d b+
      commonRateAt d*removed+markedGain d live (coreFactor*frequency) := by
  obtain ⟨hphi,hu,hv,hslope⟩:=gain_facts hd
  obtain ⟨hrate,hlinear,hmixed,hinverse,hcapped⟩:=ledger_channels hd hb
  have hcore:=coreFactor_bounds
  have hc : 0 ≤ capCoefficient d := by unfold capCoefficient;positivity
  have hfreq : planeFrequency price intercept q lambda B markedRootCutoff b≤
      2*removed+coreFactor*frequency := by
    have h1:=mul_le_mul_of_nonneg_left hfrequency (by linarith [hcore.1] : (0:ℝ)≤ coreFactor)
    have h2:=mul_le_mul_of_nonneg_right (by linarith [hcore.2] : coreFactor≤1) hremoved
    simp only [planeFrequency,coreFactor] at *
    nlinarith
  exact ExactGain.exact_gain_payment (by linarith) hremoved hphi.le hu.le hv.le
    (supply_le_frequency hb) hslope.le hlive hsupply hfreq
    hrate hlinear hmixed hinverse hcapped
end
end Cycle153.MarkedRootPrice

#print axioms Cycle153.MarkedRootPrice.ledger_channels
#print axioms Cycle153.MarkedRootPrice.ledger_unmarked
#print axioms Cycle153.MarkedRootPrice.native_root_dominates
#print axioms Cycle153.MarkedRootPrice.large_root_tail_positive
#print axioms Cycle153.MarkedRootPrice.marked_allocation_payment
