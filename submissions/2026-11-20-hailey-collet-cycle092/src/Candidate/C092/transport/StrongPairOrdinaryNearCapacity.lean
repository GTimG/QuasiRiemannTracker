/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual restored ordinary caps, including the native seam and bounded collar. -/
import Candidate.C092.transport.StrongPairOrdinarySelection

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness

/-- On the earlier side restore the ratio. On the native side retain the
true upper ordinary cap, including its authentic collar beyond one half. -/
def nearOrdinaryCap (n m r : ℝ) : ℝ :=
  if adjustedWitness n m r ≤ sourceY then adjustedWitness n m r else m

def nearOrdinaryQuota (n m r : ℝ) : ℝ :=
  lowerOrdinaryCapacity n m r/r

theorem near_quota_formula {n m r : ℝ} (hr : 0 < r) :
    nearOrdinaryQuota n m r =
      if adjustedWitness n m r ≤ sourceY then
        (1-n/r-adjustedWitness n m r)/2+sourceGain (adjustedWitness n m r)
      else (1-n/r-m)/2 := by
  unfold nearOrdinaryQuota lowerOrdinaryCapacity
  dsimp only
  split_ifs <;> field_simp <;> ring

theorem near_quota_capacity {n m r : ℝ} (hr : 0 < r) :
    r*nearOrdinaryQuota n m r=lowerOrdinaryCapacity n m r := by
  unfold nearOrdinaryQuota
  field_simp

theorem near_cap_dominates (n m r : ℝ) : m ≤ nearOrdinaryCap n m r := by
  unfold nearOrdinaryCap
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

/-- The live relative capacity is normalized at min(d,H); above H this is
exactly the frozen source capacity, not a new analytic assumption. -/
theorem ordinary_capacity_at_clipped_radius {n y m d : ℝ}
    (hn : n ≤ sourceRatio*y) (hm : y/(H:ℝ) ≤ m) (hd : 0 < d) :
    ordinaryCapacity n m d=d*nearOrdinaryQuota n m (min d (H:ℝ)) := by
  by_cases hdH : d ≤ (H:ℝ)
  · rw [min_eq_left hdH,ordinaryCapacity,ite_eq_left hdH]
    exact (near_quota_capacity hd).symm
  · rw [min_eq_right (le_of_not_ge hdH),ordinaryCapacity,ite_eq_right hdH]
    have hAdj := adjustedWitness_at_H hn hm
    rw [near_quota_formula H_real_bounds.1,hAdj]
    by_cases hmY : m ≤ sourceY
    · simp only [hmY,ite_true,frozenCapacity,continuedGain]
    · simp only [hmY,ite_false,frozenCapacity,continuedGain,add_zero]

/-- Semiderivative for the genuine continued gain across the tiny Y seam.
The negative value at Y and jump to zero make the crossing favorable. -/
theorem continued_gain_quarter {m B : ℝ} (hm : sourceY0 ≤ m) (hB : m ≤ B) :
    continuedGain m-continuedGain B ≤ (1/4:ℝ)*(B-m) := by
  have h := frozen_capacity_rounding (n:=0) hm hB
  unfold frozenCapacity at h
  linarith

end
end QRH.Cycle092.StrongPair
