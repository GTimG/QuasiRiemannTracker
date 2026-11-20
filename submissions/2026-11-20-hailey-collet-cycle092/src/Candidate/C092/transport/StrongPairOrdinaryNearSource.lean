/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Authentic independent-pair earlier/native sources at restored lower radii. -/
import Candidate.C092.transport.StrongPairOrdinaryNearCapacity

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.LowActual
open QRH.Cycle092.SourceFurtherWitness
open OAI OAI.SevenEighths

theorem ordinary_near_source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y m r l : ℝ} (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (hm0 : y/(H:ℝ) ≤ m) (hm1 : m ≤ 51/100)
    (hr0 : (98/100:ℝ) ≤ r) (hr1 : r ≤ (H:ℝ))
    (hl0 : 0 ≤ l) (hl : l < nearOrdinaryQuota n m r) :
    PairUniformBox (n/r) (nearOrdinaryCap n m r) l := by
  have hr : 0 < r := by linarith
  by_cases hseam : adjustedWitness n m r ≤ sourceY
  · have hprior := earlier_adjusted_pair cover hy0 hn0 hn1 hm0 hr hr1 hseam
    obtain ⟨_,_,_,_,hcap⟩ := adjustedWitness_source_domain hy0 hn0 hn1 hm0 hr hr1 hseam
    rw [←near_quota_capacity hr] at hcap
    have hquota := (mul_le_mul_iff_right₀ hr).mp hcap
    have hsrc := hprior l hl0 (hl.trans_le hquota)
    rw [nearOrdinaryCap,ite_eq_left hseam]
    by_cases horder : adjustedWitness n m r ≤ n/r
    · simpa only [max_eq_left horder,min_eq_right horder] using hsrc
    · have horder' := le_of_not_ge horder
      apply pairUniform_swap
      simpa only [max_eq_right horder',min_eq_left horder'] using hsrc
  · rw [nearOrdinaryCap,ite_eq_right hseam]
    have hN : n/r < 1/2 := by
      apply (div_lt_iff₀ hr).2
      norm_num [sourceRatio,sourceY] at hn1 hy1
      nlinarith
    have hypos : 0 ≤ y := source_domain.1.le.trans hy0
    have hnr : y ≤ n/r := by
      apply (le_div_iff₀ hr).2
      have hrle := hr1.trans H_real_bounds.2.le
      nlinarith [mul_nonneg hypos (sub_nonneg.mpr hrle)]
    have hNlo : (7/20:ℝ) ≤ n/r := by norm_num [sourceY0] at hy0; linarith
    have hmlo : (7/20:ℝ) ≤ m := by
      have hyH : y ≤ y/(H:ℝ) := (le_div_iff₀ H_real_bounds.1).2
        (mul_le_of_le_one_right hypos H_real_bounds.2.le)
      norm_num [sourceY0] at hy0
      linarith
    rw [near_quota_formula hr,ite_eq_right hseam] at hl
    by_cases hmhalf : m < 1/2
    · exact native_mean_pair_box hβ hNlo hmlo hN hmhalf hl0 hl
    · apply native_marked_unmarked_box hβ hN.le (by linarith) hl0
      · linarith
      · linarith

/-- The true capacity is positive, so every fixed restored cap has a real
strict positive quota. This includes the small witness collar beyond .5. -/
theorem ordinary_near_positive {n y m r : ℝ}
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y) (hm : m ≤ 51/100)
    (hr0 : (98/100:ℝ) ≤ r) (hr1 : r ≤ (H:ℝ)) :
    0 < nearOrdinaryQuota n m r := by
  have h := ordinaryCapacity_positive_extended hy hn hm hr0
  rw [ordinaryCapacity,ite_eq_left hr1] at h
  exact div_pos h (by linarith)

#print axioms ordinary_near_source
#print axioms ordinary_near_positive
end
end QRH.Cycle092.StrongPair
