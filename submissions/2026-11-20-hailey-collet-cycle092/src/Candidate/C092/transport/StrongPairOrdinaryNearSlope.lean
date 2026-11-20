/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One-sided radius/cap bounds for the genuine restored ordinary capacity. -/
import Candidate.C092.transport.StrongPairOrdinaryNearSource

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness

/-- Relative long caps change by at most the downward radius displacement
on the actual [.98,H] interval. -/
theorem near_long_displacement {n r x : ℝ}
    (hn0 : 0 ≤ n) (hn1 : n ≤ 5589/12500)
    (hr : (98/100:ℝ) ≤ r) (hrx : r ≤ x) :
    0 ≤ n/r-n/x ∧ n/r-n/x ≤ x-r := by
  have hr0 : 0 < r := by linarith
  have hx0 : 0 < x := hr0.trans_le hrx
  have heq : (n/r-n/x)*(r*x)=n*(x-r) := by field_simp <;> ring
  have hden : n ≤ r*x := by nlinarith
  have hpos := mul_nonneg hn0 (sub_nonneg.mpr hrx)
  constructor
  · nlinarith [mul_pos hr0 hx0]
  · apply (mul_le_mul_iff_right₀ (mul_pos hr0 hx0)).mp
    nlinarith [mul_nonneg (sub_nonneg.mpr hden) (sub_nonneg.mpr hrx)]

theorem near_adjusted_displacement {n m B r x : ℝ}
    (hn0 : 0 ≤ n) (hn1 : n ≤ 5589/12500)
    (hr : (98/100:ℝ) ≤ r) (hrx : r ≤ x) (hmB : m ≤ B) :
    adjustedWitness n m x ≤ adjustedWitness n B r ∧
    adjustedWitness n B r-adjustedWitness n m x ≤ (B-m)+(x-r) := by
  have hRatio : 0 < sourceRatio := by norm_num [sourceRatio]
  have hlong := near_long_displacement hn0 hn1 hr hrx
  have hrlambda : n/(sourceRatio*r)-n/(sourceRatio*x) = (n/r-n/x)/sourceRatio := by field_simp <;> ring
  have hgap0 : 0 ≤ n/(sourceRatio*r)-n/(sourceRatio*x) := by rw [hrlambda]; exact div_nonneg hlong.1 hRatio.le
  have hgap1 : n/(sourceRatio*r)-n/(sourceRatio*x) ≤ x-r := by
    rw [hrlambda]
    apply (div_le_iff₀ hRatio).2
    have hRatio1 : 1 ≤ sourceRatio := by norm_num [sourceRatio]
    nlinarith
  constructor
  · exact max_le_max hmB (by linarith)
  · unfold adjustedWitness
    have hB := le_max_left m (n/(sourceRatio*x))
    have hratio := le_max_right m (n/(sourceRatio*x))
    apply sub_le_iff_le_add.mpr
    apply max_le <;> linarith

/-- Genuine downward semiderivative, with the actual native transition.
No false two-sided continuity at Y is used. A downward radius bank and an
upward ordinary-cap bank cost only 5/4 and 3/4 respectively. -/
theorem near_quota_displacement {n m B r x : ℝ}
    (hn0 : 0 ≤ n) (hn1 : n ≤ 5589/12500)
    (hm0 : sourceY0 ≤ m) (hmB : m ≤ B)
    (hr : (98/100:ℝ) ≤ r) (hrx : r ≤ x) :
    nearOrdinaryQuota n m x-nearOrdinaryQuota n B r ≤
      (5/4:ℝ)*(x-r)+(3/4:ℝ)*(B-m) := by
  have hr0 : 0 < r := by linarith
  have hx0 : 0 < x := hr0.trans_le hrx
  have hlong := near_long_displacement hn0 hn1 hr hrx
  have hadj := near_adjusted_displacement hn0 hn1 hr hrx hmB
  have hml : m ≤ adjustedWitness n m x := le_max_left _ _
  have hBl : B ≤ adjustedWitness n B r := le_max_left _ _
  rw [near_quota_formula hx0,near_quota_formula hr0]
  by_cases hbank : adjustedWitness n B r ≤ sourceY
  · have hlive : adjustedWitness n m x ≤ sourceY := hadj.1.trans hbank
    rw [ite_eq_left hlive,ite_eq_left hbank]
    have hsec := sourceGain_quarter_secant (hm0.trans hml) hadj.1 hbank
    linarith
  · rw [ite_eq_right hbank]
    by_cases hlive : adjustedWitness n m x ≤ sourceY
    · rw [ite_eq_left hlive]
      have hsec := continued_gain_quarter (hm0.trans hml) hadj.1
      rw [continuedGain,ite_eq_left hlive,continuedGain,ite_eq_right hbank] at hsec
      linarith
    · rw [ite_eq_right hlive]
      linarith

/-- The real absolute ordinary capacity at the enlarged conductor scale
is paid by an earlier fixed source radius, including scales crossing H. -/
theorem near_capacity_payment {n y m B d r : ℝ}
    (hn : n ≤ sourceRatio*y) (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n)
    (hm : y/(H:ℝ) ≤ m) (hmB : m ≤ B)
    (hd : (98/100:ℝ) ≤ d) (hr : (98/100:ℝ) ≤ r) (hrd : r ≤ min d (H:ℝ)) :
    ordinaryCapacity n m d-d*nearOrdinaryQuota n B r ≤
      d*((5/4:ℝ)*(min d (H:ℝ)-r)+(3/4:ℝ)*(B-m)) := by
  have hn0 : 0 ≤ n := (source_domain.1.le.trans hy0).trans hyn
  have hn1 : n ≤ 5589/12500 := by
    have hh := hn.trans (mul_le_mul_of_nonneg_left hy1 (by norm_num [sourceRatio]))
    norm_num [sourceRatio,sourceY] at hh
    exact hh
  have hyH : y ≤ y/(H:ℝ) := (le_div_iff₀ H_real_bounds.1).2
    (mul_le_of_le_one_right (source_domain.1.le.trans hy0) H_real_bounds.2.le)
  have hm0 : sourceY0 ≤ m := hy0.trans (hyH.trans hm)
  have hh := mul_le_mul_of_nonneg_left (near_quota_displacement hn0 hn1 hm0 hmB hr hrd)
    (show 0 ≤ d by linarith)
  rw [ordinary_capacity_at_clipped_radius hn hm (by linarith)]
  nlinarith

#print axioms near_quota_displacement
#print axioms near_capacity_payment
end
end QRH.Cycle092.StrongPair
