/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.Price
import Submissions.arvi_selected_leaf.JointDetector.WordCount

/-!
# Scalar admission of the three-witness count into the HIGH price

This file proves the rational count/price inequalities. The selected norm,
detector saturation and analytic packed supplier are separate inputs.
-/

namespace Qrh.JointDetector

noncomputable section

theorem retainedSlope_mem {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    retainedSlope ν ∈ Set.Icc (501/1000 : ℝ) ν := by
  have h := retainedSlope_bounds hν
  exact ⟨by linarith, h.2⟩

theorem k_mul_den {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    k ν * (15 - 6 * ν) = 10 * ν := by
  unfold k
  exact div_mul_cancel₀ _ (k_den_pos hν).ne'

/-- The numerator of the count denominator at the retained slot slope. -/
def retainedDenNumerator (ν : ℝ) : ℝ :=
  (3 - ν + 1/6) * (15 - 6 * ν) - 20 * ν

theorem retainedDenNumerator_eq {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    retainedDenNumerator ν = (15 - 6 * ν) * (3 - ν - 2 * retainedSlope ν) := by
  have hk := k_mul_den hν
  unfold retainedDenNumerator retainedSlope
  nlinarith

theorem retained_count_den_pos {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    0 < 3 - ν - 2 * retainedSlope ν := by
  rw [← witnessDen_eq]
  exact witnessDen_pos hν (retainedSlope_mem hν)

theorem retainedDenNumerator_pos {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    0 < retainedDenNumerator ν := by
  rw [retainedDenNumerator_eq hν]
  exact mul_pos (k_den_pos hν) (retained_count_den_pos hν)

/-- The exact denominator-cleared reserve polynomial. -/
def countReserveNumerator (ν : ℝ) : ℝ :=
  ((15 - 6 * ν) - 10 * ν) * retainedDenNumerator ν -
    3 * ((15 - 6 * ν) - (10 * ν - (15 - 6 * ν)/12)) * (1 - ν) * (15 - 6 * ν) -
    (15 - 6 * ν) * retainedDenNumerator ν / 1000

/-- Bernstein coordinates on `[13/20,3/4]`, with all four coefficients positive. -/
theorem countReserveNumerator_bernstein (ν : ℝ) :
    countReserveNumerator ν =
      (8282693/2000000 : ℝ) * (15/2 - 10 * ν)^3 +
      3 * (3378413/1200000 : ℝ) * (10 * ν - 13/2) * (15/2 - 10 * ν)^2 +
      3 * (368327/240000 : ℝ) * (10 * ν - 13/2)^2 * (15/2 - 10 * ν) +
      (8007/16000 : ℝ) * (10 * ν - 13/2)^3 := by
  unfold countReserveNumerator retainedDenNumerator
  ring

theorem countReserveNumerator_nonneg {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    0 ≤ countReserveNumerator ν := by
  have ht : 0 ≤ 10 * ν - 13/2 := by linarith [hν.1]
  have hu : 0 ≤ 15/2 - 10 * ν := by linarith [hν.2]
  rw [countReserveNumerator_bernstein]
  positivity

theorem countReserveNumerator_identity {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    countReserveNumerator ν =
      ((1 - k ν) - jointCountExponent ν (retainedSlope ν) - 1/1000) *
        ((15 - 6 * ν) * retainedDenNumerator ν) := by
  have hd := (k_den_pos hν).ne'
  have he := (retained_count_den_pos hν).ne'
  have hκ : retainedSlope ν * (15 - 6 * ν) = 10 * ν - (15 - 6 * ν)/12 := by
    have hk := k_mul_den hν
    unfold retainedSlope
    nlinarith
  calc
    countReserveNumerator ν =
        ((15 - 6 * ν) - 10 * ν) * retainedDenNumerator ν -
          3 * ((15 - 6 * ν) - retainedSlope ν * (15 - 6 * ν)) *
            (1 - ν) * (15 - 6 * ν) -
          (15 - 6 * ν) * retainedDenNumerator ν / 1000 := by
      rw [hκ]
      rfl
    _ = _ := by
      rw [retainedDenNumerator_eq hν, jointCountExponent_eq]
      unfold k
      field_simp [hd, he]

/-- The three-witness count gains the fixed reserve `1/1000` at `k-1/12`. -/
theorem joint_count_at_retainedSlope {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    jointCountExponent ν (retainedSlope ν) ≤ (1 - k ν) - 1/1000 := by
  have hnum := countReserveNumerator_nonneg hν
  have hden := mul_pos (k_den_pos hν) (retainedDenNumerator_pos hν)
  rw [countReserveNumerator_identity hν] at hnum
  have hres : 0 ≤ (1 - k ν) - jointCountExponent ν (retainedSlope ν) - 1/1000 := by
    by_contra hc
    have hn : (1 - k ν) - jointCountExponent ν (retainedSlope ν) - 1/1000 < 0 :=
      lt_of_not_ge hc
    have := mul_neg_of_neg_of_pos hn hden
    linarith
  linarith

/-- The exact finite-difference identity underlying the amplitude derivative. -/
theorem jointCount_difference {ν δ₁ δ₂ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ₁ : δ₁ ∈ Set.Icc (501/1000 : ℝ) ν)
    (hδ₂ : δ₂ ∈ Set.Icc (501/1000 : ℝ) ν) :
    jointCountExponent ν δ₁ - jointCountExponent ν δ₂ =
      3 * (1 - ν)^2 * (δ₂ - δ₁) /
        ((3 - ν - 2 * δ₁) * (3 - ν - 2 * δ₂)) := by
  have h₁ : 3 - ν - 2 * δ₁ ≠ 0 := by
    rw [← witnessDen_eq]
    exact (witnessDen_pos hν hδ₁).ne'
  have h₂ : 3 - ν - 2 * δ₂ ≠ 0 := by
    rw [← witnessDen_eq]
    exact (witnessDen_pos hν hδ₂).ne'
  have hm₁ : jointCountExponent ν δ₁ * (3 - ν - 2 * δ₁) =
      3 * (1 - δ₁) * (1 - ν) := by
    rw [jointCountExponent_eq]
    exact div_mul_cancel₀ _ h₁
  have hm₂ : jointCountExponent ν δ₂ * (3 - ν - 2 * δ₂) =
      3 * (1 - δ₂) * (1 - ν) := by
    rw [jointCountExponent_eq]
    exact div_mul_cancel₀ _ h₂
  apply (eq_div_iff (mul_ne_zero h₁ h₂)).mpr
  calc
    (jointCountExponent ν δ₁ - jointCountExponent ν δ₂) *
        ((3 - ν - 2 * δ₁) * (3 - ν - 2 * δ₂)) =
      (jointCountExponent ν δ₁ * (3 - ν - 2 * δ₁)) * (3 - ν - 2 * δ₂) -
        (jointCountExponent ν δ₂ * (3 - ν - 2 * δ₂)) * (3 - ν - 2 * δ₁) := by ring
    _ = _ := by rw [hm₁, hm₂]; ring

/-- A uniform finite-difference version of `partial_delta e <= -3/25`. -/
theorem jointCount_decrease {ν δ₁ δ₂ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ₁ : δ₁ ∈ Set.Icc (501/1000 : ℝ) ν)
    (hδ₂ : δ₂ ∈ Set.Icc (501/1000 : ℝ) ν)
    (hδ : δ₁ ≤ δ₂) :
    jointCountExponent ν δ₂ ≤ jointCountExponent ν δ₁ - (3/25 : ℝ) * (δ₂ - δ₁) := by
  have h₁ : 0 < 3 - ν - 2 * δ₁ := by
    rw [← witnessDen_eq]
    exact witnessDen_pos hν hδ₁
  have h₂ : 0 < 3 - ν - 2 * δ₂ := by
    rw [← witnessDen_eq]
    exact witnessDen_pos hν hδ₂
  have hb : 0 ≤ 5 * (1 - ν) := by linarith [hν.2]
  have hu₁ : 3 - ν - 2 * δ₁ ≤ 5 * (1 - ν) := by linarith [hν.2, hδ₁.1]
  have hu₂ : 3 - ν - 2 * δ₂ ≤ 5 * (1 - ν) := by linarith [hν.2, hδ₂.1]
  have hprod := mul_le_mul hu₁ hu₂ h₂.le hb
  have hgap : 0 ≤ (3/25 : ℝ) * (δ₂ - δ₁) := by positivity
  have hpaid := mul_le_mul_of_nonneg_right hprod hgap
  have hi : (3/25 : ℝ) * (δ₂ - δ₁) ≤
      3 * (1 - ν)^2 * (δ₂ - δ₁) /
        ((3 - ν - 2 * δ₁) * (3 - ν - 2 * δ₂)) := by
    apply (le_div_iff₀ (mul_pos h₁ h₂)).mpr
    nlinarith
  rw [← jointCount_difference hν hδ₁ hδ₂] at hi
  linarith

/-- Above the retained slope the joint count improves with a uniform linear rate. -/
theorem joint_count_above_retainedSlope {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (retainedSlope ν) ν) :
    jointCountExponent ν δ ≤ (1 - k ν) - 1/1000 -
      (3/25 : ℝ) * (δ - retainedSlope ν) := by
  have hκ := retainedSlope_mem hν
  have hδ' : δ ∈ Set.Icc (501/1000 : ℝ) ν := ⟨hκ.1.trans hδ.1, hδ.2⟩
  have hdec := jointCount_decrease hν hκ hδ' hδ.1
  linarith [joint_count_at_retainedSlope hν]

/-- The HIGH-amplitude branch pays the retained price with its fixed reserve. -/
theorem joint_energy_small_cap_high {ν δ P s M : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (retainedSlope ν) ν)
    (hM : 0 ≤ M) (hs : s ≤ M/10) :
    jointCountExponent ν δ * M + ν * P + δ * s ≤
      (1 - k ν) * M + ν * P + retainedSlope ν * s - M/1000 := by
  have hc := mul_le_mul_of_nonneg_right (joint_count_above_retainedSlope hν hδ) hM
  have hgap : 0 ≤ δ - retainedSlope ν := sub_nonneg.mpr hδ.1
  have hcap : 0 ≤ (3/25 : ℝ) * M - s := by linarith
  have hpaid := mul_nonneg hgap hcap
  nlinarith

/-- At small retained width, the better of the zero and joint counts pays `g`. -/
theorem joint_energy_small_cap {ν δ P s M : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (501/1000 : ℝ) ν)
    (hM : 0 ≤ M) (hs0 : 0 ≤ s) (hs : s ≤ M/10) :
    min (1 - k ν) (jointCountExponent ν δ) * M + ν * P + δ * s ≤
      M + g ν P s M := by
  have heq : M + g ν P s M =
      (1 - k ν) * M + ν * P + retainedSlope ν * s := by
    rw [g, max_eq_right (by linarith : s - M/10 ≤ 0), mul_zero]
    ring
  rw [heq]
  by_cases hκ : δ ≤ retainedSlope ν
  · have hmin := mul_le_mul_of_nonneg_right
      (min_le_left (1 - k ν) (jointCountExponent ν δ)) hM
    have hslot := mul_le_mul_of_nonneg_right hκ hs0
    linarith
  · have hδκ : δ ∈ Set.Icc (retainedSlope ν) ν := ⟨le_of_not_ge hκ, hδ.2⟩
    have hhigh := joint_energy_small_cap_high hν hδκ hM hs (P := P)
    have hmin := mul_le_mul_of_nonneg_right
      (min_le_right (1 - k ν) (jointCountExponent ν δ)) hM
    linarith

/-- The scalar extension to all nonnegative slot widths leaves the slots intact. -/
theorem joint_energy_le_g {ν δ P s M : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (501/1000 : ℝ) ν)
    (hM : 0 ≤ M) (hs0 : 0 ≤ s) :
    min (1 - k ν) (jointCountExponent ν δ) * M + ν * P + δ * s ≤
      M + g ν P s M := by
  by_cases hs : s ≤ M/10
  · exact joint_energy_small_cap hν hδ hM hs0 hs
  · have hbase := joint_energy_small_cap hν hδ hM
      (by linarith : 0 ≤ M/10) (le_rfl : M/10 ≤ M/10) (P := P)
    have hshift := mul_le_mul_of_nonneg_right hδ.2
      (by linarith : 0 ≤ s - M/10)
    have hcap : g ν P (M/10) M =
        ν * P - k ν * M + retainedSlope ν * (M/10) := by simp [g]
    rw [hcap] at hbase
    rw [g, max_eq_left (by linarith : 0 ≤ s - M/10)]
    dsimp [retainedSlope] at hbase ⊢
    nlinarith

/-- Low-amplitude labels need only the inherited zero count. -/
theorem zero_energy_le_g_of_delta_le {ν δ P s M : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ≤ retainedSlope ν) (hs : 0 ≤ s) :
    (1 - k ν) * M + ν * P + δ * s ≤ M + g ν P s M := by
  have hslot := mul_le_mul_of_nonneg_right hδ hs
  have hext := mul_nonneg (extensionCoeff_pos hν).le
    (le_max_right (s - M/10) 0)
  unfold g
  nlinarith

/-- A uniform density supremum is a valid scalar HIGH majorant. -/
theorem joint_energy_le_highSup {q ν δ P s M : ℝ}
    (hq : q ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hν : ν ∈ Set.Icc q (3/4))
    (hδ : δ ∈ Set.Icc (501/1000 : ℝ) ν)
    (hM : 0 ≤ M) (hs : 0 ≤ s) :
    min (1 - k ν) (jointCountExponent ν δ) * M + ν * P + δ * s ≤
      M + highSup q P s M := by
  have hν' : ν ∈ Set.Icc (13/20 : ℝ) (3/4) := ⟨hq.1.trans hν.1, hν.2⟩
  exact (joint_energy_le_g hν' hδ hM hs).trans
    (add_le_add le_rfl (le_highSup hq.1 hν.1 hν.2 P s M))

end

end Qrh.JointDetector
