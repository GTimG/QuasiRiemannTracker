import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RationalCertificate

set_option autoImplicit false
namespace BelowSevenEighthsTight
noncomputable section

/- These inequalities justify the numeric domain changes. They do not by
   themselves extend the analytic moment theorem. -/
theorem extended_capacity_floor (κ M z : ℝ) (hκ : 13/18 ≤ κ)
    (hz : 0 ≤ z) (hdom : 6*κ*z ≤ M) :
    z ≤ 3*M/13 ∧ κ*z ≤ M/6 := by
  have h := mul_nonneg (sub_nonneg.mpr hκ) hz
  constructor <;> nlinarith

theorem extended_long_input (κ M A z : ℝ) (hκ : 13/18 ≤ κ)
    (hz : 0 ≤ z) (hA : 5*M/6 < A)
    (hdom : A+(6*κ-1)*z ≤ M) : z < M/20 := by
  have h := mul_nonneg (sub_nonneg.mpr hκ) hz
  nlinarith

theorem extended_comparison_bounds (κ M A z ξ Acomp : ℝ)
    (hκ : 13/18 ≤ κ) (hz : 0 ≤ z) (hA : 5*M/6 < A)
    (hdom : A+(6*κ-1)*z ≤ M)
    (hcomp : Acomp ≤ 3*M/2-A+2*z+ξ) :
    Acomp ≤ 23*M/30+ξ ∧
    Acomp+(6*κ-1)*z ≤ 14*M/15+ξ ∧ M/2 < A-z := by
  have hzlim := extended_long_input κ M A z hκ hz hA hdom
  constructor
  · linarith
  constructor <;> nlinarith

theorem extended_affine_coefficient (κ : ℝ)
    (hκ : 13/18 ≤ κ) (hκu : κ ≤ 1) : 0 ≤ 6*κ-1 ∧ 6*κ-1 ≤ 5 := by
  constructor <;> linarith

theorem actual_capacity_hypothesis (β : ℝ) (hβ : sigmaRat < β) (hβu : β ≤ 1) :
    (13/18 : ℝ) ≤ 2*β-1 ∧ 2*β-1 ≤ 1 ∧ β ≤ (1+(2*β-1))/2 := by
  norm_num [sigmaRat] at hβ
  constructor
  · linarith
  constructor <;> linarith

theorem capacity_penalty_constant :
    (5 / (54*(13/18)^2) : ℝ) = 30/169 ∧ (30/169 : ℝ) < 1/4 := by
  norm_num

/- The actual capacity, rather than the baseline, must satisfy the moment's
   zero-free hypothesis. This proves the cost of changing between them. -/
theorem actual_capacity_penalty_bound (q m β σ κ₀ κ : ℝ)
    (hq : 0 ≤ q) (hqu : q ≤ 5/12) (hm : 1/3 ≤ m) (hmu : m ≤ 1/2)
    (hgap : σ ≤ β) (hfloor : 13/18 ≤ κ₀)
    (hbase : κ₀ = 2*σ-1) (hactual : κ = 2*β-1) :
    q*(1-2*m)/3*(1/κ₀-1/κ) ≤ (β-σ)/4 := by
  have hk₀ : 0 < κ₀ := by linarith
  have hkk : κ₀ ≤ κ := by linarith
  have hk : 0 < κ := hk₀.trans_le hkk
  have hκfloor : 13/18 ≤ κ := hfloor.trans hkk
  have hprod : (169/324 : ℝ) ≤ κ₀*κ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hfloor) (sub_nonneg.mpr hκfloor)]
  have hn : 2*q*(1-2*m) ≤ (5/18 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqu) (by linarith : 0 ≤ 1-2*m)]
  have hcoef : 2*q*(1-2*m) ≤ 3*κ₀*κ/4 := by nlinarith
  have he : 1/κ₀-1/κ = 2*(β-σ)/(κ₀*κ) := by
    field_simp
    <;> nlinarith
  rw [he]
  have he' : q*(1-2*m)/3*(2*(β-σ)/(κ₀*κ)) =
      (2*q*(1-2*m)*(β-σ))/(3*κ₀*κ) := by field_simp <;> ring
  rw [he']
  apply (div_le_iff₀ (by positivity : 0 < 3*κ₀*κ)).mpr
  have hp := mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hgap)
  nlinarith

theorem endpoint_extension_and_capacity_absorption (Eext d Δ : ℝ)
    (hΔ : 0 ≤ Δ) (hd : d ≤ 1)
    (hE : Eext ≤ -1/1000000000000000 + 2*(1/8000000000000000) + d*Δ/4-Δ) :
    Eext ≤ -3/4000000000000000-3*Δ/4 := by
  have h := mul_nonneg (sub_nonneg.mpr hd) hΔ
  nlinarith

theorem limit_margin_absorption (Eext d Δ ζ : ℝ)
    (hΔ : 0 < Δ) (hd : d ≤ 1) (hζ : ζ < Δ/16)
    (hE : Eext ≤ 2*ζ+d*Δ/4-Δ) : Eext < -5*Δ/8 := by
  have h := mul_nonneg (sub_nonneg.mpr hd) hΔ.le
  nlinarith

#print axioms extended_comparison_bounds
#print axioms actual_capacity_penalty_bound
#print axioms endpoint_extension_and_capacity_absorption
end
end BelowSevenEighthsTight
