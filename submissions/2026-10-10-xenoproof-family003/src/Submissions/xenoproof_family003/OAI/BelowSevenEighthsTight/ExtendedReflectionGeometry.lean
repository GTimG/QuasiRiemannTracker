import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.CapacityBounds

/- Exact replacements for the real-valued geometry used by the pinned
   ReflectionRetainedLength, ReferenceLowBranchGeometry, and LiveClippingDefect
   modules. Analytic reflection and moment construction must still invoke these
   weaker bounds with the correspondingly smaller reserve. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.CapacityExtension
noncomputable section

theorem positive_slot_width_drop (M A z ξ κ : ℝ)
    (_hM : 0 ≤ M) (hz : 0 ≤ z) (hκ : 13/18 ≤ κ)
    (hA : 5*M/6 ≤ A) (hcap : A+(6*κ-1)*z ≤ M) :
    3*M/2-A+2*z+ξ ≤ 23*M/30+ξ ∧
    3*M/2-A+2*z+ξ+(6*κ-1)*z ≤ 14*M/15+ξ := by
  have hkz := mul_le_mul_of_nonneg_right (by linarith : 10/3 ≤ 6*κ-1) hz
  have hsmall : z ≤ M/20 := by linarith
  constructor <;> nlinarith

theorem slot_budgets (M total ell κ : ℝ) (hell : 0 ≤ ell) (hκ : 13/18 ≤ κ)
    (hlarge : 5*M/6 ≤ total+ell) (hcap : total+ell+(6*κ-1)*ell ≤ M) :
    ell ≤ M/20 ∧ (6*κ-1)*ell ≤ M/6 := by
  have hkell := mul_le_mul_of_nonneg_right (by linarith : 10/3 ≤ 6*κ-1) hell
  constructor <;> nlinarith

theorem robust_slot_budgets (M total ell κ e : ℝ) (hell : 0 ≤ ell) (hκ : 13/18 ≤ κ)
    (hlarge : 5*M/6-e ≤ total+ell) (hcap : total+ell+(6*κ-1)*ell ≤ M) :
    ell ≤ M/20+3*e/10 ∧ (6*κ-1)*ell ≤ M/6+e := by
  have hkell := mul_le_mul_of_nonneg_right (by linarith : 10/3 ≤ 6*κ-1) hell
  constructor <;> nlinarith

theorem robust_defect_le_width (M ξ e : ℝ) (hM : 0 ≤ M) (hξ : 0 ≤ ξ)
    (hreserve : ξ+8*e/5 ≤ M/15) : e ≤ M := by linarith

theorem robust_balanced_long_nonneg (M total ell κ ξ e : ℝ)
    (hM : 0 ≤ M) (hell : 0 ≤ ell) (hκ : 13/18 ≤ κ) (hξ : 0 ≤ ξ)
    (hlarge : 5*M/6-e ≤ total+ell) (hcap : total+ell+(6*κ-1)*ell ≤ M)
    (hreserve : ξ+8*e/5 ≤ M/15) :
    8*M/15-13*e/10 ≤ total-M/4 ∧ 0 ≤ total-M/4 := by
  obtain ⟨he, hbudget⟩ := robust_slot_budgets M total ell κ e hell hκ hlarge hcap
  constructor <;> linarith

theorem robust_reflected_low (M short along ell z κ ξ e reflected : ℝ)
    (hM : 0 ≤ M) (_hs : 0 ≤ short) (hsM : short ≤ M/4)
    (_hell : 0 ≤ ell) (_hz : 0 ≤ z) (hze : z ≤ ell) (hκ : 13/18 ≤ κ)
    (he : ell ≤ M/20+3*e/10) (hbudget : (6*κ-1)*ell ≤ M/6+e)
    (hξ : 0 ≤ ξ) (he0 : 0 ≤ e) (heM : e ≤ M)
    (hhigh : 5*M/6 < short+max 0 along+z)
    (href : reflected ≤ max 0 (M-along+ξ)) :
    0 < along ∧ reflected+short+z ≤ 23*M/30+ξ+3*e/5 ∧
      reflected+short+6*κ*z ≤ 14*M/15+ξ+8*e/5 := by
  have haz : 0 < along := by
    by_contra hn
    have ha : along ≤ 0 := le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget : (6*κ-1)*z ≤ M/6+e :=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap : z ≤ M/20+3*e/10 := hze.trans he
  refine ⟨haz, ?_⟩
  by_cases hr : 0 ≤ M-along+ξ
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

theorem robust_reflected_low_admissible (M ξ e short reflected z κ : ℝ)
    (he : 0 ≤ e) (hreserve : ξ+8*e/5 ≤ M/15)
    (ht : reflected+short+z ≤ 23*M/30+ξ+3*e/5)
    (hc : reflected+short+6*κ*z ≤ 14*M/15+ξ+8*e/5) :
    reflected+short+z ≤ 5*M/6 ∧ reflected+short+6*κ*z ≤ M := by
  constructor <;> linarith

theorem robust_deleted_cases (M total short along ell z κ ξ e reflected : ℝ)
    (hM : 0 ≤ M) (hs : 0 ≤ short) (hsM : short ≤ M/4)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hκ : 13/18 ≤ κ)
    (hξ : 0 ≤ ξ) (he0 : 0 ≤ e) (hreserve : ξ+8*e/5 ≤ M/15)
    (hlarge : 5*M/6-e ≤ total+ell) (hcap : total+ell+(6*κ-1)*ell ≤ M)
    (halong : max 0 along ≤ total-M/4) (href : reflected ≤ max 0 (M-along+ξ)) :
    (short+max 0 along+z ≤ 5*M/6 ∧ short+max 0 along+6*κ*z ≤ M) ∨
    (0 < along ∧ reflected+short+z ≤ 5*M/6 ∧ reflected+short+6*κ*z ≤ M) := by
  obtain ⟨he, hbudget⟩ := robust_slot_budgets M total ell κ e hell hκ hlarge hcap
  by_cases hlo : short+max 0 along+z ≤ 5*M/6
  · refine Or.inl ⟨hlo, ?_⟩
    have hzcap := mul_le_mul_of_nonneg_left hze (by linarith : 0 ≤ 6*κ)
    nlinarith
  · obtain ⟨ha, ht, hc⟩ := robust_reflected_low M short along ell z κ ξ e reflected
      hM hs hsM hell hz hze hκ he hbudget hξ he0
      (robust_defect_le_width M ξ e hM hξ hreserve) (lt_of_not_ge hlo) href
    exact Or.inr ⟨ha, robust_reflected_low_admissible M ξ e short reflected z κ he0 hreserve ht hc⟩

theorem robust_fixed_slack (M₀ : ℝ) (hM₀ : 0 < M₀) :
    0 < M₀/56 ∧ ∀ M : ℝ, M₀ ≤ M → M₀/56+8*(M₀/56)/5 ≤ M/15 := by
  constructor
  · positivity
  · intro M hM
    linarith

theorem reflected_low (M short along ell z κ ξ reflected : ℝ)
    (hM : 0 ≤ M) (hs : 0 ≤ short) (hsM : short ≤ M/4)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hκ : 13/18 ≤ κ)
    (he : ell ≤ M/20) (hbudget : (6*κ-1)*ell ≤ M/6) (hξ : 0 ≤ ξ)
    (hhigh : 5*M/6 < short+max 0 along+z)
    (href : reflected ≤ max 0 (M-along+ξ)) :
    0 < along ∧ reflected+short+z ≤ 23*M/30+ξ ∧
      reflected+short+6*κ*z ≤ 14*M/15+ξ := by
  simpa using robust_reflected_low M short along ell z κ ξ 0 reflected
    hM hs hsM hell hz hze hκ (by simpa using he) (by simpa using hbudget)
    hξ (by norm_num) hM hhigh href

theorem reflected_low_admissible (M ξ short reflected z κ : ℝ)
    (hξ : ξ ≤ M/15) (ht : reflected+short+z ≤ 23*M/30+ξ)
    (hc : reflected+short+6*κ*z ≤ 14*M/15+ξ) :
    reflected+short+z ≤ 5*M/6 ∧ reflected+short+6*κ*z ≤ M := by
  constructor <;> linarith

#print axioms robust_deleted_cases
end
end BelowSevenEighthsTight.CapacityExtension
