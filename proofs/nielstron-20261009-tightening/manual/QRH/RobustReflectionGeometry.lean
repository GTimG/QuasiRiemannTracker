import QRH.PlainReflectionGeometry

/-!
Extended clipping-defect estimates used by the actual deleted reflection gates.
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
Energy/LiveClippingDefect.lean (Apache-2.0). The changed constants follow from
6κ-1 ≥ 10/3. The fixed slack M₀/56 is retained, not assumed sufficient.
-/
namespace QRH.RobustReflection

theorem slot_budgets (M total ell κ e : ℝ)
    (hell : 0 ≤ ell) (hk : (13/18:ℝ) ≤ κ)
    (hlarge : 5*M/6-e ≤ total+ell)
    (hcap : total+ell+(6*κ-1)*ell ≤ M) :
    ell ≤ M/20+3*e/10 ∧ (6*κ-1)*ell ≤ M/6+e := by
  have hkell : (10/3:ℝ)*ell ≤ (6*κ-1)*ell :=
    mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem defect_le_width (M ξ e : ℝ) (hM : 0 ≤ M) (hξ : 0 ≤ ξ)
    (hreserve : ξ+8*e/5 ≤ M/15) : e ≤ M := by
  linarith

theorem balanced_long_nonneg (M total ell κ ξ e : ℝ)
    (hM : 0 ≤ M) (hell : 0 ≤ ell) (hk : (13/18:ℝ) ≤ κ) (hξ : 0 ≤ ξ)
    (hlarge : 5*M/6-e ≤ total+ell)
    (hcap : total+ell+(6*κ-1)*ell ≤ M)
    (hreserve : ξ+8*e/5 ≤ M/15) :
    8*M/15-13*e/10 ≤ total-M/4 ∧ 0 ≤ total-M/4 := by
  obtain ⟨he, hb⟩ := slot_budgets M total ell κ e hell hk hlarge hcap
  constructor <;> linarith

theorem reflected_low (M short along ell z κ ξ e reflected : ℝ)
    (hM : 0 ≤ M) (hsM : short ≤ M/4) (hze : z ≤ ell) (hk : (13/18:ℝ) ≤ κ)
    (he : ell ≤ M/20+3*e/10)
    (hbudget : (6*κ-1)*ell ≤ M/6+e)
    (hξ : 0 ≤ ξ) (he0 : 0 ≤ e) (heM : e ≤ M)
    (hhigh : 5*M/6 < short+max 0 along+z)
    (href : reflected ≤ max 0 (M-along+ξ)) :
    0 < along ∧ reflected+short+z ≤ 23*M/30+ξ+3*e/5 ∧
      reflected+short+6*κ*z ≤ 14*M/15+ξ+8*e/5 := by
  have hzbudget : (6*κ-1)*z ≤ M/6+e :=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  simp only [max_def] at hhigh href
  split_ifs at hhigh href <;> refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem reflected_low_admissible (M ξ e short reflected z κ : ℝ)
    (he : 0 ≤ e) (hreserve : ξ+8*e/5 ≤ M/15)
    (ht : reflected+short+z ≤ 23*M/30+ξ+3*e/5)
    (hc : reflected+short+6*κ*z ≤ 14*M/15+ξ+8*e/5) :
    reflected+short+z ≤ 5*M/6 ∧ reflected+short+6*κ*z ≤ M := by
  constructor <;> linarith

theorem deleted_cases (M total short along ell z κ ξ e reflected : ℝ)
    (hM : 0 ≤ M) (hsM : short ≤ M/4)
    (hell : 0 ≤ ell) (hze : z ≤ ell) (hk : (13/18:ℝ) ≤ κ)
    (hξ : 0 ≤ ξ) (he0 : 0 ≤ e) (hreserve : ξ+8*e/5 ≤ M/15)
    (hlarge : 5*M/6-e ≤ total+ell)
    (hcap : total+ell+(6*κ-1)*ell ≤ M)
    (halong : max 0 along ≤ total-M/4)
    (href : reflected ≤ max 0 (M-along+ξ)) :
    (short+max 0 along+z ≤ 5*M/6 ∧ short+max 0 along+6*κ*z ≤ M) ∨
    (0 < along ∧ reflected+short+z ≤ 5*M/6 ∧ reflected+short+6*κ*z ≤ M) := by
  obtain ⟨he, hb⟩ := slot_budgets M total ell κ e hell hk hlarge hcap
  by_cases hlo : short+max 0 along+z ≤ 5*M/6
  · refine Or.inl ⟨hlo, ?_⟩
    have hzcap := mul_le_mul_of_nonneg_left hze (by linarith : 0 ≤ 6*κ)
    nlinarith
  · obtain ⟨ha, ht, hc⟩ := reflected_low M short along ell z κ ξ e reflected
      hM hsM hze hk he hb hξ he0 (defect_le_width M ξ e hM hξ hreserve)
      (lt_of_not_ge hlo) href
    exact Or.inr ⟨ha, reflected_low_admissible M ξ e short reflected z κ he0 hreserve ht hc⟩

theorem fixed_slack (M₀ : ℝ) (hM₀ : 0 < M₀) :
    0 < M₀/56 ∧ ∀ M : ℝ, M₀ ≤ M → M₀/56+8*(M₀/56)/5 ≤ M/15 := by
  constructor
  · positivity
  · intro M hM
    linarith

end QRH.RobustReflection
