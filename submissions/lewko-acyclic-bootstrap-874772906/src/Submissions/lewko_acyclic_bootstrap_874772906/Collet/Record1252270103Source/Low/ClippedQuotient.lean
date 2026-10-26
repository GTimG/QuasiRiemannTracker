/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The support/log argument generalizes the OpenAI/Gao CommonMaskChildCapacity
argument to literal ideal witnesses, without factoring a restricted sum. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskChildCapacity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentEnergyBands
open CenteredMomentEnergyInputParentCapacity
local notation "O" => HeckeFamily.O

/-- Any nonzero literal ideal-profile term supplies the necessary lower scale.
The coefficient multiplying this term can be arbitrary. -/
theorem support_value_scale (W : ℝ → ℂ) (I : Ideal O) (X b : ℝ)
    (hI : I ≠ 0) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b)
    (hne : W ((I.absNorm:ℝ)/X) ≠ 0) : 1 ≤ b*X := by
  have hi : (1:ℝ) ≤ I.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact hi.trans ((div_le_iff₀ hX).mp (hs hne))

/-- The sole cost of clipping an actually supported scale is its fixed support
endpoint. There is no positive lower exponent assumption. -/
theorem clipped_log_of_scale_support (Z X b : ℝ) (hZ : 1 < Z)
    (hX : 0 < X) (hs : 1 ≤ b*X) :
    0 ≤ length Z X ∧ length Z X ≤ Real.logb Z X + Real.logb Z (max 1 b) := by
  have hb : 0 < max 1 b := zero_lt_one.trans_le (le_max_left _ _)
  have hclip : max 1 X ≤ max 1 b*X := max_le
    (hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hX.le))
    (by simpa using mul_le_mul_of_nonneg_right (le_max_left 1 b) hX.le)
  refine ⟨Real.logb_nonneg hZ (le_max_left _ _),?_⟩
  have hh := Real.logb_le_logb_of_le hZ
    (zero_lt_one.trans_le (le_max_left 1 X)) hclip
  rw [Real.logb_mul hb.ne' hX.ne'] at hh
  simpa only [length,add_comm] using hh

/-- Both quotient scales share their raw product exactly. The support witnesses
refer to this same branch of the centered rectangle. -/
theorem clipped_quotient_pair (W₁ W₂ : ℝ → ℂ) (I J : Ideal O)
    (Z X₁ X₂ d₁ d₂ b₁ b₂ : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hI : I ≠ 0) (hJ : J ≠ 0)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hne₁ : W₁ ((I.absNorm:ℝ)/(X₁/d₁)) ≠ 0)
    (hne₂ : W₂ ((J.absNorm:ℝ)/(X₂/d₂)) ≠ 0) :
    length Z (X₁/d₁) + length Z (X₂/d₂) ≤
      Real.logb Z (X₁*X₂) - (Real.logb Z d₁ + Real.logb Z d₂) +
        Real.logb Z (max 1 b₁*max 1 b₂) := by
  have h₁ := clipped_log_of_scale_support Z (X₁/d₁) b₁ hZ (div_pos hX₁ hd₁)
    (support_value_scale W₁ I _ b₁ hI (div_pos hX₁ hd₁) hs₁ hne₁)
  have h₂ := clipped_log_of_scale_support Z (X₂/d₂) b₂ hZ (div_pos hX₂ hd₂)
    (support_value_scale W₂ J _ b₂ hJ (div_pos hX₂ hd₂) hs₂ hne₂)
  rw [Real.logb_div hX₁.ne' hd₁.ne'] at h₁
  rw [Real.logb_div hX₂.ne' hd₂.ne'] at h₂
  rw [Real.logb_mul hX₁.ne' hX₂.ne',Real.logb_mul
    (zero_lt_one.trans_le (le_max_left 1 b₁)).ne'
    (zero_lt_one.trans_le (le_max_left 1 b₂)).ne']
  linarith only [h₁.2,h₂.2]

/-- A nonzero centered rectangle yields a supported original or reference pair.
The conclusion keeps that choice: support of Y alone cannot justify X clipping. -/
theorem clipped_equal_product_disjunction (W₁ W₂ : ℝ → ℂ) (I J : Ideal O)
    (Z X₁ X₂ Y₁ Y₂ d₁ d₂ b₁ b₂ : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) (hprod : Y₁*Y₂ = X₁*X₂)
    (hne : (W₁ ((I.absNorm:ℝ)/(X₁/d₁)) ≠ 0 ∧ W₂ ((J.absNorm:ℝ)/(X₂/d₂)) ≠ 0) ∨
      (W₁ ((I.absNorm:ℝ)/(Y₁/d₁)) ≠ 0 ∧ W₂ ((J.absNorm:ℝ)/(Y₂/d₂)) ≠ 0)) :
    let cap := Real.logb Z (X₁*X₂) - (Real.logb Z d₁ + Real.logb Z d₂) +
      Real.logb Z (max 1 b₁*max 1 b₂)
    (length Z (X₁/d₁) + length Z (X₂/d₂) ≤ cap) ∨
    (length Z (Y₁/d₁) + length Z (Y₂/d₂) ≤ cap) := by
  rcases hne with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact Or.inl (clipped_quotient_pair W₁ W₂ I J Z X₁ X₂ d₁ d₂ b₁ b₂
      hZ hX₁ hX₂ hd₁ hd₂ hI hJ hs₁ hs₂ h₁ h₂)
  · apply Or.inr
    simpa only [hprod] using clipped_quotient_pair W₁ W₂ I J Z Y₁ Y₂ d₁ d₂ b₁ b₂
      hZ hY₁ hY₂ hd₁ hd₂ hI hJ hs₁ hs₂ h₁ h₂

/-- A branch whose scale fails support vanishes for every character and height. -/
theorem polynomial_eq_zero_of_scale (χ : Character) (W : ℝ → ℂ)
    (X sigma t b : ℝ) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b)
    (hsmall : b*X < 1) : HeckeDyadic.polynomial χ false W X sigma t = 0 := by
  by_contra hn
  have h := CenteredMomentCommonMaskChildCapacity.polynomial_nonzero_support
    χ W X sigma t b hX hs hn
  linarith only [h,hsmall]

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.clipped_quotient_pair
#print axioms QRH.Record1252270103Low.clipped_equal_product_disjunction
#print axioms QRH.Record1252270103Low.polynomial_eq_zero_of_scale
