import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The height split in `PlainUnmarkedDensity.tex`, lines 209–216.

The bounded-height density estimate is an explicit premise. The conclusion
retains its common scale threshold while extending the estimate to every
nonnegative height. Parameters such as the zero bin are represented by `α`.
-/

set_option autoImplicit false

namespace OAI.SevenEighths.LocalMoment

open Filter

/-- Above the detector height, a sufficiently large polynomial in the height
dominates the elementary linear row count. -/
theorem scale_le_height_weight
    {Y T τ ρ : ℝ} {J : ℕ}
    (hY : 1 ≤ Y) (hT : Y ^ τ ≤ T) (hρ : 0 ≤ ρ)
    (hJ : 1 ≤ τ * (J : ℝ)) :
    Y ≤ (1 + T) ^ J * Y ^ ρ := by
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  have hT0 : 0 ≤ T := (Real.rpow_nonneg hY0 τ).trans hT
  have hpower : Y ≤ (1 + T) ^ J := by
    calc
      Y = Y ^ (1 : ℝ) := (Real.rpow_one Y).symm
      _ ≤ Y ^ (τ * (J : ℝ)) := Real.rpow_le_rpow_of_exponent_le hY hJ
      _ = (Y ^ τ) ^ J := by rw [Real.rpow_mul hY0, Real.rpow_natCast]
      _ ≤ (1 + T) ^ J := pow_le_pow_left₀ (Real.rpow_nonneg hY0 τ) (by linarith) J
  exact hpower.trans (le_mul_of_one_le_right
    (pow_nonneg (by linarith : 0 ≤ 1 + T) J) (Real.one_le_rpow hY hρ))

/-- A bounded-height estimate and the elementary row count give a bound at
every height, with the same threshold for all parameters and heights. -/
theorem all_height_density_of_bounded_height
    {α : Type*} (N : α → ℝ → ℝ → ℝ) (ρ : α → ℝ)
    (C D Y₀ τ : ℝ) (J : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hρ : ∀ p, 0 ≤ ρ p)
    (hJ : 1 ≤ τ * (J : ℝ))
    (hbounded : ∀ Y, Y₀ ≤ Y → 1 ≤ Y → ∀ p T, 0 ≤ T → T ≤ Y ^ τ →
      N p Y T ≤ C * Y ^ ρ p)
    (hcount : ∀ Y, 1 ≤ Y → ∀ p T, 0 ≤ T → N p Y T ≤ D * Y) :
    ∀ Y, max 1 Y₀ ≤ Y → ∀ p T, 0 ≤ T →
      N p Y T ≤ max C D * (1 + T) ^ J * Y ^ ρ p := by
  intro Y hY p T hT
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hY₀ : Y₀ ≤ Y := (le_max_right _ _).trans hY
  have hYρ : 0 ≤ Y ^ ρ p := Real.rpow_nonneg (zero_le_one.trans hY1) _
  have hweight : 1 ≤ (1 + T) ^ J := one_le_pow₀ (by linarith : 1 ≤ 1 + T)
  by_cases hsmall : T ≤ Y ^ τ
  · calc
      N p Y T ≤ C * Y ^ ρ p := hbounded Y hY₀ hY1 p T hT hsmall
      _ ≤ max C D * Y ^ ρ p := mul_le_mul_of_nonneg_right (le_max_left _ _) hYρ
      _ ≤ max C D * (1 + T) ^ J * Y ^ ρ p :=
        mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (hC.trans (le_max_left _ _)) hweight) hYρ
  · calc
      N p Y T ≤ D * Y := hcount Y hY1 p T hT
      _ ≤ D * ((1 + T) ^ J * Y ^ ρ p) :=
        mul_le_mul_of_nonneg_left
          (scale_le_height_weight hY1 (le_of_not_ge hsmall) (hρ p) hJ) hD
      _ ≤ max C D * ((1 + T) ^ J * Y ^ ρ p) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _)
          (mul_nonneg (zero_le_one.trans hweight) hYρ)
      _ = max C D * (1 + T) ^ J * Y ^ ρ p := (mul_assoc _ _ _).symm

/-- A threshold chosen before all parameters and bounded heights extends to
a threshold chosen before all parameters and arbitrary heights. -/
theorem eventually_all_height_density_of_bounded_height
    {α : Type*} (N : α → ℝ → ℝ → ℝ) (ρ : α → ℝ)
    (C D τ : ℝ) (J : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hρ : ∀ p, 0 ≤ ρ p)
    (hJ : 1 ≤ τ * (J : ℝ))
    (hbounded : ∀ᶠ Y : ℝ in atTop, ∀ p T, 0 ≤ T → T ≤ Y ^ τ →
      N p Y T ≤ C * Y ^ ρ p)
    (hcount : ∀ Y, 1 ≤ Y → ∀ p T, 0 ≤ T → N p Y T ≤ D * Y) :
    ∀ᶠ Y : ℝ in atTop, ∀ p T, 0 ≤ T →
      N p Y T ≤ max C D * (1 + T) ^ J * Y ^ ρ p := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 hbounded
  apply eventually_atTop.2
  refine ⟨max 1 Y₀, ?_⟩
  exact all_height_density_of_bounded_height N ρ C D Y₀ τ J hC hD hρ hJ
    (fun Y hY _ => hY₀ Y hY) hcount

#print axioms scale_le_height_weight
#print axioms all_height_density_of_bounded_height
#print axioms eventually_all_height_density_of_bounded_height

end OAI.SevenEighths.LocalMoment
