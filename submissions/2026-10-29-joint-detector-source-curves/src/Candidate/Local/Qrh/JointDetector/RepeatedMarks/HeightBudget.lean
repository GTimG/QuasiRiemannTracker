/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false

/-- A fixed polynomial height allowance pays the full trivial row count
in the large-height regime. -/
theorem large_height_budget (τ : ℝ) (hτ : 0<τ) :
    ∃J : ℕ,∀U T : ℝ,1≤U → 0≤T → U^τ≤T → U≤(1+T)^J := by
  let J : ℕ:=⌈1/τ⌉₊
  have hJ : 1/τ≤(J:ℝ) := Nat.le_ceil _
  have hτJ : 1≤τ*(J:ℝ) := by
    have hh := (div_le_iff₀ hτ).mp hJ
    linarith
  refine ⟨J,?_⟩
  intro U T hU hT hUT
  calc U=U^(1:ℝ) := (Real.rpow_one U).symm
    _ ≤ U^(τ*(J:ℝ)) := Real.rpow_le_rpow_of_exponent_le hU hτJ
    _ = (U^τ)^J := Real.rpow_mul_natCast (by linarith) τ J
    _ ≤ (1+T)^J := pow_le_pow_left₀ (Real.rpow_nonneg (show 0≤U by linarith) τ) (by linarith) J

/-- The moment-degree cost in the small-height regime is an arbitrarily
small power once the height power is selected after that degree. -/
theorem small_height_budget {U τ A : ℝ} (J : ℕ)
    (hU : 1≤U) (hτ : 0≤τ) (hA : 0≤A) :
    (1+A*U^τ)^J≤(1+A)^J*U^(τ*(J:ℝ)) := by
  have hUpow : 1≤U^τ := Real.one_le_rpow hU hτ
  have hu : 0≤U^τ := Real.rpow_nonneg (by linarith) τ
  calc _ ≤ ((1+A)*U^τ)^J := pow_le_pow_left₀ (show 0≤1+A*U^τ by positivity) (by nlinarith) J
    _ = (1+A)^J*(U^τ)^J := mul_pow _ _ _
    _ = _ := by rw [Real.rpow_mul_natCast (by linarith) τ J]

end
end Qrh.JointDetector.RepeatedMarks
