/-
Moving the height of a plain sum into its profile.

`rowTwistedSum η m A z W t X = X^{it} · rowTwistedSum η m A z (twistProfile W 0 t) 0 X`, hence for a row
character `χ` of the row (`hrow`), `(√X)⁻¹ · rowTwistedSum η m A z W t X = X^{it} · polynomial χ false W X 0 t`,
and the height `t` can be carried by the profile `normTwistedSource W (t/2π)` at height `0`.
-/
import Submissions.arvi_selected_leaf.R1.RadRow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.TwistedReflection

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion HeckeFamily HeckeRowClosure HeckeDyadic
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O

theorem cpow_height_split (N X t : ℝ) (hN : 0 ≤ N) (hX : 0 < X) :
    (X : ℂ)^(Complex.I*t) * ((N/X : ℝ) : ℂ)^(Complex.I*t) = (N : ℂ)^(Complex.I*t) := by
  have h := Complex.mul_cpow_ofReal_nonneg hX.le (div_nonneg hN hX.le) (Complex.I*t)
  rw [← h]
  congr 2
  push_cast
  have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  field_simp

/-- The height of a plain sum moves into the profile. -/
theorem rowTwistedSum_twist (η : Character) (m A z : O) (W : ℝ → ℂ) (t X : ℝ) (hX : 0 < X) :
    rowTwistedSum η m A z W t X =
      (X : ℂ)^(Complex.I*t) * rowTwistedSum η m A z (twistProfile W 0 t) 0 X := by
  rw [rowTwistedSum_eq_weight, rowTwistedSum_eq_weight, ← tsum_mul_left]
  apply tsum_congr
  intro I
  change (idealCoeff η I * idealRowHom (m^6 * (A * z)) I * (Ideal.absNorm I : ℂ)^(Complex.I*t)) *
      W ((Ideal.absNorm I : ℝ)/X) =
    (X : ℂ)^(Complex.I*t) * ((idealCoeff η I * idealRowHom (m^6 * (A * z)) I *
      (Ideal.absNorm I : ℂ)^(Complex.I*(0:ℝ))) * twistProfile W 0 t ((Ideal.absNorm I : ℝ)/X))
  have hsplit := cpow_height_split (Ideal.absNorm I : ℝ) X t (Nat.cast_nonneg _) hX
  have hshift : -HeckeDyadic.shift 0 t = Complex.I*t := by simp [HeckeDyadic.shift]; ring
  simp only [twistProfile, hshift, Complex.ofReal_zero, mul_zero, Complex.cpow_zero, mul_one]
  rw [show ((Ideal.absNorm I : ℕ) : ℂ) = (((Ideal.absNorm I : ℕ) : ℝ) : ℂ) by norm_cast] at *
  rw [← hsplit]
  ring

/-- **The normalized plain sum is a row-character polynomial up to a unimodular factor.** -/
theorem plain_eq_polynomial (η χ : Character) (m A z : O)
    (hrow : ∀ n, elementCoeff χ n = rowTwist (elementHom η) m 1 (A*z) n)
    (W : ℝ → ℂ) (t X : ℝ) (hX : 0 < X) :
    (Real.sqrt X : ℂ)⁻¹ * rowTwistedSum η m A z W t X =
      (X : ℂ)^(Complex.I*t) * polynomial χ false W X 0 t := by
  rw [CenteredMomentDetectorDictionary.plain_polynomial_eq_row η χ m A z hrow W X 0 t hX,
    rowTwistedSum_twist η m A z W t X hX]
  ring

/-- The height carried by the profile. -/
theorem polynomial_height_profile (χ : Character) (W : ℝ → ℂ) (X t : ℝ) (hX : 0 < X) :
    polynomial χ false W X 0 t =
      polynomial χ false (CompletedHeight.normTwistedSource W (t/(2*Real.pi))) X 0 0 := by
  have h := CenteredMomentTwistedReflection.polynomial_twisted_source χ W X (t/(2*Real.pi)) hX
  have ht : 2*Real.pi*(t/(2*Real.pi)) = t := by field_simp
  rw [ht] at h
  exact h

theorem norm_height_factor (X t : ℝ) (hX : 0 < X) : ‖(X : ℂ)^(Complex.I*t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp

end
end QRH.ArviSelectedLeaf.R1
