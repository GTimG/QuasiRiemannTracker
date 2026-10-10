import Cycle25.Numerator.Imported.NumeratorLocalCoefficients
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A finite Fourier extraction of coefficient mass from a uniform local bound.
Unlike a pointwise estimate at a single `w`, the four evaluations below determine
all coefficients of the local quadratic polynomial. -/
noncomputable section
namespace Cycle25.Weighted.Numerator

private theorem average_four_norm_le (a b c d : ℂ) (B : ℝ)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B) (hd : ‖d‖ ≤ B) :
    ‖(a + b + c + d) / 4‖ ≤ B := by
  rw [norm_div]
  rw [show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  have h := (norm_add_le (a + b + c) d).trans
    (add_le_add ((norm_add_le (a + b) c).trans
      (add_le_add (norm_add_le a b) le_rfl)) le_rfl)
  linarith

theorem quadratic_coefficients_of_four_bounds (a b c : ℂ) (B : ℝ)
    (h₁ : ‖quadratic a b c 1‖ ≤ B) (h₂ : ‖quadratic a b c (-1)‖ ≤ B)
    (h₃ : ‖quadratic a b c Complex.I‖ ≤ B)
    (h₄ : ‖quadratic a b c (-Complex.I)‖ ≤ B) :
    ‖a‖ ≤ B ∧ ‖b‖ ≤ B ∧ ‖c‖ ≤ B := by
  have ha : a = (quadratic a b c 1 + quadratic a b c (-1) +
      quadratic a b c Complex.I + quadratic a b c (-Complex.I)) / 4 := by
    simp [quadratic, Complex.I_sq]
    ring
  have hb : b = (quadratic a b c 1 + -(quadratic a b c (-1)) +
      (-Complex.I * quadratic a b c Complex.I) +
      (Complex.I * quadratic a b c (-Complex.I))) / 4 := by
    simp [quadratic, Complex.I_sq]
    ring_nf
    simp [Complex.I_sq]
    ring
  have hc : c = (quadratic a b c 1 + quadratic a b c (-1) +
      -(quadratic a b c Complex.I) + -(quadratic a b c (-Complex.I))) / 4 := by
    simp [quadratic, Complex.I_sq]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]
    exact average_four_norm_le _ _ _ _ B h₁ h₂ h₃ h₄
  · rw [hb]
    apply average_four_norm_le _ _ _ _ B h₁
    · simpa only [norm_neg] using h₂
    · simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul] using h₃
    · simpa only [norm_mul, Complex.norm_I, one_mul] using h₄
  · rw [hc]
    exact average_four_norm_le _ _ _ _ B h₁ h₂
      (by simpa only [norm_neg] using h₃) (by simpa only [norm_neg] using h₄)

def quadraticMass (a b c : ℂ) (r : ℝ) : ℝ := ‖a‖ + ‖b‖ * r + ‖c‖ * r ^ 2

theorem quadraticMass_le_of_circle_bound (a b c : ℂ) (r B : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ T : ℂ, ‖T‖ = r → ‖quadratic a b c T‖ ≤ B) :
    quadraticMass a b c r ≤ 3 * B := by
  have he (T : ℂ) : quadratic a (b * r) (c * (r : ℂ) ^ 2) T =
      quadratic a b c ((r : ℂ) * T) := by unfold quadratic; ring
  have hn (T : ℂ) (hT : ‖T‖ = 1) : ‖(r : ℂ) * T‖ = r := by
    rw [norm_mul, hT, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hh := quadratic_coefficients_of_four_bounds a (b * r) (c * (r : ℂ) ^ 2) B
    (by rw [he]; exact hbound _ (hn 1 (by simp)))
    (by rw [he]; exact hbound _ (hn (-1) (by simp)))
    (by rw [he]; exact hbound _ (hn Complex.I (by simp)))
    (by rw [he]; exact hbound _ (hn (-Complex.I) (by simp)))
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at hh
  unfold quadraticMass
  linarith [hh.1, hh.2.1, hh.2.2]

theorem quadraticMass_mono (a b c : ℂ) (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) :
    quadraticMass a b c r ≤ quadraticMass a b c s := by
  unfold quadraticMass
  gcongr

/-- The complete vertical line visits the complete circle in the local variable.
This is why a bound uniform in the imaginary part really does control every local
coefficient, once the finite degree is known. -/
theorem vertical_cpow_surjective (Q sigma : ℝ) (hQ : 1 < Q) (T : ℂ)
    (hT : ‖T‖ = Q ^ (-sigma)) :
    ∃ w : ℂ, w.re = sigma ∧ (Q : ℂ) ^ (-w) = T := by
  have hQ0 : 0 < Q := lt_trans zero_lt_one hQ
  have hlog : Real.log Q ≠ 0 := ne_of_gt (Real.log_pos hQ)
  have hT0 : T ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hT
    exact (Real.rpow_pos_of_pos hQ0 (-sigma)).ne' hT.symm
  refine ⟨-Complex.log T / (Real.log Q : ℂ), ?_, ?_⟩
  · rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re, hT,
      Real.rpow_def_of_pos hQ0, Real.log_exp]
    field_simp
  · rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hQ0.ne'),
      ← Complex.ofReal_log hQ0.le]
    have hlogC : (Real.log Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
    have he : (Real.log Q : ℂ) * -(-Complex.log T / (Real.log Q : ℂ)) =
        Complex.log T := by field_simp
    rw [he, Complex.exp_log hT0]

/-- A uniform bound on one vertical line controls the absolute quadratic
coefficient mass, and all lines to its right. -/
theorem quadraticMass_le_of_vertical_bound (Q sigma tau B : ℝ) (a b c : ℂ)
    (hQ : 1 < Q) (hst : sigma ≤ tau)
    (hbound : ∀ w : ℂ, w.re = sigma →
      ‖quadratic a b c ((Q : ℂ) ^ (-w))‖ ≤ B) :
    quadraticMass a b c (Q ^ (-tau)) ≤ 3 * B := by
  apply (quadraticMass_mono a b c (Q ^ (-tau)) (Q ^ (-sigma))
    (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith))).trans
  apply quadraticMass_le_of_circle_bound a b c _ B (Real.rpow_nonneg (by linarith) _)
  intro T hT
  obtain ⟨w, hw, he⟩ := vertical_cpow_surjective Q sigma hQ T hT
  rw [← he]
  exact hbound w hw

theorem cubic_coefficients_of_four_bounds (a b c d : ℂ) (B : ℝ)
    (h₁ : ‖cubic a b c d 1‖ ≤ B) (h₂ : ‖cubic a b c d (-1)‖ ≤ B)
    (h₃ : ‖cubic a b c d Complex.I‖ ≤ B)
    (h₄ : ‖cubic a b c d (-Complex.I)‖ ≤ B) :
    ‖a‖ ≤ B ∧ ‖b‖ ≤ B ∧ ‖c‖ ≤ B ∧ ‖d‖ ≤ B := by
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]; ring
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Complex.I_sq]; norm_num
  have ha : a = (cubic a b c d 1 + cubic a b c d (-1) +
      cubic a b c d Complex.I + cubic a b c d (-Complex.I)) / 4 := by
    simp [cubic, Complex.I_sq, hI3]
    ring_nf
    simp [hI3]
  have hb : b = (cubic a b c d 1 + -(cubic a b c d (-1)) +
      (-Complex.I * cubic a b c d Complex.I) +
      (Complex.I * cubic a b c d (-Complex.I))) / 4 := by
    simp [cubic, Complex.I_sq, hI3]
    ring_nf
    simp [Complex.I_sq, hI3, hI4]
    ring
  have hc : c = (cubic a b c d 1 + cubic a b c d (-1) +
      -(cubic a b c d Complex.I) + -(cubic a b c d (-Complex.I))) / 4 := by
    simp [cubic, Complex.I_sq, hI3]
    ring_nf
    simp [hI3]
  have hd : d = (cubic a b c d 1 + -(cubic a b c d (-1)) +
      (Complex.I * cubic a b c d Complex.I) +
      (-Complex.I * cubic a b c d (-Complex.I))) / 4 := by
    simp [cubic, Complex.I_sq, hI3]
    ring_nf
    simp [Complex.I_sq, hI3, hI4]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha]
    exact average_four_norm_le _ _ _ _ B h₁ h₂ h₃ h₄
  · rw [hb]
    apply average_four_norm_le _ _ _ _ B h₁
    · simpa only [norm_neg] using h₂
    · simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul] using h₃
    · simpa only [norm_mul, Complex.norm_I, one_mul] using h₄
  · rw [hc]
    exact average_four_norm_le _ _ _ _ B h₁ h₂
      (by simpa only [norm_neg] using h₃) (by simpa only [norm_neg] using h₄)
  · rw [hd]
    apply average_four_norm_le _ _ _ _ B h₁
    · simpa only [norm_neg] using h₂
    · simpa only [norm_mul, Complex.norm_I, one_mul] using h₃
    · simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul] using h₄

def cubicMass (a b c d : ℂ) (r : ℝ) : ℝ :=
  ‖a‖ + ‖b‖ * r + ‖c‖ * r ^ 2 + ‖d‖ * r ^ 3

theorem cubicMass_le_of_circle_bound (a b c d : ℂ) (r B : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ T : ℂ, ‖T‖ = r → ‖cubic a b c d T‖ ≤ B) :
    cubicMass a b c d r ≤ 4 * B := by
  have he (T : ℂ) : cubic a (b * r) (c * (r : ℂ) ^ 2) (d * (r : ℂ) ^ 3) T =
      cubic a b c d ((r : ℂ) * T) := by unfold cubic; ring
  have hn (T : ℂ) (hT : ‖T‖ = 1) : ‖(r : ℂ) * T‖ = r := by
    rw [norm_mul, hT, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hh := cubic_coefficients_of_four_bounds a (b * r) (c * (r : ℂ) ^ 2)
    (d * (r : ℂ) ^ 3) B
    (by rw [he]; exact hbound _ (hn 1 (by simp)))
    (by rw [he]; exact hbound _ (hn (-1) (by simp)))
    (by rw [he]; exact hbound _ (hn Complex.I (by simp)))
    (by rw [he]; exact hbound _ (hn (-Complex.I) (by simp)))
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at hh
  unfold cubicMass
  linarith [hh.1, hh.2.1, hh.2.2.1, hh.2.2.2]

theorem cubicMass_mono (a b c d : ℂ) (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) :
    cubicMass a b c d r ≤ cubicMass a b c d s := by
  unfold cubicMass
  gcongr

theorem cubicMass_le_of_vertical_bound (Q sigma tau B : ℝ) (a b c d : ℂ)
    (hQ : 1 < Q) (hst : sigma ≤ tau)
    (hbound : ∀ w : ℂ, w.re = sigma →
      ‖cubic a b c d ((Q : ℂ) ^ (-w))‖ ≤ B) :
    cubicMass a b c d (Q ^ (-tau)) ≤ 4 * B := by
  apply (cubicMass_mono a b c d (Q ^ (-tau)) (Q ^ (-sigma))
    (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith))).trans
  apply cubicMass_le_of_circle_bound a b c d _ B (Real.rpow_nonneg (by linarith) _)
  intro T hT
  obtain ⟨w, hw, he⟩ := vertical_cpow_surjective Q sigma hQ T hT
  rw [← he]
  exact hbound w hw

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
