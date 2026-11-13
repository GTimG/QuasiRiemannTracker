/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.InBallSum

/-!
# Inverse.Poisson.StepBounds — the numerical constants of the Poisson step

Logarithm bookkeeping (`1 + log₂ Λ ≤ (1 + 1/(η log 2)) Λ^η`), the rapid-tail constant
(`Cl · 128² Λ³ ≤ Cw 128² 2 bl^(7+2At)` once `κ At ≥ 14`), and the definitions of the two
constants `cIn`, `cDt` of the step.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI OAI.ActualEisensteinCubic
open EisensteinSchwartzPoisson (paperRadialFourier)
open OAI.RayFourExpansion (RayCharacter gCoeff crossCoeff)

theorem logb_two_mul' (Λ : ℝ) (hΛ : 0 < Λ) : Real.logb 2 (2 * Λ) = 1 + Real.logb 2 Λ := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  simp only [Real.logb]
  rw [Real.log_mul (by norm_num) hΛ.ne', add_div, div_self hl2]

theorem logb_two_mul_sq (Λ : ℝ) (hΛ : 0 < Λ) :
    Real.logb 2 (2 * Λ ^ 2) = 1 + 2 * Real.logb 2 Λ := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  simp only [Real.logb]
  rw [Real.log_mul (by norm_num) (pow_pos hΛ 2).ne', Real.log_pow]
  push_cast
  rw [add_div, div_self hl2, mul_div_assoc]

theorem one_add_logb_le (Λ η : ℝ) (hΛ : 1 ≤ Λ) (hη : 0 < η) :
    1 + Real.logb 2 Λ ≤ (1 + 1 / (η * Real.log 2)) * Λ ^ η := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : 1 ≤ Λ ^ η := Real.one_le_rpow hΛ hη.le
  have h2 : Real.log Λ ≤ Λ ^ η / η := Real.log_le_rpow_div (by linarith) hη
  have h3 : Real.logb 2 Λ ≤ Λ ^ η / (η * Real.log 2) := by
    simp only [Real.logb]
    rw [div_le_div_iff₀ hl2 (mul_pos hη hl2)]
    have h4 := mul_le_mul_of_nonneg_right h2 (mul_pos hη hl2).le
    calc Real.log Λ * (η * Real.log 2) ≤ Λ ^ η / η * (η * Real.log 2) := h4
      _ = Λ ^ η * Real.log 2 := by rw [div_mul_eq_mul_div, div_eq_iff hη.ne']; ring
  calc 1 + Real.logb 2 Λ ≤ Λ ^ η + Λ ^ η / (η * Real.log 2) := by linarith
    _ = (1 + 1 / (η * Real.log 2)) * Λ ^ η := by ring

theorem ell_pow_le (bl Z N' η : ℝ) (n : ℕ) (hbl : 1 ≤ bl) (hZ : 1 ≤ Z) (hN0 : 0 ≤ N')
    (hN2 : N' ≤ 2) (hη : 0 < η) :
    (1 + Real.logb 2 (bl * Z ^ N')) ^ n ≤
      ((1 + 1 / (η * Real.log 2)) * bl ^ η) ^ n * Z ^ (2 * η * n) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hZ1 : 1 ≤ Z ^ N' := Real.one_le_rpow hZ hN0
  have hΛ : 1 ≤ bl * Z ^ N' := one_le_mul_of_one_le_of_one_le hbl hZ1
  have h0 : 0 ≤ 1 + Real.logb 2 (bl * Z ^ N') := by
    have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hΛ; linarith
  have hA : 0 ≤ 1 + 1 / (η * Real.log 2) :=
    add_nonneg zero_le_one (div_nonneg zero_le_one (mul_pos hη hl2).le)
  have h1 := one_add_logb_le _ η hΛ hη
  have hblη : 0 ≤ bl ^ η := Real.rpow_nonneg (by linarith) _
  have h2 : (bl * Z ^ N') ^ η ≤ bl ^ η * Z ^ (2 * η) := by
    rw [Real.mul_rpow (by linarith) (by linarith), ← Real.rpow_mul (by linarith)]
    apply mul_le_mul_of_nonneg_left _ hblη
    exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)
  calc (1 + Real.logb 2 (bl * Z ^ N')) ^ n
      ≤ ((1 + 1 / (η * Real.log 2)) * (bl * Z ^ N') ^ η) ^ n := pow_le_pow_left₀ h0 h1 n
    _ ≤ ((1 + 1 / (η * Real.log 2)) * (bl ^ η * Z ^ (2 * η))) ^ n :=
        pow_le_pow_left₀ (mul_nonneg hA (Real.rpow_nonneg (by linarith) _))
          (mul_le_mul_of_nonneg_left h2 hA) n
    _ = ((1 + 1 / (η * Real.log 2)) * bl ^ η) ^ n * Z ^ (2 * η * n) := by
        rw [← mul_assoc, mul_pow, Real.rpow_mul_natCast (by linarith)]

/-- The rapid-tail constant. -/
theorem tail_const_le (Cw bl Z N' κ : ℝ) (At : ℕ) (hCw : 0 ≤ Cw) (hbl : 1 ≤ bl) (hZ : 1 ≤ Z)
    (hN0 : 0 ≤ N') (hN2 : N' ≤ 2) (hAt : 14 ≤ κ * At) :
    Cw * (1 + (bl * Z ^ N') ^ 4) / (1 + Z ^ κ / bl ^ 2) ^ At * (128 ^ 2 * (bl * Z ^ N') ^ 3) ≤
      Cw * 128 ^ 2 * 2 * bl ^ (7 + 2 * At) := by
  have hZ0 : 0 < Z := by linarith
  have hX1 : 1 ≤ Z ^ N' := Real.one_le_rpow hZ hN0
  have hbl0 : 0 < bl := by linarith
  have hT : 0 ≤ Z ^ κ / bl ^ 2 := div_nonneg (Real.rpow_pos_of_pos hZ0 _).le (by positivity)
  have hP : 0 < (1 + Z ^ κ / bl ^ 2) ^ At := pow_pos (by linarith) _
  have hΛ : 1 ≤ bl * Z ^ N' := one_le_mul_of_one_le_of_one_le hbl hX1
  rw [div_mul_eq_mul_div, div_le_iff₀ hP]
  have h1 : 1 + (bl * Z ^ N') ^ 4 ≤ 2 * (bl * Z ^ N') ^ 4 := by
    have := one_le_pow₀ (n := 4) hΛ; linarith
  have h2 : (Z ^ N') ^ 7 ≤ (Z ^ κ) ^ At := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ0.le, ← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    push_cast; nlinarith
  have h3 : (Z ^ κ) ^ At ≤ bl ^ (2 * At) * (1 + Z ^ κ / bl ^ 2) ^ At := by
    have hblne : bl ≠ 0 := hbl0.ne'
    have he : Z ^ κ = bl ^ 2 * (Z ^ κ / bl ^ 2) := by field_simp
    calc (Z ^ κ) ^ At = (bl ^ 2 * (Z ^ κ / bl ^ 2)) ^ At := by rw [← he]
      _ = bl ^ (2 * At) * (Z ^ κ / bl ^ 2) ^ At := by rw [mul_pow, ← pow_mul]
      _ ≤ bl ^ (2 * At) * (1 + Z ^ κ / bl ^ 2) ^ At :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT (by linarith) At) (pow_nonneg hbl0.le _)
  have hX0 : 0 ≤ (Z ^ N') ^ 7 := pow_nonneg (by linarith) 7
  calc Cw * (1 + (bl * Z ^ N') ^ 4) * (128 ^ 2 * (bl * Z ^ N') ^ 3)
      ≤ Cw * (2 * (bl * Z ^ N') ^ 4) * (128 ^ 2 * (bl * Z ^ N') ^ 3) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCw)
          (mul_nonneg (by norm_num) (pow_nonneg (by linarith) 3))
    _ = Cw * 128 ^ 2 * 2 * bl ^ 7 * (Z ^ N') ^ 7 := by ring
    _ ≤ Cw * 128 ^ 2 * 2 * bl ^ 7 * (bl ^ (2 * At) * (1 + Z ^ κ / bl ^ 2) ^ At) :=
        mul_le_mul_of_nonneg_left (h2.trans h3)
          (mul_nonneg (mul_nonneg (mul_nonneg hCw (by norm_num)) (by norm_num)) (pow_nonneg hbl0.le 7))
    _ = Cw * 128 ^ 2 * 2 * bl ^ (7 + 2 * At) * (1 + Z ^ κ / bl ^ 2) ^ At := by
        rw [pow_add]; ring

/-- The cross-phase mass. -/
def crossMass : ℝ := ∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖

/-- `∫ (1+|t|)^(-2)`. -/
def c2Int : ℝ := ∫ t : ℝ, (1 + ‖t‖) ^ (-(2 : ℝ))

/-- The in-ball constant. -/
def cIn (Kslots d : ℕ) (b' : 𝓢(ℝ, ℂ)) (Cb Cd η bl : ℝ) : ℝ :=
  Cb * crossMass * 2 * (∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d)) * c2Int *
    (gSum * 2 ^ Kslots * (∫ τ : ℝ, ‖b' τ‖) / 2 * 4 ^ Kslots * 768 *
      ((1 + 1 / (η * Real.log 2)) * bl ^ η) ^ (2 * Kslots + 2)) *
    (2 ^ Kslots * gSum) * Cd ^ 3

/-- The diagonal and tail constant. -/
def cDt (Cw bl : ℝ) (At : ℕ) : ℝ :=
  gSum ^ 2 * (‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ +
    Cw * 128 ^ 2 * 2 * bl ^ (7 + 2 * At))

theorem crossMass_nonneg : 0 ≤ crossMass :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem c2Int_nonneg : 0 ≤ c2Int :=
  integral_nonneg fun t => Real.rpow_nonneg (by positivity) _

theorem cIn_nonneg (Kslots d : ℕ) (b' : 𝓢(ℝ, ℂ)) (Cb Cd η bl : ℝ) (hCb : 0 ≤ Cb) (hCd : 0 ≤ Cd)
    (hη : 0 < η) (hbl : 0 ≤ bl) : 0 ≤ cIn Kslots d b' Cb Cd η bl := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : 0 ≤ ∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d) := integral_nonneg fun τ => by positivity
  have h2 : 0 ≤ ∫ τ : ℝ, ‖b' τ‖ := integral_nonneg fun τ => norm_nonneg _
  have hA : 0 ≤ 1 + 1 / (η * Real.log 2) :=
    add_nonneg zero_le_one (div_nonneg zero_le_one (mul_pos hη hl2).le)
  have hblη : 0 ≤ bl ^ η := Real.rpow_nonneg hbl _
  unfold cIn
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCb
    crossMass_nonneg) (by norm_num)) h1) c2Int_nonneg) ?_) ?_) (pow_nonneg hCd 3)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg gSum_nonneg
      (pow_nonneg (by norm_num) _)) h2) (by norm_num)) (pow_nonneg (by norm_num) _)) (by norm_num))
      (pow_nonneg (mul_nonneg hA hblη) _)
  · exact mul_nonneg (pow_nonneg (by norm_num) _) gSum_nonneg

theorem cDt_nonneg (Cw bl : ℝ) (At : ℕ) (hCw : 0 ≤ Cw) (hbl : 0 ≤ bl) : 0 ≤ cDt Cw bl At := by
  unfold cDt
  exact mul_nonneg (sq_nonneg _) (add_nonneg (norm_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg hCw (by norm_num)) (by norm_num)) (pow_nonneg hbl _)))

end
end Qrh.MarkedAnchor.Inverse.Poisson
