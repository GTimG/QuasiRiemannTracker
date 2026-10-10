import Cycle25.Numerator.Holder
import Cycle25.Numerator.Damping
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact amplitude-bin exponent extracted from the weighted fourth moment. -/
noncomputable section
open scoped BigOperators
namespace Cycle25.Numerator

theorem rpow_fourth (U e : ℝ) (hU : 0 ≤ U) : (U^e)^4 = U^(4*e) := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hU]
  congr 1
  ring

theorem weighted_amplitude_bin {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (U R total selected epsilon Ccount Cmoment : ℝ)
    (hU : 0 < U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment)
    (hcard : (s.card : ℝ) ≤ Ccount * U^R)
    (hselected : ∀ i ∈ s, U^selected ≤ ‖Q i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^total)
    (henergy : (∑ i ∈ s, ‖S i‖^4 * ‖Q i‖^2) ≤ Cmoment * U^(1+epsilon)) :
    (∑ i ∈ s, ‖S i * P i‖) ≤
      Ccount * Cmoment * U^(total-selected/2+(3*R+1+epsilon)/4) := by
  have hL : 0 < U^selected := Real.rpow_pos_of_pos hU _
  have hh := weighted_row_holder_with_full s S Q P (U^selected) (U^total)
    hL.le (Real.rpow_nonneg hU.le _) hselected hfull
  have hpow (e : ℝ) (n : ℕ) : (U^e)^n = U^(e*n) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
  have hcomb : (U^total)^4 * (Ccount * U^R)^3 * (Cmoment * U^(1+epsilon)) =
      Ccount^3 * Cmoment * U^(4*total+3*R+1+epsilon) := by
    rw [mul_pow,hpow,hpow]
    rw [show total*(4:ℕ) = 4*total by ring,show R*(3:ℕ) = 3*R by ring]
    calc
      _ = Ccount^3 * Cmoment * ((U^(4*total) * U^(3*R))*U^(1+epsilon)) := by ring
      _ = _ := by rw [←Real.rpow_add hU,←Real.rpow_add hU]; congr 2; ring
  have htarget : (U^selected)^2 *
      (Ccount*Cmoment*U^(total-selected/2+(3*R+1+epsilon)/4))^4 =
      Ccount^4 * Cmoment^4 * U^(4*total+3*R+1+epsilon) := by
    rw [mul_pow,mul_pow,hpow,hpow]
    calc
      _ = Ccount^4 * Cmoment^4 *
          (U^(selected*2) * U^((total-selected/2+(3*R+1+epsilon)/4)*4)) := by ring
      _ = _ := by rw [←Real.rpow_add hU]; congr 2; ring
  have hconst : Ccount^3 * Cmoment ≤ Ccount^4 * Cmoment^4 := by
    have hc0 : 0 ≤ Ccount := le_trans zero_le_one hc
    have hm0 : 0 ≤ Cmoment := le_trans zero_le_one hm
    have hc' : Ccount^3 ≤ Ccount^4 := pow_le_pow_right₀ hc (by norm_num)
    have hm' : Cmoment ≤ Cmoment^4 := by
      simpa only [pow_one] using pow_le_pow_right₀ hm (show 1 ≤ 4 by norm_num)
    exact mul_le_mul hc' hm' hm0 (by positivity)
  have hh' : (U^selected)^2 * (∑ i ∈ s, ‖S i * P i‖)^4 ≤
      (U^selected)^2 * (Ccount*Cmoment*U^(total-selected/2+(3*R+1+epsilon)/4))^4 := by
    calc
      _ ≤ (U^total)^4 * (s.card : ℝ)^3 * (Cmoment * U^(1+epsilon)) :=
        hh.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
      _ ≤ (U^total)^4 * (Ccount*U^R)^3 * (Cmoment * U^(1+epsilon)) := by
        gcongr
      _ = Ccount^3*Cmoment*U^(4*total+3*R+1+epsilon) := hcomb
      _ ≤ Ccount^4*Cmoment^4*U^(4*total+3*R+1+epsilon) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hU.le _)
      _ = _ := htarget.symm
  have hf := (mul_le_mul_iff_right₀ (sq_pos_of_pos hL)).mp hh'
  exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (by have hc0 := le_trans zero_le_one hc; have hm0 := le_trans zero_le_one hm; positivity)
    (by norm_num : (4 : ℕ) ≠ 0)).mp hf

/-- A bounded dilation box pays for the lost selected-prime capacity.  The
box width xi appears only as the explicit small exponent loss delta*xi/4. -/
theorem weighted_dilation_bin {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (κ U R q L z v xi delta loss epsilon Ccount Cmoment : ℝ)
    (hκ : 7 / 10 ≤ κ)
    (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta / 2) (hv : 0 ≤ v) (hxi : 0 ≤ xi)
    (hcard : (s.card : ℝ) ≤ Ccount * U^R)
    (hselected : ∀ i ∈ s, U^(q*selectedCapacity κ z (v+xi)-loss) ≤ ‖Q i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^(q*L))
    (henergy : (∑ i ∈ s, ‖S i‖^4 * ‖Q i‖^2) ≤ Cmoment * U^(1+epsilon)) :
    U^(-delta*v/4) * (∑ i ∈ s, ‖S i * P i‖) ≤
      Ccount * Cmoment * U^(q*L-q*z/2+(3*R+1+epsilon)/4+loss/2+delta*xi/4-
        11*delta*(v+xi)/84) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hh := weighted_amplitude_bin s S Q P U R (q*L)
    (q*selectedCapacity κ z (v+xi)-loss) epsilon Ccount Cmoment hU0 hc hm
    hcard hselected hfull henergy
  have hd := capacity_damping_uniform hκ hq hqdelta (add_nonneg hv hxi) (z := z)
  calc
    _ ≤ U^(-delta*v/4) *
        (Ccount*Cmoment*U^(q*L-(q*selectedCapacity κ z (v+xi)-loss)/2+(3*R+1+epsilon)/4)) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hU0.le _)
    _ = (Ccount*Cmoment) * (U^(-delta*v/4) *
        U^(q*L-(q*selectedCapacity κ z (v+xi)-loss)/2+(3*R+1+epsilon)/4)) := by ring
    _ = Ccount*Cmoment*U^(-delta*v/4+q*L-
        (q*selectedCapacity κ z (v+xi)-loss)/2+(3*R+1+epsilon)/4) := by
      rw [←Real.rpow_add hU0]
      congr 1
      congr 1
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by have hc0 := le_trans zero_le_one hc; have hm0 := le_trans zero_le_one hm; positivity)
      apply Real.rpow_le_rpow_of_exponent_le hU
      linarith

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
