/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The finite Hölder kernels are adapted from the retained PR67 weighted numerator,
with the original OpenAI/Collet/Levy/Gao attribution. This module has no source,
count, schedule or historic geometry instance. The selected prime factors retain
exponent two inside the fourth moment, with the full factors bounded separately. -/
import Candidate.C092.Physical
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace QRH.Cycle092.DirectEnergy.Packet
theorem sum_fourth_le_card_cube {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 4 := by
  have h₁ := Finset.sum_mul_sq_le_sq_mul_sq s f (fun _ => (1 : ℝ))
  have h₂ := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => f i ^ 2) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h₁ h₂
  have h₁' : ((∑ i ∈ s, f i) ^ 2) ^ 2 ≤
      ((∑ i ∈ s, f i ^ 2) * (s.card : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ (sq_nonneg _) h₁ 2
  have h₂' := mul_le_mul_of_nonneg_right h₂ (sq_nonneg (s.card : ℝ))
  simp only [← pow_mul] at h₂
  calc
    _ ≤ ((∑ i ∈ s, f i ^ 2) * (s.card : ℝ)) ^ 2 := by
      simpa only [← pow_mul] using h₁'
    _ = (s.card : ℝ) ^ 2 * (∑ i ∈ s, f i ^ 2) ^ 2 := by ring
    _ ≤ (s.card : ℝ) ^ 2 * ((∑ i ∈ s, f i ^ 4) * (s.card : ℝ)) :=
      mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
    _ = _ := by ring

/-- The exact fourth-power form of the weighted Hölder step.  Only a pointwise lower
bound for the selected prime product is required. -/
theorem weighted_row_holder {ι : Type*} (s : Finset ι) (S Q : ι → ℂ)
    (L : ℝ) (hL : 0 ≤ L) (hQ : ∀ i ∈ s, L ≤ ‖Q i‖) :
    L ^ 2 * (∑ i ∈ s, ‖S i‖) ^ 4 ≤
      (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4 * ‖Q i‖ ^ 2 := by
  calc
    _ ≤ L ^ 2 * ((s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4) :=
      mul_le_mul_of_nonneg_left (sum_fourth_le_card_cube s (fun i => ‖S i‖))
        (sq_nonneg _)
    _ = (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4 * L ^ 2 := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL (hQ i hi) 2)
        (by positivity)

/-- Full prime factors may be removed using their upper amplitude bound, while the
selected factors remain in the fourth moment. -/
theorem weighted_row_holder_with_full {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (L A : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hQ : ∀ i ∈ s, L ≤ ‖Q i‖) (hP : ∀ i ∈ s, ‖P i‖ ≤ A) :
    L ^ 2 * (∑ i ∈ s, ‖S i * P i‖) ^ 4 ≤
      A ^ 4 * (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4 * ‖Q i‖ ^ 2 := by
  have hsum : (∑ i ∈ s, ‖S i * P i‖) ≤ A * ∑ i ∈ s, ‖S i‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul, mul_comm A]
    exact mul_le_mul_of_nonneg_left (hP i hi) (norm_nonneg _)
  calc
    _ ≤ L ^ 2 * (A * ∑ i ∈ s, ‖S i‖) ^ 4 := by
      gcongr
    _ = A ^ 4 * (L ^ 2 * (∑ i ∈ s, ‖S i‖) ^ 4) := by ring
    _ ≤ A ^ 4 * ((s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4 * ‖Q i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (weighted_row_holder s S Q L hL hQ) (by positivity)
    _ = _ := by ring

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

theorem weighted_dilation_bin {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (y source d U R q L v xi ann delta loss epsilon Ccount Cmoment : ℝ)
    (hsource : 0 ≤ source)
    (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta / 2) (hv : 0 ≤ v) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hcard : (s.card : ℝ) ≤ Ccount * U^R)
    (hselected : ∀ i ∈ s, U^(q*QRH.Cycle092.Physical.Selection.scheduledCapacity y source d (2*(v+xi+ann))-loss) ≤ ‖Q i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^(q*L))
    (henergy : (∑ i ∈ s, ‖S i‖^4 * ‖Q i‖^2) ≤ Cmoment * U^(1+epsilon)) :
    U^(-delta*v/2) * (∑ i ∈ s, ‖S i * P i‖) ≤
      Ccount * Cmoment * U^(q*L-q*QRH.Cycle092.Physical.Selection.zeroCapacity y source d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2-
        2*(1/1000 : ℝ)*delta*(v+xi+ann)) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hh := weighted_amplitude_bin s S Q P U R (q*L)
    (q*QRH.Cycle092.Physical.Selection.scheduledCapacity y source d (2*(v+xi+ann))-loss) epsilon Ccount Cmoment hU0 hc hm
    hcard hselected hfull henergy
  have hdelta : 0 ≤ delta := by linarith
  have hdamp := QRH.Cycle092.Physical.Selection.capacity_damping
    (y:=y) (d:=d) hsource (by positivity : 0 ≤ 2*(v+xi+ann)) hq hqdelta hdelta
  calc
    _ ≤ U^(-delta*v/2) *
        (Ccount*Cmoment*U^(q*L-(q*QRH.Cycle092.Physical.Selection.scheduledCapacity y source d (2*(v+xi+ann))-loss)/2+(3*R+1+epsilon)/4)) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hU0.le _)
    _ = (Ccount*Cmoment) * (U^(-delta*v/2) *
        U^(q*L-(q*QRH.Cycle092.Physical.Selection.scheduledCapacity y source d (2*(v+xi+ann))-loss)/2+(3*R+1+epsilon)/4)) := by ring
    _ = Ccount*Cmoment*U^(-delta*v/2+q*L-
        (q*QRH.Cycle092.Physical.Selection.scheduledCapacity y source d (2*(v+xi+ann))-loss)/2+(3*R+1+epsilon)/4) := by
      rw [←Real.rpow_add hU0]
      congr 1
      congr 1
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by have hc0 := le_trans zero_le_one hc; have hm0 := le_trans zero_le_one hm; positivity)
      apply Real.rpow_le_rpow_of_exponent_le hU
      linarith


end QRH.Cycle092.DirectEnergy.Packet
#print axioms QRH.Cycle092.DirectEnergy.Packet.weighted_dilation_bin
