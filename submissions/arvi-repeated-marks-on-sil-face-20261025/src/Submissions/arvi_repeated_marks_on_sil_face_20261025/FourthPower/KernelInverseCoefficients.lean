/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
The coefficient-induction pattern follows PR69 TwoIdeal.CoefficientBounds,
but the recurrence here is derived for the new fifth-free kernel itself.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.KernelCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelInverseCoefficients
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal
open KernelFormal KernelForwardMass KernelCoefficients

def shiftCoeff (n : Exponent) (j k : ℕ) : ℤ :=
  if exponent j k ≤ n then reciprocalCoeff (n-exponent j k) else 0

theorem coeff_shift (n : Exponent) (j k : ℕ) :
    MvPowerSeries.coeff n ((formalX^j*formalY^k)*reciprocalSeries) = shiftCoeff n j k := by
  rw [formal_power_monomial,MvPowerSeries.coeff_monomial_mul]
  simp only [shiftCoeff,reciprocalCoeff,one_mul]

theorem reciprocal_recurrence (n : Exponent) :
    reciprocalCoeff n + ∑ i : Fin 11, ordinaryCoefficient i.succ *
      shiftCoeff n (ordinaryExponent i.succ).1 (ordinaryExponent i.succ).2 =
        if n=0 then 1 else 0 := by
  have h := congrArg (MvPowerSeries.coeff n) kernel_reciprocal
  rw [ordinary_series_expansion,Finset.sum_mul,map_sum] at h
  have hterm (i : Fin 12) : MvPowerSeries.coeff n
      ((ordinaryCoefficient i • (formalX^(ordinaryExponent i).1*formalY^(ordinaryExponent i).2))*reciprocalSeries) =
      ordinaryCoefficient i * shiftCoeff n (ordinaryExponent i).1 (ordinaryExponent i).2 := by
    fin_cases i <;> dsimp [ordinaryCoefficient,ordinaryExponent] <;>
      simp only [one_smul,neg_one_smul,neg_mul,map_neg,coeff_shift,one_mul]
  simp_rw [hterm] at h
  rw [MvPowerSeries.coeff_one] at h
  rw [Fin.sum_univ_succ] at h
  have hz : ordinaryCoefficient 0 * shiftCoeff n (ordinaryExponent 0).1 (ordinaryExponent 0).2 =
      reciprocalCoeff n := by
    norm_num [ordinaryCoefficient,ordinaryExponent,shiftCoeff,exponent]
  rw [hz] at h
  exact h

theorem nonconstant_degree (i : Fin 11) :
    5 ≤ (ordinaryExponent i.succ).1+(ordinaryExponent i.succ).2 := by
  fin_cases i <;> norm_num [ordinaryExponent]

theorem nonconstant_abs (i : Fin 11) : |(ordinaryCoefficient i.succ : ℝ)| = 1 := by
  fin_cases i <;> norm_num [ordinaryCoefficient]

theorem shift_small (n : Exponent) (hn : degree n < 5) (i : Fin 11) :
    shiftCoeff n (ordinaryExponent i.succ).1 (ordinaryExponent i.succ).2 = 0 := by
  rw [shiftCoeff,ite_eq_right]
  intro h
  obtain ⟨hj,hk⟩ := (exponent_le_iff _ _ _).mp h
  have hi := nonconstant_degree i
  unfold degree at hn
  omega

theorem reciprocalCoeff_small_degree (n : Exponent) (hn : n ≠ 0) (hd : degree n < 5) :
    reciprocalCoeff n = 0 := by
  have h := reciprocal_recurrence n
  simp only [shift_small n hd,mul_zero,Finset.sum_const_zero,add_zero,ite_eq_right hn] at h
  exact h

theorem reciprocal_abs_recurrence (n : Exponent) (hn : n ≠ 0) :
    |(reciprocalCoeff n : ℝ)| ≤ ∑ i : Fin 11,
      |(shiftCoeff n (ordinaryExponent i.succ).1 (ordinaryExponent i.succ).2 : ℝ)| := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (reciprocal_recurrence n)
  rw [ite_eq_right hn] at h
  push_cast at h
  have he : (reciprocalCoeff n : ℝ) = -(∑ i : Fin 11, (ordinaryCoefficient i.succ : ℝ)*
      (shiftCoeff n (ordinaryExponent i.succ).1 (ordinaryExponent i.succ).2 : ℝ)) := by linarith
  rw [he,abs_neg]
  calc
    _ ≤ ∑ i : Fin 11, |(ordinaryCoefficient i.succ : ℝ)*
        (shiftCoeff n (ordinaryExponent i.succ).1 (ordinaryExponent i.succ).2 : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul,nonconstant_abs,one_mul]

/-- A uniform geometric coefficient majorant, proved for the actual inverse.
The 11 nonconstant shifts all have total degree at least five. -/
theorem reciprocalCoeff_abs_bound (n : Exponent) :
    |(reciprocalCoeff n : ℝ)| ≤ (2 : ℝ)^(degree n) := by
  have aux : ∀ d : ℕ, ∀ n : Exponent, degree n=d →
      |(reciprocalCoeff n : ℝ)| ≤ (2 : ℝ)^d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro n hn
      by_cases hz : d=0
      · have hn0 : n=0 := by
          apply (exponent_zero_iff n).mpr
          unfold degree at hn
          omega
        subst n
        simp [reciprocalCoeff_zero,hz]
      have hn0 : n ≠ 0 := by
        intro he
        simp [he,degree] at hn
        omega
      by_cases hd : d < 5
      · rw [reciprocalCoeff_small_degree n hn0 (by omega)]
        simp only [Int.cast_zero,abs_zero]
        positivity
      have hd5 : 5 ≤ d := by omega
      have hshift (i : Fin 11) :
          |(shiftCoeff n (ordinaryExponent i.succ).1 (ordinaryExponent i.succ).2 : ℝ)| ≤
            (2 : ℝ)^(d-5) := by
        by_cases hle : exponent (ordinaryExponent i.succ).1 (ordinaryExponent i.succ).2 ≤ n
        · rw [shiftCoeff,ite_eq_left hle]
          have he := degree_sub_exponent n _ _ hle
          have hi := nonconstant_degree i
          have hlt : degree (n-exponent (ordinaryExponent i.succ).1 (ordinaryExponent i.succ).2) < d := by omega
          have hpow : degree (n-exponent (ordinaryExponent i.succ).1 (ordinaryExponent i.succ).2) ≤ d-5 := by omega
          exact (ih _ hlt _ rfl).trans (pow_le_pow_right₀ (by norm_num) hpow)
        · rw [shiftCoeff,ite_eq_right hle]
          simp only [Int.cast_zero,abs_zero]
          positivity
      calc
        _ ≤ ∑ i : Fin 11, |(shiftCoeff n (ordinaryExponent i.succ).1 (ordinaryExponent i.succ).2 : ℝ)| :=
          reciprocal_abs_recurrence n hn0
        _ ≤ ∑ _i : Fin 11, (2 : ℝ)^(d-5) := Finset.sum_le_sum (fun i _ => hshift i)
        _ = 11*(2 : ℝ)^(d-5) := by simp
        _ ≤ (2 : ℝ)^5*(2 : ℝ)^(d-5) := by nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) (d-5)]
        _ = (2 : ℝ)^d := by rw [← pow_add,Nat.add_sub_of_le hd5]
  exact aux (degree n) n rfl

end
end Candidate.FourthPower.KernelInverseCoefficients
