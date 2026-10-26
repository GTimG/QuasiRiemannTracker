/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103TwoIdeal.KernelCoefficients

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103TwoIdeal
noncomputable section

theorem abs_five_terms (a b c d e : ℝ) :
    |a+b+c-d-e| ≤ |a|+|b|+|c|+|d|+|e| := by
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self a,neg_abs_le a,le_abs_self b,neg_abs_le b,
    le_abs_self c,neg_abs_le c,le_abs_self d,neg_abs_le d,le_abs_self e,neg_abs_le e]

theorem inverseCoeff_abs_bound (n : Exponent) :
    |(inverseCoeff n : ℝ)| ≤ (3:ℝ)^(degree n) := by
  have aux : ∀ d : ℕ, ∀ n : Exponent, degree n=d →
      |(inverseCoeff n : ℝ)| ≤ (3:ℝ)^d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro n hn
      by_cases hd0 : d=0
      · have hdeg : degree n=0 := hn.trans hd0
        have hn0 : n=0 := by
          apply (exponent_zero_iff n).mpr
          unfold degree at hdeg
          omega
        subst n
        simp [inverseCoeff_zero,hd0]
      by_cases hd1 : d=1
      · have hdeg : degree n=1 := hn.trans hd1
        rw [inverseCoeff_degree_one n hdeg]
        simpa only [Int.cast_zero,abs_zero] using
          (pow_nonneg (by norm_num : (0:ℝ) ≤ 3) d)
      have hd : 2 ≤ d := by omega
      have hshift (i j : ℕ) (hij : 2 ≤ i+j) :
          |(shiftedInverseCoeff n i j : ℝ)| ≤ (3:ℝ)^(d-2) := by
        by_cases hle : exponent i j ≤ n
        · rw [shiftedInverseCoeff,ite_eq_left hle]
          have heq := degree_sub_exponent n i j hle
          have hlt : degree (n-exponent i j)<d := by omega
          have hpow : degree (n-exponent i j) ≤ d-2 := by omega
          exact (ih _ hlt _ rfl).trans (pow_le_pow_right₀ (by norm_num) hpow)
        · rw [shiftedInverseCoeff,ite_eq_right hle]
          simpa only [Int.cast_zero,abs_zero] using
            (pow_nonneg (by norm_num : (0:ℝ) ≤ 3) (d-2))
      have hn0 : n≠0 := by
        intro h
        simp [h,degree] at hn
        omega
      have hr := inverse_coefficient_recurrence n
      rw [ite_eq_right hn0] at hr
      have hrr := congrArg (fun z : ℤ => (z:ℝ)) hr
      push_cast at hrr
      have heq : (inverseCoeff n : ℝ) =
          (shiftedInverseCoeff n 2 0 : ℝ)+(shiftedInverseCoeff n 1 1 : ℝ)+
          (shiftedInverseCoeff n 0 2 : ℝ)-(shiftedInverseCoeff n 2 1 : ℝ)-
          (shiftedInverseCoeff n 1 2 : ℝ) := by linarith
      calc
        |(inverseCoeff n : ℝ)| ≤
            |(shiftedInverseCoeff n 2 0 : ℝ)|+|(shiftedInverseCoeff n 1 1 : ℝ)|+
            |(shiftedInverseCoeff n 0 2 : ℝ)|+|(shiftedInverseCoeff n 2 1 : ℝ)|+
            |(shiftedInverseCoeff n 1 2 : ℝ)| := by
          rw [heq]
          exact abs_five_terms _ _ _ _ _
        _ ≤ 5*(3:ℝ)^(d-2) := by
          linarith [hshift 2 0 (by decide),hshift 1 1 (by decide),hshift 0 2 (by decide),
            hshift 2 1 (by decide),hshift 1 2 (by decide)]
        _ ≤ (3:ℝ)^2*(3:ℝ)^(d-2) := by nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤3) (d-2)]
        _ = (3:ℝ)^d := by rw [← pow_add,Nat.add_sub_of_le hd]
  exact aux (degree n) n rfl

end
end QRH.Record1252270103TwoIdeal

#print axioms QRH.Record1252270103TwoIdeal.inverseCoeff_abs_bound
