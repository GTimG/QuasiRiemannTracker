/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Absorption of the actual source and supported-witness height factors. -/
import Candidate.C092.transport.StrongPairOrdinaryErrors
import Candidate.C092.transport.WitnessRowSupActualRows

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped BigOperators
open QRH.Cycle092.WitnessRowSup.Actual

/-- The sum of the actual finite source degree and actual witness polynomial
order determines the frequency loss. The dyad is bounded by the early I. -/
theorem ordinary_height_payment {U d dmax τ tMark tLong height : ℝ}
    (degree J I i : ℕ) (hU : 1 < U) (hd : d ≤ dmax) (hdmax : 0 < dmax)
    (hτ : 0 ≤ τ) (hi : i ≤ I) (hheight : 0 ≤ height)
    (hsmall : |tMark|+|tLong|+height ≤ U^τ) :
    (1+|tLong|+(|tMark|+|tLong|+height))^degree*
      (1+(2*Real.pi*((U^d)^(τ/(2*dmax)))+(3*i:ℕ)*U^τ))^(2*J+1) ≤
    ((4:ℝ)^degree*(1+2*Real.pi+(3*I:ℕ))^(2*J+1))*
      U^(τ*((degree+2*J+1:ℕ):ℝ)) := by
  have hUp : 0 < U := zero_lt_one.trans hU
  have hpow : 1 ≤ U^τ := Real.one_le_rpow hU.le hτ
  have hsrc : 1+|tLong|+(|tMark|+|tLong|+height) ≤ 4*U^τ := by
    have ht : |tLong| ≤ U^τ := by
      linarith [abs_nonneg tMark]
    linarith
  have hwit := (witness_height_budget hU hd hdmax hτ i).2
  have hi' : (3*i:ℕ) ≤ (3*I:ℕ) := Nat.mul_le_mul_left 3 hi
  have hiR : ((3*i:ℕ):ℝ) ≤ ((3*I:ℕ):ℝ) := by exact_mod_cast hi'
  have hwi : 1+(2*Real.pi*((U^d)^(τ/(2*dmax)))+(3*i:ℕ)*U^τ) ≤
      (1+2*Real.pi+(3*I:ℕ))*U^τ := by
    nlinarith [mul_le_mul_of_nonneg_right hiR (Real.rpow_nonneg hUp.le τ)]
  have hs0 : 0 ≤ 1+|tLong|+(|tMark|+|tLong|+height) := by
    linarith [abs_nonneg tMark,abs_nonneg tLong]
  have hw0 : 0 ≤ 1+(2*Real.pi*((U^d)^(τ/(2*dmax)))+(3*i:ℕ)*U^τ) := by positivity
  have hh := mul_le_mul (pow_le_pow_left₀ hs0 hsrc degree)
    (pow_le_pow_left₀ hw0 hwi (2*J+1)) (pow_nonneg hw0 _) (by positivity : 0 ≤ (4*U^τ)^degree)
  calc
    _ ≤ (4*U^τ)^degree*((1+2*Real.pi+(3*I:ℕ))*U^τ)^(2*J+1) := hh
    _ = ((4:ℝ)^degree*(1+2*Real.pi+(3*I:ℕ))^(2*J+1))*
        U^(τ*((degree+2*J+1:ℕ):ℝ)) := by
      rw [mul_pow,mul_pow,←Real.rpow_mul_natCast hUp.le,←Real.rpow_mul_natCast hUp.le]
      rw [show (4:ℝ)^degree*U^(τ*(degree:ℝ))*
          ((1+2*Real.pi+(3*I:ℕ))^(2*J+1)*U^(τ*((2*J+1:ℕ):ℝ))) =
          ((4:ℝ)^degree*(1+2*Real.pi+(3*I:ℕ))^(2*J+1))*
          (U^(τ*(degree:ℝ))*U^(τ*((2*J+1:ℕ):ℝ))) by ring]
      rw [←Real.rpow_add hUp]
      congr 2
      push_cast
      ring

#print axioms ordinary_height_payment
end
end QRH.Cycle092.StrongPair
