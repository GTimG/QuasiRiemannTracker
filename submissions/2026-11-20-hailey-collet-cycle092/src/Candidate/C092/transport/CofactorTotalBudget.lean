/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Charge all ordinary divisors and deleted prime terms against one prescribed loss. -/
import Candidate.C092.transport.CofactorLift
import Candidate.C092.transport.CofactorPrimeUniform
namespace QRH.Cycle092.CofactorOrdinary
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeInverseAmplification IdealMobiusDivisorSum

theorem total_budget (n : ℕ) (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ J : ℝ, 1 ≤ J → ∃ C : ℝ, 0 < C ∧
    ∀ U : ℝ, 1 ≤ U → ∀ root : NonzeroIdeal, (root.val.absNorm:ℝ) ≤ U^L →
      ((idealDivisors root.val).card:ℝ)^4 *
        ((2*(J*U^δ)^2)^n * (2:ℝ)^n) ≤ C*U^ε := by
  let δ : ℝ := (ε/4)/((n:ℝ)+1)
  have hd : 0 < δ := div_pos (by positivity) (by positivity)
  have heq : δ*((n:ℝ)+1) = ε/4 := div_mul_cancel₀ _ (by positivity)
  obtain ⟨D,hD,hdiv⟩ := pair_divisor_budget (ε/2) L (by positivity) hL
  refine ⟨δ,hd,?_⟩; intro J hJ
  let A := (2*J^2)^n * (2:ℝ)^n
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨D*A,mul_pos hD hA,?_⟩; intro U hU root hroot
  have h0 := zero_lt_one.trans_le hU
  have hr : ((U^δ)^2)^n = U^(δ*2*(n:ℝ)) := by
    rw [←Real.rpow_natCast (U^δ) 2,←Real.rpow_mul h0.le,←Real.rpow_natCast,←Real.rpow_mul h0.le]
    norm_num
  have hpow : (2*(J*U^δ)^2)^n * (2:ℝ)^n = A*U^(δ*2*(n:ℝ)) := by
    rw [mul_pow J,←mul_assoc,mul_pow,hr]; dsimp [A]; ring
  rw [hpow]
  calc
    _ ≤ (D * U^(ε/2))*(A*U^(δ*2*(n:ℝ))) :=
       mul_le_mul_of_nonneg_right (hdiv _ hU _ hroot) (by positivity)
    _ = (D*A)*U^(ε/2+δ*2*(n:ℝ)) := by rw [Real.rpow_add h0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU (by nlinarith only [hd,heq])) (mul_pos hD hA).le

#print axioms total_budget
end
end QRH.Cycle092.CofactorOrdinary
