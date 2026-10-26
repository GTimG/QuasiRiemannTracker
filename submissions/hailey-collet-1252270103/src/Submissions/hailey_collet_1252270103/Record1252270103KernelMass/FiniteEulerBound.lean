/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.MobiusEulerCorrection

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103KernelMass
noncomputable section
open scoped BigOperators
abbrev PrimeIdeal := OAI.SmoothMobiusCorrection.PrimeIdeal

def primeWeight (σ : ℝ) (P : PrimeIdeal) : ℝ := (Ideal.absNorm P.val : ℝ)^(-2*σ)
def eulerBound (C σ : ℝ) : ℝ := Real.exp (C * ∑' P : PrimeIdeal, primeWeight σ P)

theorem primeWeight_nonneg (σ : ℝ) (P : PrimeIdeal) : 0 ≤ primeWeight σ P :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem primeWeight_summable (σ : ℝ) (hσ : 1/2 < σ) : Summable (primeWeight σ) := by
  have h := OAI.SmoothMobiusCorrection.prime_norm_series_summable (2*σ-1) (by linarith)
  convert h using 1
  ext P
  unfold primeWeight
  congr 1; ring

theorem eulerBound_pos (C σ : ℝ) : 0 < eulerBound C σ := Real.exp_pos _

theorem finite_euler_bound (C σ : ℝ) (hC : 0 ≤ C) (hσ : 1/2 < σ)
    (S : Finset PrimeIdeal) :
    ∏ P ∈ S, (1+C*primeWeight σ P) ≤ eulerBound C σ := by
  have hsum : ∑ P ∈ S, primeWeight σ P ≤ ∑' P : PrimeIdeal, primeWeight σ P :=
    (primeWeight_summable σ hσ).sum_le_tsum S (fun P _ => primeWeight_nonneg σ P)
  calc
    ∏ P ∈ S, (1+C*primeWeight σ P) ≤ ∏ P ∈ S, Real.exp (C*primeWeight σ P) := by
      apply Finset.prod_le_prod₀
      · intro P hP
        exact add_nonneg (by norm_num) (mul_nonneg hC (primeWeight_nonneg σ P))
      · intro P hP
        simpa [add_comm] using Real.add_one_le_exp (C*primeWeight σ P)
    _ = Real.exp (C * ∑ P ∈ S, primeWeight σ P) := by
      rw [Finset.mul_sum,Real.exp_sum]
    _ ≤ eulerBound C σ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum hC)

end
end QRH.Record1252270103KernelMass
#print axioms QRH.Record1252270103KernelMass.finite_euler_bound
