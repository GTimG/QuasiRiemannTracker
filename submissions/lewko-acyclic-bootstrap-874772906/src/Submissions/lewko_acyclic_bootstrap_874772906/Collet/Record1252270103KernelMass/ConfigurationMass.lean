/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103KernelMass.FiniteEulerBound
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103KernelMass.IdealKernels

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103KernelMass
noncomputable section
open scoped BigOperators
open Record1252270103TwoIdeal

def localMassTerm (f : Exponent → ℤ) (σ : ℝ) (P : PrimeIdeal) (ij : ℕ×ℕ) : ℝ :=
  |(f (exponent ij.1 ij.2) : ℝ)| * ((Ideal.absNorm P.val : ℝ)^(-σ))^(ij.1+ij.2)

theorem localMassTerm_nonneg (f : Exponent → ℤ) (σ : ℝ) (P : PrimeIdeal) (ij : ℕ×ℕ) :
    0 ≤ localMassTerm f σ P ij := mul_nonneg (abs_nonneg _) (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _)

theorem finite_configuration_mass (f : Exponent → ℤ) (σ C : ℝ)
    (hσ : 1/2 < σ) (hC : 0 ≤ C) (S : Finset PrimeIdeal)
    (t : S → Finset (ℕ×ℕ))
    (hlocal : ∀ P : S, ∑ ij ∈ t P, localMassTerm f σ P.val ij ≤ 1+C*primeWeight σ P.val) :
    ∑ a ∈ Fintype.piFinset t, ∏ P : S, localMassTerm f σ P.val (a P) ≤ eulerBound C σ := by
  classical
  rw [← Finset.prod_univ_sum]
  calc
    ∏ P : S, ∑ ij ∈ t P, localMassTerm f σ P.val ij ≤
        ∏ P : S, (1+C*primeWeight σ P.val) := by
      apply Finset.prod_le_prod₀
      · intro P hP
        exact Finset.sum_nonneg (fun ij _ => localMassTerm_nonneg f σ P.val ij)
      · intro P hP
        exact hlocal P
    _ = ∏ P ∈ S, (1+C*primeWeight σ P) := by exact (Finset.prod_subtype (p := fun P => P ∈ S) S (by simp) (fun P => (1+C*primeWeight σ P))).symm
    _ ≤ eulerBound C σ := finite_euler_bound C σ hC hσ S

end
end QRH.Record1252270103KernelMass
#print axioms QRH.Record1252270103KernelMass.finite_configuration_mass
