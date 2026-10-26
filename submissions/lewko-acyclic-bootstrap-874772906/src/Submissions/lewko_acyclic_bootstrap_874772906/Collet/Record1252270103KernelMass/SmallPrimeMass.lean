/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103KernelMass.SmallPrimeSplit

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103KernelMass
noncomputable section
open scoped BigOperators
open Record1252270103TwoIdeal

def ordinaryPrimeMassBound (S : Finset PrimeIdeal) : ℝ :=
  ∏ P : S, ((1-(Ideal.absNorm P.val.val : ℝ)^(-(1/2:ℝ)))⁻¹)^2

theorem prime_half_weight_lt_one (P : PrimeIdeal) :
    (Ideal.absNorm P.val : ℝ)^(-(1/2:ℝ)) < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · have h := OAI.SmoothMobiusCorrection.prime_norm_two_le P
    have hh : (2:ℝ) ≤ Ideal.absNorm P.val := by exact_mod_cast h
    linarith
  · norm_num

theorem ordinaryPrimeMassBound_pos (S : Finset PrimeIdeal) : 0 < ordinaryPrimeMassBound S := by
  apply Finset.prod_pos
  intro P hP
  exact pow_pos (inv_pos.mpr (sub_pos.mpr (prime_half_weight_lt_one P.val))) 2

theorem ordinary_supported_finite_mass (S : Finset PrimeIdeal)
    (D : Finset (Ideal O × Ideal O))
    (hnz : ∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hs : ∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) :
    ∑ d ∈ D, normWeight (1/2) d.1 * normWeight (1/2) d.2 ≤ ordinaryPrimeMassBound S := by
  classical
  have heq : (∑ d ∈ D, idealPairWeight (fun _ => 1) (1/2) d) =
      ∑ d ∈ D, normWeight (1/2) d.1 * normWeight (1/2) d.2 := by
    apply Finset.sum_congr rfl
    intro d hd
    simp only [idealPairWeight,idealKernel_const_one (hnz d hd).1 (hnz d hd).2,
      Int.cast_one,abs_one,one_mul]
  rw [← heq]
  calc
    _ ≤ ∏ P : S, ∑ ij ∈ D.image (fun d => encodePair S d P), localMassTerm (fun _ => 1) (1/2) P.val ij :=
      finite_ideal_mass_product _ rfl _ D S hnz hs
    _ ≤ ordinaryPrimeMassBound S := by
      apply Finset.prod_le_prod₀
      · intro P hP
        exact Finset.sum_nonneg (fun ij _ => localMassTerm_nonneg _ _ _ _)
      · intro P hP
        have hz0 := Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm P.val.val)) (-(1/2:ℝ))
        have hz1 := prime_half_weight_lt_one P.val
        have hg := geometric_pair_sum hz0 hz1
        have h := hg.1.sum_le_tsum (D.image (fun d => encodePair S d P))
          (fun ij _ => pow_nonneg hz0 (ij.1+ij.2))
        rw [hg.2] at h
        simpa only [localMassTerm,Int.cast_one,abs_one,one_mul] using h

end
end QRH.Record1252270103KernelMass
#print axioms QRH.Record1252270103KernelMass.ordinary_supported_finite_mass
