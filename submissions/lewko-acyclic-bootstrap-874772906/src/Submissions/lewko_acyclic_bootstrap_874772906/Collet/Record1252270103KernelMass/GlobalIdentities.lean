/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103KernelMass.SquarefreeKernel
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103TwoIdeal.RectangularConvolution

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103KernelMass
noncomputable section
open scoped BigOperators
open Record1252270103TwoIdeal
open OAI.IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)

theorem idealKernel_eq_prime_prod (f : Exponent → ℤ) (hf : f 0=1)
    {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset PrimeIdeal) (hs : pairSupport I J ⊆ primeValues S) :
    idealKernel f I J = ∏ P : S, f (localExponent I J P.val.val) := by
  rw [idealKernel_eq_prod f hf hI hJ (primeValues S) hs]
  unfold primeValues
  rw [Finset.prod_image (by intro P hP Q hQ h; exact Subtype.val_injective h)]
  exact Finset.prod_subtype (p := fun P => P ∈ S) S (by simp) _

theorem single_pair_support (I J : Ideal O) :
    pairSupport I J ⊆ primeValues (primeClosure {(I,J)}) := by
  rw [primeValues_primeClosure]
  intro P hP
  exact Finset.mem_biUnion.mpr ⟨(I,J),Finset.mem_singleton_self _,hP⟩

theorem idealKernel_const_one {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealKernel (fun _ => 1) I J=1 := by
  simp only [idealKernel,ite_eq_right (not_or.mpr ⟨hI,hJ⟩),Finset.prod_const_one]

theorem forward_global_divisor_identity {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0) :
    squarefreeIndicator (I*J) = ∑ d ∈ idealDivisors I ×ˢ idealDivisors J, forwardKernel d.1 d.2 := by
  classical
  let S := primeClosure {(I,J)}
  have hs := single_pair_support I J
  have h := ideal_divisor_convolution_factorization forwardCoeff (fun _ => 1)
    (by simpa [exponent] using forward_coefficient_at 0 0) rfl hI hJ S hs
  have heq : (∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
      idealKernel forwardCoeff d.1 d.2 *
        idealKernel (fun _ => 1) (cofactorPair I J d).1 (cofactorPair I J d).2) =
      ∑ d ∈ idealDivisors I ×ˢ idealDivisors J, forwardKernel d.1 d.2 := by
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hd
    dsimp only [cofactorPair]
    rw [idealKernel_const_one (idealCofactor_ne_zero hI ((mem_idealDivisors hI).mp hi))
      (idealCofactor_ne_zero hJ ((mem_idealDivisors hJ).mp hj)),mul_one]
    rfl
  rw [heq] at h
  rw [← squarefreeKernel_eq_indicator hI hJ,idealKernel_eq_prime_prod squarefreeCoeff squarefreeCoeff_zero hI hJ S hs]
  rw [h]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [mul_one,Finset.sum_product]
  rw [forward_rectangular_convolution,squarefreeCoeff,localExponent,squarefree_coefficient_at]

theorem inverse_global_divisor_identity {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0) :
    (1 : ℤ) = ∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
      inverseKernel d.1 d.2 * squarefreeIndicator ((idealCofactor I d.1)*(idealCofactor J d.2)) := by
  classical
  let S := primeClosure {(I,J)}
  have hs := single_pair_support I J
  have h := ideal_divisor_convolution_factorization inverseCoeff squarefreeCoeff
    inverseCoeff_zero squarefreeCoeff_zero hI hJ S hs
  have heq : (∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
      idealKernel inverseCoeff d.1 d.2 *
        idealKernel squarefreeCoeff (cofactorPair I J d).1 (cofactorPair I J d).2) =
      ∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
        inverseKernel d.1 d.2 * squarefreeIndicator ((idealCofactor I d.1)*(idealCofactor J d.2)) := by
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hd
    dsimp only [cofactorPair]
    rw [squarefreeKernel_eq_indicator
      (idealCofactor_ne_zero hI ((mem_idealDivisors hI).mp hi))
      (idealCofactor_ne_zero hJ ((mem_idealDivisors hJ).mp hj))]
    rfl
  rw [heq] at h
  rw [h]
  symm
  apply Finset.prod_eq_one
  intro P hP
  simp only [Finset.sum_product,squarefreeCoeff,squarefree_coefficient_at]
  exact inverse_rectangular_convolution _ _

end
end QRH.Record1252270103KernelMass
#print axioms QRH.Record1252270103KernelMass.forward_global_divisor_identity
#print axioms QRH.Record1252270103KernelMass.inverse_global_divisor_identity
