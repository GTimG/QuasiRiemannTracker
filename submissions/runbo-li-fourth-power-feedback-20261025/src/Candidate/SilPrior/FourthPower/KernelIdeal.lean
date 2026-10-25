/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Exact fifth-free ideal-divisor restoration. The generic divisor enumeration is
imported unchanged from PR69. The short global-assembly pattern follows its
GlobalIdentities module, with our fifth-free series and a literal PowerFree predicate.
-/
import Candidate.SilPrior.FourthPower.KernelFormal
import Candidate.SilPrior.FourthPower.SexticSieve
import Submissions.hailey_collet_1252270103.Record1252270103KernelMass.DivisorConvolution

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.KernelIdeal
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open OAI.IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open KernelFormal
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

def forwardIdeal (I J : Id) : ℤ := idealKernel kernelCoeff I J
def inverseIdeal (I J : Id) : ℤ := idealKernel reciprocalCoeff I J
def restrictedIdeal (I : Id) : ℤ := if SexticSieve.PowerFree 5 I then 1 else 0

theorem powerFree_iff_valuations {I : Id} (hI : I ≠ 0) :
    SexticSieve.PowerFree 5 I ↔ ∀ P, valuation I P < 5 := by
  constructor
  · intro h P
    by_contra hlt
    have hval : 5 ≤ valuation I P := by omega
    have hmem : P ∈ primeSupport I := by
      by_contra hm
      rw [valuation_eq_zero_of_not_mem hm] at hval
      omega
    have hp := primeSupport_prime hmem
    apply h P hp
    apply (dvd_iff_valuation_le (pow_ne_zero 5 hp.ne_zero) hI).mpr
    intro Q
    rw [valuation_pow,valuation_prime (⟨P,hp⟩ : PrimeIdeal)]
    split_ifs with hq
    · subst Q
      simpa using hval
    · simp
  · intro h P hp hd
    have he := (dvd_iff_valuation_le (pow_ne_zero 5 hp.ne_zero) hI).mp hd P
    rw [valuation_pow,valuation_prime (⟨P,hp⟩ : PrimeIdeal)] at he
    simp only [ite_true,mul_one] at he
    exact (not_le_of_gt (h P)) he

theorem powerFree_mul_iff_on_support {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset Id) (hs : pairSupport I J ⊆ S) :
    SexticSieve.PowerFree 5 (I*J) ↔ ∀ P ∈ S, valuation I P+valuation J P < 5 := by
  rw [powerFree_iff_valuations (mul_ne_zero hI hJ)]
  simp_rw [valuation_mul hI hJ]
  constructor
  · exact fun h P _ => h P
  · intro h P
    by_cases hp : P ∈ S
    · exact h P hp
    · have hi : P ∉ primeSupport I := fun hx => hp (hs (Finset.mem_union_left _ hx))
      have hj : P ∉ primeSupport J := fun hx => hp (hs (Finset.mem_union_right _ hx))
      rw [valuation_eq_zero_of_not_mem hi,valuation_eq_zero_of_not_mem hj]
      decide

theorem restricted_kernel_eq_indicator {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealKernel restrictedCoeff I J = restrictedIdeal (I*J) := by
  rw [idealKernel_eq_prod restrictedCoeff restrictedCoeff_zero hI hJ
    (pairSupport I J) (Finset.Subset.refl _)]
  simp only [restrictedCoeff,localExponent,exponent,Finsupp.coe_add,Pi.add_apply,
    Finsupp.single_eq_same,Finsupp.single_eq_of_ne (by decide : (0:Fin 2)≠1),
    Finsupp.single_eq_of_ne (by decide : (1:Fin 2)≠0),add_zero,zero_add,
    Finset.prod_ite_zero,Finset.prod_const_one]
  unfold restrictedIdeal
  rw [powerFree_mul_iff_on_support hI hJ (pairSupport I J) (Finset.Subset.refl _)]
  split_ifs <;> rfl

theorem kernel_eq_prime_prod (f : Exponent → ℤ) (hf : f 0=1)
    {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset PrimeIdeal) (hs : pairSupport I J ⊆ primeValues S) :
    idealKernel f I J = ∏ P : S, f (localExponent I J P.val.val) := by
  rw [idealKernel_eq_prod f hf hI hJ (primeValues S) hs]
  unfold primeValues
  rw [Finset.prod_image (by intro P hP Q hQ h; exact Subtype.val_injective h)]
  exact Finset.prod_subtype (p := fun P => P ∈ S) S (by simp) _

theorem pair_support (I J : Id) : pairSupport I J ⊆ primeValues (primeClosure {(I,J)}) := by
  rw [primeValues_primeClosure]
  intro P hP
  exact Finset.mem_biUnion.mpr ⟨(I,J),Finset.mem_singleton_self _,hP⟩

theorem const_kernel_one {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealKernel (fun _ => 1) I J = 1 := by
  simp only [idealKernel,ite_eq_right (not_or.mpr ⟨hI,hJ⟩),Finset.prod_const_one]

theorem forward_global_identity {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0) :
    restrictedIdeal (I*J) = ∑ d ∈ idealDivisors I ×ˢ idealDivisors J, forwardIdeal d.1 d.2 := by
  let S := primeClosure {(I,J)}
  have hs := pair_support I J
  have h := ideal_divisor_convolution_factorization kernelCoeff (fun _ => 1)
    kernelCoeff_zero rfl hI hJ S hs
  have heq : (∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
      idealKernel kernelCoeff d.1 d.2 *
        idealKernel (fun _ => 1) (cofactorPair I J d).1 (cofactorPair I J d).2) =
      ∑ d ∈ idealDivisors I ×ˢ idealDivisors J, forwardIdeal d.1 d.2 := by
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hd
    dsimp only [cofactorPair]
    rw [const_kernel_one (idealCofactor_ne_zero hI ((mem_idealDivisors hI).mp hi))
      (idealCofactor_ne_zero hJ ((mem_idealDivisors hJ).mp hj)),mul_one]
    rfl
  rw [heq] at h
  rw [← restricted_kernel_eq_indicator hI hJ,
    kernel_eq_prime_prod restrictedCoeff restrictedCoeff_zero hI hJ S hs,h]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [mul_one,Finset.sum_product]
  rw [KernelFormal.forward_rectangular_convolution]
  simp [restrictedCoeff,localExponent,exponent]

theorem inverse_global_identity {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0) :
    (1 : ℤ) = ∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
      inverseIdeal d.1 d.2*restrictedIdeal ((idealCofactor I d.1)*(idealCofactor J d.2)) := by
  let S := primeClosure {(I,J)}
  have hs := pair_support I J
  have h := ideal_divisor_convolution_factorization reciprocalCoeff restrictedCoeff
    reciprocalCoeff_zero restrictedCoeff_zero hI hJ S hs
  have heq : (∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
      idealKernel reciprocalCoeff d.1 d.2 *
        idealKernel restrictedCoeff (cofactorPair I J d).1 (cofactorPair I J d).2) =
      ∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
        inverseIdeal d.1 d.2*restrictedIdeal ((idealCofactor I d.1)*(idealCofactor J d.2)) := by
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hd
    dsimp only [cofactorPair]
    rw [restricted_kernel_eq_indicator
      (idealCofactor_ne_zero hI ((mem_idealDivisors hI).mp hi))
      (idealCofactor_ne_zero hJ ((mem_idealDivisors hJ).mp hj))]
    rfl
  rw [heq] at h
  rw [h]
  symm
  apply Finset.prod_eq_one
  intro P hP
  simp only [Finset.sum_product,restrictedCoeff,exponent,Finsupp.coe_add,Pi.add_apply,
    Finsupp.single_eq_same,Finsupp.single_eq_of_ne (by decide : (0:Fin 2)≠1),
    Finsupp.single_eq_of_ne (by decide : (1:Fin 2)≠0),add_zero,zero_add]
  exact KernelFormal.inverse_rectangular_convolution _ _

end
end Candidate.SilPrior.FourthPower.KernelIdeal
