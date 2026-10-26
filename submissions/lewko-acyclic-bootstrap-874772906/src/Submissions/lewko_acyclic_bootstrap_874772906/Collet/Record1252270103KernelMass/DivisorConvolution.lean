/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103KernelMass.ValuationEnumeration

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103KernelMass
noncomputable section
open scoped BigOperators
open Record1252270103TwoIdeal
open OAI.IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)

def idealCofactor (I d : Ideal O) : Ideal O := by
  classical
  exact if h : d ∣ I then Classical.choose h else 0

theorem idealCofactor_mul {I d : Ideal O} (hd : d ∣ I) : d * idealCofactor I d = I := by
  simpa only [idealCofactor,dite_eq_left hd] using (Classical.choose_spec hd).symm

theorem idealCofactor_ne_zero {I d : Ideal O} (hI : I ≠ 0) (hd : d ∣ I) : idealCofactor I d ≠ 0 := by
  intro hz
  apply hI
  rw [← idealCofactor_mul hd,hz,mul_zero]

theorem idealCofactor_dvd {I d : Ideal O} (hd : d ∣ I) : idealCofactor I d ∣ I :=
  ⟨d,by rw [mul_comm,idealCofactor_mul hd]⟩

theorem valuation_idealCofactor {I d : Ideal O} (hI : I ≠ 0) (hd : d ∣ I) (P : Ideal O) :
    valuation (idealCofactor I d) P = valuation I P-valuation d P := by
  have heq := congrArg (fun x => valuation x P) (idealCofactor_mul hd)
  rw [valuation_mul (ne_zero_of_dvd_ne_zero hI hd) (idealCofactor_ne_zero hI hd)] at heq
  omega

def cofactorPair (I J : Ideal O) (d : Ideal O × Ideal O) : Ideal O × Ideal O :=
  (idealCofactor I d.1,idealCofactor J d.2)

theorem idealKernel_decodePair (f : Exponent → ℤ) (hf : f 0=1)
    (S : Finset PrimeIdeal) (a : S → ℕ×ℕ) :
    idealKernel f (decodePair S a).1 (decodePair S a).2 =
      ∏ P : S, f (exponent (a P).1 (a P).2) := by
  dsimp only [decodePair]
  rw [idealKernel_eq_prod f hf (decode_ne_zero _ _) (decode_ne_zero _ _)
    (primeValues S) (Finset.union_subset (decode_support _ _) (decode_support _ _))]
  unfold primeValues
  rw [Finset.prod_image (by intro P hP Q hQ h; exact Subtype.val_injective h)]
  rw [Finset.prod_subtype (p := fun P => P ∈ S) S (by simp)]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [localExponent]
  rw [valuation_decode S _ P,valuation_decode S _ P]

theorem cofactorPair_decodePair {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset PrimeIdeal) (hs : pairSupport I J ⊆ primeValues S)
    {a : S → ℕ×ℕ} (ha : a ∈ pairBox S I J) :
    cofactorPair I J (decodePair S a) = decodePair S (fun P =>
      (valuation I P.val.val-(a P).1,valuation J P.val.val-(a P).2)) := by
  have hd := decodePair_mem_divisors hI hJ S ha
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hd
  have hdi := (mem_idealDivisors hI).mp hi
  have hdj := (mem_idealDivisors hJ).mp hj
  dsimp only [decodePair] at hdi hdj
  apply Prod.ext
  · apply ideals_eq_of_valuations_on (idealCofactor_ne_zero hI hdi) (decode_ne_zero _ _)
      (primeValues S)
      (Finset.Subset.trans (primeSupport_subset_of_dvd (idealCofactor_ne_zero hI hdi)
        hI (idealCofactor_dvd hdi)) (Finset.Subset.trans Finset.subset_union_left hs))
      (decode_support _ _)
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    rw [valuation_idealCofactor hI hdi,valuation_decode S _ ⟨Q,hQ⟩,valuation_decode S _ ⟨Q,hQ⟩]
  · apply ideals_eq_of_valuations_on (idealCofactor_ne_zero hJ hdj) (decode_ne_zero _ _)
      (primeValues S)
      (Finset.Subset.trans (primeSupport_subset_of_dvd (idealCofactor_ne_zero hJ hdj)
        hJ (idealCofactor_dvd hdj)) (Finset.Subset.trans Finset.subset_union_right hs))
      (decode_support _ _)
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    rw [valuation_idealCofactor hJ hdj,valuation_decode S _ ⟨Q,hQ⟩,valuation_decode S _ ⟨Q,hQ⟩]

theorem ideal_divisor_convolution_factorization (f g : Exponent → ℤ) (hf : f 0=1) (hg : g 0=1)
    {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset PrimeIdeal) (hs : pairSupport I J ⊆ primeValues S) :
    ∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
      idealKernel f d.1 d.2 * idealKernel g (cofactorPair I J d).1 (cofactorPair I J d).2 =
    ∏ P : S, ∑ ij ∈ Finset.range (valuation I P.val.val+1) ×ˢ Finset.range (valuation J P.val.val+1),
      f (exponent ij.1 ij.2) * g (exponent (valuation I P.val.val-ij.1) (valuation J P.val.val-ij.2)) := by
  rw [← divisor_pair_enumeration hI hJ S hs,
    Finset.sum_image (fun a _ b _ h => decodePair_injective S h)]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [cofactorPair_decodePair hI hJ S hs ha,idealKernel_decodePair f hf,
    idealKernel_decodePair g hg,Finset.prod_mul_distrib]

end
end QRH.Record1252270103KernelMass
#print axioms QRH.Record1252270103KernelMass.ideal_divisor_convolution_factorization
