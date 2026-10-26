/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103KernelMass.GlobalIdentities

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103KernelMass
noncomputable section
open scoped BigOperators

/-- All prime ideals omitted by the large-prime kernel mass estimates. -/
def smallPrimes : Finset PrimeIdeal := by
  classical
  have hf : Set.Finite {P : PrimeIdeal | Ideal.absNorm P.val ≤ 15} :=
    (Ideal.finite_setOfPred_absNorm_le (S := O) 15).preimage
    (f := fun P : PrimeIdeal => P.val)
    (Set.injOn_of_injective Subtype.val_injective)
  exact hf.toFinset

theorem mem_smallPrimes (P : PrimeIdeal) : P ∈ smallPrimes ↔ Ideal.absNorm P.val < 16 := by
  simp only [smallPrimes,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]
  omega

def smallFactor (S : Finset PrimeIdeal) (I : Ideal O) : Ideal O :=
  decode S (fun P => valuation I P.val.val)

def residualFactor (S : Finset PrimeIdeal) (I : Ideal O) : Ideal O :=
  idealCofactor I (smallFactor S I)

theorem smallFactor_dvd (S : Finset PrimeIdeal) {I : Ideal O} (hI : I ≠ 0) : smallFactor S I ∣ I := by
  apply (dvd_iff_valuation_le (decode_ne_zero _ _) hI).mpr
  intro P
  by_cases hp : P ∈ primeValues S
  · obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hp
    exact le_of_eq (valuation_decode S _ ⟨Q,hQ⟩)
  · rw [valuation_decode_outside S _ P hp]
    exact Nat.zero_le _

theorem split_identity (S : Finset PrimeIdeal) {I : Ideal O} (hI : I ≠ 0) :
    smallFactor S I * residualFactor S I = I := idealCofactor_mul (smallFactor_dvd S hI)

theorem residualFactor_ne_zero (S : Finset PrimeIdeal) {I : Ideal O} (hI : I ≠ 0) :
    residualFactor S I ≠ 0 := idealCofactor_ne_zero hI (smallFactor_dvd S hI)

theorem residual_valuation_zero (S : Finset PrimeIdeal) {I : Ideal O} (hI : I ≠ 0) (P : S) :
    valuation (residualFactor S I) P.val.val=0 := by
  rw [residualFactor,valuation_idealCofactor hI (smallFactor_dvd S hI)]
  rw [smallFactor,valuation_decode]
  exact Nat.sub_self _

theorem residual_good {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0) :
    GoodPair (residualFactor smallPrimes I,residualFactor smallPrimes J) := by
  refine ⟨residualFactor_ne_zero _ hI,residualFactor_ne_zero _ hJ,?_⟩
  intro P hP
  by_contra hn
  have hp : Prime P := by
    rcases Finset.mem_union.mp hP with hi|hj
    · exact primeSupport_prime hi
    · exact primeSupport_prime hj
  have hm : (⟨P,hp⟩ : PrimeIdeal) ∈ smallPrimes := (mem_smallPrimes _).mpr (show Ideal.absNorm P < 16 from Nat.lt_of_not_ge hn)
  have hzi := residual_valuation_zero smallPrimes hI ⟨⟨P,hp⟩,hm⟩
  have hzj := residual_valuation_zero smallPrimes hJ ⟨⟨P,hp⟩,hm⟩
  rcases Finset.mem_union.mp hP with hi|hj
  · have hx : P ∈ (factorization (residualFactor smallPrimes I)).support := by
      simpa only [support_factorization,primeSupport,OAI.IdealMobiusDivisorSum.primeSupport] using hi
    exact (Finsupp.mem_support_iff.mp hx) hzi
  · have hx : P ∈ (factorization (residualFactor smallPrimes J)).support := by
      simpa only [support_factorization,primeSupport,OAI.IdealMobiusDivisorSum.primeSupport] using hj
    exact (Finsupp.mem_support_iff.mp hx) hzj

theorem smallFactor_support (S : Finset PrimeIdeal) (I : Ideal O) :
    primeSupport (smallFactor S I) ⊆ primeValues S := decode_support S _

theorem split_norm (S : Finset PrimeIdeal) {I : Ideal O} (hI : I ≠ 0) :
    Ideal.absNorm (smallFactor S I)*Ideal.absNorm (residualFactor S I)=Ideal.absNorm I := by
  rw [← map_mul,split_identity S hI]

end
end QRH.Record1252270103KernelMass
#print axioms QRH.Record1252270103KernelMass.residual_good
