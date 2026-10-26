/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103KernelMass.DivisorConvolution
import Submissions.hailey_collet_1252270103.Record1252270103TwoIdeal.LocalValuations

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103KernelMass
noncomputable section
open scoped BigOperators
open Record1252270103TwoIdeal UniqueFactorizationMonoid

def squarefreeCoeff (n : Exponent) : ℤ := MvPowerSeries.coeff n squarefreeSeries

def squarefreeIndicator (I : Ideal O) : ℤ := by
  classical
  exact if Squarefree I then 1 else 0

theorem squarefreeCoeff_zero : squarefreeCoeff 0=1 := by
  simpa [squarefreeCoeff,exponent] using squarefree_coefficient_at 0 0

theorem squarefree_mul_iff_valuations {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0) :
    Squarefree (I*J) ↔ ∀ P, valuation I P+valuation J P ≤ 1 := by
  rw [squarefree_iff_nodup_normalizedFactors (mul_ne_zero hI hJ),Multiset.nodup_iff_count_le_one]
  simp only [← factorization_eq_count,← valuation_mul hI hJ]
  rfl

theorem squarefree_mul_iff_on_support {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) (hs : pairSupport I J ⊆ S) :
    Squarefree (I*J) ↔ ∀ P ∈ S, valuation I P+valuation J P ≤ 1 := by
  rw [squarefree_mul_iff_valuations hI hJ]
  constructor
  · exact fun h P _ => h P
  · intro h P
    by_cases hp : P ∈ S
    · exact h P hp
    · have hi : P ∉ primeSupport I := fun hx => hp (hs (Finset.mem_union_left _ hx))
      have hj : P ∉ primeSupport J := fun hx => hp (hs (Finset.mem_union_right _ hx))
      rw [valuation_eq_zero_of_not_mem hi,valuation_eq_zero_of_not_mem hj]
      decide

theorem squarefreeKernel_eq_indicator {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealKernel squarefreeCoeff I J = squarefreeIndicator (I*J) := by
  classical
  rw [idealKernel_eq_prod squarefreeCoeff squarefreeCoeff_zero hI hJ (pairSupport I J) (Finset.Subset.refl _)]
  simp only [squarefreeCoeff,localExponent,squarefree_coefficient_at,Finset.prod_ite_zero,
    Finset.prod_const_one]
  unfold squarefreeIndicator
  rw [squarefree_mul_iff_on_support hI hJ (pairSupport I J) (Finset.Subset.refl _)]
  split_ifs <;> rfl

end
end QRH.Record1252270103KernelMass
#print axioms QRH.Record1252270103KernelMass.squarefreeKernel_eq_indicator
