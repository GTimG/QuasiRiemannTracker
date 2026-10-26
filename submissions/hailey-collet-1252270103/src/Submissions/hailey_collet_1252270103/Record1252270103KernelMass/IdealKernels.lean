/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Submissions.hailey_collet_1252270103.Record1252270103TwoIdeal.CoefficientBounds

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103KernelMass
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
open Record1252270103TwoIdeal
abbrev O := OAI.ActualEisensteinCubic.O
abbrev primeSupport := OAI.IdealMobiusDivisorSum.primeSupport

def valuation (I P : Ideal O) : ℕ := factorization I P

def pairSupport (I J : Ideal O) : Finset (Ideal O) := primeSupport I ∪ primeSupport J

def localExponent (I J P : Ideal O) : Exponent := exponent (valuation I P) (valuation J P)

def idealKernel (f : Exponent → ℤ) (I J : Ideal O) : ℤ :=
  if I = 0 ∨ J = 0 then 0 else ∏ P ∈ pairSupport I J, f (localExponent I J P)

def forwardKernel : Ideal O → Ideal O → ℤ := idealKernel (fun n => MvPowerSeries.coeff n forwardSeries)
def inverseKernel : Ideal O → Ideal O → ℤ := idealKernel inverseCoeff

theorem valuation_mul {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0) (P : Ideal O) :
    valuation (I*J) P = valuation I P + valuation J P := by
  simp [valuation,factorization_mul hI hJ]

theorem valuation_eq_zero_of_not_mem {I P : Ideal O} (h : P ∉ primeSupport I) :
    valuation I P = 0 := by
  simpa [valuation,← support_factorization] using (Finsupp.notMem_support_iff.mp h)

theorem ideals_eq_of_valuations {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ P, valuation I P = valuation J P) : I=J := by
  have hf : factorization I = factorization J := Finsupp.ext h
  exact associated_iff_eq.mp (associated_of_factorization_eq I J hI hJ hf)

theorem idealKernel_zero_left (f : Exponent → ℤ) (J : Ideal O) : idealKernel f 0 J = 0 := by simp [idealKernel]
theorem idealKernel_zero_right (f : Exponent → ℤ) (I : Ideal O) : idealKernel f I 0 = 0 := by simp [idealKernel]

theorem idealKernel_one (f : Exponent → ℤ) : idealKernel f 1 1 = 1 := by
  have hs : primeSupport (1 : Ideal O) = ∅ := by
    exact congrArg Multiset.toFinset normalizedFactors_one
  rw [idealKernel,ite_eq_right (by simp),pairSupport,hs,Finset.union_self,Finset.prod_empty]


theorem idealKernel_eq_prod (f : Exponent → ℤ) (hf : f 0 = 1)
    {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) (hS : pairSupport I J ⊆ S) :
    idealKernel f I J = ∏ P ∈ S, f (localExponent I J P) := by
  rw [idealKernel,ite_eq_right (not_or.mpr ⟨hI,hJ⟩)]
  exact Finset.prod_subset hS (by
    intro P hP hn
    have hz : valuation I P=0 ∧ valuation J P=0 := by
      simp only [pairSupport,Finset.mem_union,not_or] at hn
      exact ⟨valuation_eq_zero_of_not_mem hn.1,valuation_eq_zero_of_not_mem hn.2⟩
    simpa [localExponent,exponent,hz.1,hz.2] using hf)

theorem primeSupport_prime {I P : Ideal O} (hP : P ∈ primeSupport I) : Prime P :=
  OAI.IdealMobiusDivisorSum.support_prime hP

theorem ideals_eq_of_valuations_on {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) (hIS : primeSupport I ⊆ S) (hJS : primeSupport J ⊆ S)
    (h : ∀ P ∈ S, valuation I P = valuation J P) : I=J := by
  apply ideals_eq_of_valuations hI hJ
  intro P
  by_cases hp : P ∈ S
  · exact h P hp
  · rw [valuation_eq_zero_of_not_mem (fun hx => hp (hIS hx)),
      valuation_eq_zero_of_not_mem (fun hx => hp (hJS hx))]

theorem ideal_eq_prod_valuation {I : Ideal O} (hI : I ≠ 0) :
    I = ∏ P ∈ primeSupport I, P ^ valuation I P := by
  classical
  rw [← Ideal.prod_normalizedFactors_eq_self hI]
  conv_rhs => rw [Ideal.prod_normalizedFactors_eq_self hI]
  simpa only [valuation,factorization_eq_count,primeSupport,OAI.IdealMobiusDivisorSum.primeSupport] using (Finset.prod_multiset_count (normalizedFactors I))


theorem ideal_eq_prod_valuation_of_support {I : Ideal O} (hI : I ≠ 0)
    (S : Finset (Ideal O)) (hS : primeSupport I ⊆ S) :
    I = ∏ P ∈ S, P ^ valuation I P := by
  rw [ideal_eq_prod_valuation hI]
  conv_rhs => rw [← ideal_eq_prod_valuation hI]
  exact Finset.prod_subset hS (by
    intro P hP hn
    rw [valuation_eq_zero_of_not_mem hn,pow_zero])

theorem norm_eq_prod_valuation {I : Ideal O} (hI : I ≠ 0)
    (S : Finset (Ideal O)) (hS : primeSupport I ⊆ S) :
    Ideal.absNorm I = ∏ P ∈ S, (Ideal.absNorm P) ^ valuation I P := by
  calc
    Ideal.absNorm I = Ideal.absNorm (∏ P ∈ S, P ^ valuation I P) :=
      congrArg Ideal.absNorm (ideal_eq_prod_valuation_of_support hI S hS)
    _ = _ := by simp only [map_prod,map_pow]


def normWeight (σ : ℝ) (I : Ideal O) : ℝ := (Ideal.absNorm I : ℝ)^(-σ)

theorem normWeight_eq_prod {I : Ideal O} (hI : I ≠ 0)
    (S : Finset (Ideal O)) (hS : primeSupport I ⊆ S) (σ : ℝ) :
    normWeight σ I = ∏ P ∈ S, ((Ideal.absNorm P : ℝ)^(-σ))^(valuation I P) := by
  unfold normWeight
  rw [norm_eq_prod_valuation hI S hS,Nat.cast_prod]
  rw [← Real.finsetProd_rpow S (fun P => ((Ideal.absNorm P) ^ valuation I P : ℕ))
    (by intro P hP; positivity)]
  apply Finset.prod_congr rfl
  intro P hP
  rw [Nat.cast_pow,← Real.rpow_natCast_mul (Nat.cast_nonneg _),mul_comm,
    Real.rpow_mul_natCast (Nat.cast_nonneg _)]


end
end QRH.Record1252270103KernelMass
#print axioms QRH.Record1252270103KernelMass.ideals_eq_of_valuations
