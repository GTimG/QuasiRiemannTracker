/- Copyright (c) 2026 Sil. Apache-2.0.
Primitive Fourier analysis for the actual sextic row of a sixth-power-free
ideal, using the baseline CRT and Poisson theorems. Multiplicities 1,...,5
are retained; the Fourier modulus is the product of distinct prime factors.
The short identification of this product with the radical follows baseline
CenteredMomentAllocatedNaturalSource.primeSupport_product_radical. -/
import Candidate.SilPrior.FourthPower.SixthDecomposition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.GaussSum.ReflectionPool
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Primitive

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.SievePrimitive
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve UniqueFactorizationMonoid
open CenteredMomentPrimitive SexticSieve
open CenteredMomentFourier
open ConcretePrimeRowBridge EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def exponent (I : Id) (P : PrimeIndex I) : ℕ := (normalizedFactors I).count P.val

theorem exponent_pos (I : Id) (P : PrimeIndex I) : 0 < exponent I P :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property)

theorem exponent_lt (I : Id) (hI : Supported I) (hf : PowerFree 6 I)
    (P : PrimeIndex I) : exponent I P < 6 := by
  by_contra! hn
  apply hf P.val (prime_of_normalized_factor _ (Multiset.mem_toFinset.mp P.property))
  apply (pow_dvd_pow P.val hn).trans
  dsimp [exponent]
  rw [Multiset.pow_count]
  exact (Multiset.prod_dvd_prod_of_le (Multiset.filter_le _ _)).trans
    (dvd_of_eq (Ideal.prod_normalizedFactors_eq_self hI.1))

theorem good (I : Id) (hI : Supported I) (P : PrimeIndex I) : goodLambda ∉ P.val :=
  (supported_factors_good I hI _ (Multiset.mem_toFinset.mp P.property)).2.1

theorem odd_residue (I : Id) (hI : Supported I) (P : PrimeIndex I) :
    ringChar (O ⧸ P.val) ≠ 2 :=
  (supported_factors_good I hI _ (Multiset.mem_toFinset.mp P.property)).2.2

def modulus (I : Id) : O := finitePrimeModulus (fun P : PrimeIndex I => P.val)

theorem modulus_ne_zero (I : Id) : modulus I ≠ 0 := finitePrimeModulus_ne_zero _

theorem span_modulus (I : Id) (hI : I ≠ 0) : Ideal.span {modulus I} = I.radical := by
  rw [modulus, span_finitePrimeModulus]
  rw [Finset.prod_coe_sort (s := primeSupport I) (f := fun P => P)]
  ext x
  change x ∈ (∏ P ∈ primeSupport I, P) ↔ ∃ n : ℕ, x^n ∈ I
  simp_rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le, ← Ideal.span_singleton_pow]
  exact (UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd hI).symm

theorem finite_row (I : Id) (hI : Supported I) (hf : PowerFree 6 I) (z : O) :
    finiteSexticRow (fun P : PrimeIndex I => P.val) (good I hI) (exponent I) z =
      idealRowHom z I := by
  rw [idealRowHom_eq_prime_count_product I hI]
  unfold finiteSexticRow
  apply Finset.prod_congr rfl
  intro P _
  have he : (normalizedFactors I).count P.val % 6 = (normalizedFactors I).count P.val :=
    Nat.mod_eq_of_lt (exponent_lt I hI hf P)
  rw [he]
  rfl

def character (I : Id) (hI : Supported I) : MulChar (O ⧸ Ideal.span {modulus I}) ℂ :=
  primitiveCharacter (fun P : PrimeIndex I => P.val) (primeIndex_pairwise_coprime I)
    (good I hI) (exponent I)

theorem character_mk (I : Id) (hI : Supported I) (hf : PowerFree 6 I) (z : O) :
    character I hI (Ideal.Quotient.mk _ z) = idealRowHom z I := by
  exact (primitiveCharacter_mk _ (primeIndex_pairwise_coprime I) (good I hI) (exponent I) z).trans
    (finite_row I hI hf z)

def phase (I : Id) (hI : Supported I) : ℂ :=
  canonicalNormalizedGauss (fun P : PrimeIndex I => P.val)
    (primeIndex_pairwise_coprime I) (good I hI) (exponent I)

theorem phase_norm (I : Id) (hI : Supported I) (hf : PowerFree 6 I) : ‖phase I hI‖ = 1 :=
  norm_canonicalNormalizedGauss _ (primeIndex_pairwise_coprime I) (good I hI)
    (odd_residue I hI) (exponent I) (fun P => (exponent_pos I P).ne') (exponent_lt I hI hf)

theorem gauss_transform (I : Id) (hI : Supported I) (hf : PowerFree 6 I) (k : O) :
    normalizedResidueGauss (modulus I) (modulus_ne_zero I)
      (character I hI) (Ideal.Quotient.mk _ k) = star (idealRowHom k I) * phase I hI := by
  have he : residueGauss (modulus I) (modulus_ne_zero I)
      (character I hI) (Ideal.Quotient.mk _ k) =
      star (idealRowHom k I) * canonicalGaussSum (fun P : PrimeIndex I => P.val)
        (primeIndex_pairwise_coprime I) (good I hI) (exponent I) := by
    have h := primitive_gauss_transform _ (primeIndex_pairwise_coprime I) (good I hI)
      (odd_residue I hI) (exponent I) (fun P => (exponent_pos I P).ne') (exponent_lt I hI hf) k
    rw [finite_row I hI hf] at h
    exact h
  rw [normalizedResidueGauss, he, sqrt_absNorm]
  dsimp [phase, canonicalNormalizedGauss, modulus]
  ring

theorem radial_poisson (I : Id) (hI : Supported I) (hf : PowerFree 6 I)
    (W : 𝓢(ℝ, ℂ)) (A : ℝ) (hA : 0 < A) :
    (∑' z : O, idealRowHom z I * W (‖eisEmbedding z‖^2 / A)) =
      ((A : ℂ) * phase I hI / (‖eisEmbedding (modulus I)‖ : ℂ)) *
        ∑' k : O, star (idealRowHom k I) *
          paperRadialFourier W (A * ‖eisEmbedding k‖^2 / ‖eisEmbedding (modulus I)‖^2) := by
  have h := canonical_radial_poisson_normalized _ (primeIndex_pairwise_coprime I) (good I hI)
    (odd_residue I hI) (exponent I) (fun P => (exponent_pos I P).ne') (exponent_lt I hI hf) W A hA
  simp_rw [finite_row I hI hf] at h
  exact h

end
end Candidate.SilPrior.FourthPower.SievePrimitive
