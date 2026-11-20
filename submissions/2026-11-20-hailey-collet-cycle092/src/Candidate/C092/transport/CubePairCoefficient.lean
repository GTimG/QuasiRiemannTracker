/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.CubePairIdealResidual

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

def finiteGoodIndices (bad : Finset PrimeIdeal) (S : Finset (GoodPrimes bad)) : Finset (GoodIndex bad) :=
  S.powerset.sigma (fun T => (Finset.univ : Finset (T → Fin 7)))

lemma mem_finiteGoodIndices (bad : Finset PrimeIdeal) (S : Finset (GoodPrimes bad)) (k : GoodIndex bad) :
    k ∈ finiteGoodIndices bad S ↔ k.1 ⊆ S := by
  simp only [finiteGoodIndices,Finset.mem_sigma,Finset.mem_powerset,Finset.mem_univ,and_true]

def finiteCorrectedIndices (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (S : Finset (GoodPrimes bad)) : Finset (CorrectedIndex bad allowed) :=
  Finset.univ ×ˢ (Finset.univ ×ˢ finiteGoodIndices bad S)

lemma mem_finiteCorrectedIndices (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (S : Finset (GoodPrimes bad)) (k : CorrectedIndex bad allowed) :
    k ∈ finiteCorrectedIndices bad allowed S ↔ k.2.2.1 ⊆ S := by
  simp only [finiteCorrectedIndices,Finset.mem_product,Finset.mem_univ,mem_finiteGoodIndices,true_and]

def idealResidualCoefficient (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (I J : Ideal O) (k : CorrectedIndex bad allowed) : ℂ :=
  if I ≠ 0 ∧ J ≠ 0 ∧ correctedIdeal₁ bad allowed k ∣ I ∧ correctedIdeal₂ bad allowed k ∣ J then
    idealCoeff χ₁ (idealQuotient I (correctedIdeal₁ bad allowed k))*
      idealCoeff χ₂ (idealQuotient J (correctedIdeal₂ bad allowed k)) else 0

lemma idealResidualCoefficient_zero_outside (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (I J : Ideal O) (k : CorrectedIndex bad allowed)
    (hk : k ∉ finiteCorrectedIndices bad allowed (goodPairSupport bad I J)) :
    idealResidualCoefficient χ₁ χ₂ bad allowed I J k=0 := by
  apply ite_eq_right
  rintro ⟨hI,hJ,hd₁,hd₂⟩
  apply hk
  apply (mem_finiteCorrectedIndices bad allowed _ k).mpr
  exact admissible_good_support bad allowed k I J
    ((correctedIdeal_dvd_iff_admissible bad allowed k I J hI hJ).mp ⟨hd₁,hd₂⟩)

def idealConvolutionCoefficient (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (I J : Ideal O) (k : CorrectedIndex bad allowed) : ℂ :=
  correctedCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed k*
    idealResidualCoefficient χ₁ χ₂ bad allowed I J k

lemma idealConvolutionCoefficient_hasFiniteSupport (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (I J : Ideal O) :
    (idealConvolutionCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed I J).HasFiniteSupport := by
  apply (finiteCorrectedIndices bad allowed (goodPairSupport bad I J)).finite_toSet.subset
  intro k hk
  by_contra hn
  exact hk (by rw [idealConvolutionCoefficient,
    idealResidualCoefficient_zero_outside χ₁ χ₂ bad allowed I J k hn,mul_zero])

lemma tsum_corrected_finite_support (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (S : Finset (GoodPrimes bad))
    (f : CorrectedIndex bad allowed → ℂ)
    (hf : ∀ k,k ∉ finiteCorrectedIndices bad allowed S → f k=0) :
    (∑' k : CorrectedIndex bad allowed,f k)=
      ∑ q : BadIndex bad allowed,∑ j : DeletionIndex bad,
        ∑ T ∈ S.powerset,∑ v : T → Fin 7,f (j,(q,⟨T,v⟩)) := by
  rw [tsum_eq_sum hf]
  unfold finiteCorrectedIndices finiteGoodIndices
  rw [Finset.sum_product]
  simp only [Finset.sum_product,Finset.sum_sigma]
  rw [Finset.sum_comm]

theorem literalCubePairCoefficient_global (χ₁ χ₂ ψ₁ ψ₂ : Character)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hχ₁ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₁ P.val=idealCoeff ψ₁ P.val)
    (hχ₂ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₂ P.val=idealCoeff ψ₂ P.val)
    (hbad : ∀ P ∈ bad, ∀ q ∈ allowed P,
      (idealCoeff χ₁ P.val)^q.1*(idealCoeff χ₂ P.val)^q.2=
        (idealCoeff ψ₁ P.val)^q.1*(idealCoeff ψ₂ P.val)^q.2)
    (I J : Ideal O) :
    literalCubePairCoefficient χ₁ χ₂ bad allowed I J=
      ∑' k : CorrectedIndex bad allowed,idealConvolutionCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed I J k := by
  by_cases hI : I=0
  · subst I
    simp only [literalCubePairCoefficient,map_zero,zero_mul,ite_self,
      idealConvolutionCoefficient,idealResidualCoefficient,ne_eq,eq_self,not_true_eq_false,false_and,ite_false,mul_zero,tsum_zero]
  · by_cases hJ : J=0
    · subst J
      simp only [literalCubePairCoefficient,map_zero,mul_zero,ite_self,
        idealConvolutionCoefficient,idealResidualCoefficient,ne_eq,eq_self,not_true_eq_false,false_and,and_false,ite_false,tsum_zero]
    · rw [literalCubePairCoefficient_expansion χ₁ χ₂ ψ₁ ψ₂ bad allowed hχ₁ hχ₂ hbad I J hI hJ]
      rw [tsum_corrected_finite_support bad allowed (goodPairSupport bad I J) _
        (fun k hk => by rw [idealConvolutionCoefficient,
          idealResidualCoefficient_zero_outside χ₁ χ₂ bad allowed I J k hk,mul_zero])]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro T hT
      apply Finset.sum_congr rfl
      intro v _
      rw [correctedResidualKernel_eq_quotient χ₁ χ₂ bad allowed (j,(q,⟨T,v⟩)) I J hI hJ
        (Finset.mem_powerset.mp hT)]
      simp only [idealConvolutionCoefficient,idealResidualCoefficient,ne_eq,hI,hJ,not_false_eq_true,true_and]

#print axioms literalCubePairCoefficient_global
#print axioms tsum_corrected_finite_support
end
end QRH.Cycle092.SignedCenter
