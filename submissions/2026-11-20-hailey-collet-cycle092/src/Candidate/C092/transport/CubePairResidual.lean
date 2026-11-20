/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.CubePairExpansion

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily

/-- Ordinary geometric-series coefficients after extracting a fixed numerator
monomial. The guard is essential when a character value is zero. -/
def ordinaryResidualLocal (χ₁ χ₂ : Character) (a b : PrimeIdeal → ℕ)
    (P : PrimeIdeal) (e₁ e₂ : ℕ) : ℂ :=
  if e₁ ≤ a P ∧ e₂ ≤ b P then
    (idealCoeff χ₁ P.val)^(a P-e₁)*(idealCoeff χ₂ P.val)^(b P-e₂) else 0

lemma goodPrimeKernel_factor (χ₁ χ₂ ψ₁ ψ₂ : Character) (a b : PrimeIdeal → ℕ)
    (P : PrimeIdeal) (j : Fin 7) :
    goodPrimeKernel χ₁ χ₂ ψ₁ ψ₂ a b P j=
      h3Term (idealCoeff ψ₁ P.val) (idealCoeff ψ₂ P.val) j*
        ordinaryResidualLocal χ₁ χ₂ a b P (h3Exponent j).1 (h3Exponent j).2 := by
  unfold goodPrimeKernel ordinaryResidualLocal
  split_ifs <;> ring

lemma exceptionalPrimeKernel_factor (χ₁ χ₂ ψ₁ ψ₂ : Character) (a b : PrimeIdeal → ℕ)
    (P : PrimeIdeal) (q : ℕ×ℕ) (j : Fin 4) :
    exceptionalPrimeKernel χ₁ χ₂ ψ₁ ψ₂ a b P q j=
      ((idealCoeff ψ₁ P.val)^q.1*(idealCoeff ψ₂ P.val)^q.2)*
        deletionTerm (idealCoeff χ₁ P.val) (idealCoeff χ₂ P.val) j*
        ordinaryResidualLocal χ₁ χ₂ a b P (q.1+deletionExponent₁ j) (q.2+deletionExponent₂ j) := by
  unfold exceptionalPrimeKernel ordinaryResidualLocal
  split_ifs <;> try simp only [Nat.sub_sub]
  all_goals ring

def goodResidualKernel (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal)
    (a b : PrimeIdeal → ℕ) (S : Finset (GoodPrimes bad)) (k : GoodIndex bad) : ℂ :=
  (∏ P : k.1,ordinaryResidualLocal χ₁ χ₂ a b P.val.val
      (h3Exponent (k.2 P)).1 (h3Exponent (k.2 P)).2)*
    ∏ P ∈ S \ k.1,ordinaryLocalCoefficient χ₁ χ₂ a b P.val

def badResidualKernel (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (a b : PrimeIdeal → ℕ)
    (j : DeletionIndex bad) (q : BadIndex bad allowed) : ℂ :=
  ∏ P : bad,ordinaryResidualLocal χ₁ χ₂ a b P.val
    ((q P).val.1+deletionExponent₁ (j P)) ((q P).val.2+deletionExponent₂ (j P))

def correctedResidualKernel (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (a b : PrimeIdeal → ℕ)
    (S : Finset (GoodPrimes bad)) (k : CorrectedIndex bad allowed) : ℂ :=
  badResidualKernel χ₁ χ₂ bad allowed a b k.1 k.2.1*
    goodResidualKernel χ₁ χ₂ bad a b S k.2.2

lemma goodFiniteKernel_factor (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (a b : PrimeIdeal → ℕ) (S : Finset (GoodPrimes bad)) (k : GoodIndex bad) :
    goodFiniteKernel χ₁ χ₂ ψ₁ ψ₂ bad a b S k=
      goodCoefficient ψ₁ ψ₂ bad k*goodResidualKernel χ₁ χ₂ bad a b S k := by
  unfold goodFiniteKernel
  simp_rw [goodPrimeKernel_factor]
  rw [Finset.prod_mul_distrib]
  unfold goodCoefficient goodResidualKernel h3Term
  ring

lemma badFiniteKernel_factor (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (a b : PrimeIdeal → ℕ)
    (j : DeletionIndex bad) (q : BadIndex bad allowed) :
    (∏ P : bad,exceptionalPrimeKernel χ₁ χ₂ ψ₁ ψ₂ a b P.val (q P).val (j P))=
      (badCoefficient ψ₁ ψ₂ bad allowed q*deletionCoefficient χ₁ χ₂ bad j)*
        badResidualKernel χ₁ χ₂ bad allowed a b j q := by
  simp_rw [exceptionalPrimeKernel_factor]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  rfl

/-- Every numerator coefficient is exactly the previously constructed
`correctedCoefficient`; the remaining factor is the ordinary residual kernel. -/
theorem correctedFiniteKernel_factor (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (a b : PrimeIdeal → ℕ)
    (S : Finset (GoodPrimes bad)) (k : CorrectedIndex bad allowed) :
    correctedFiniteKernel χ₁ χ₂ ψ₁ ψ₂ bad allowed a b S k=
      correctedCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed k*
        correctedResidualKernel χ₁ χ₂ bad allowed a b S k := by
  rw [correctedFiniteKernel,badFiniteKernel_factor,goodFiniteKernel_factor]
  unfold correctedCoefficient fullCoefficient correctedResidualKernel
  ring

/-- Finite, signed, coefficient-by-ideal convolution with the exact existing
numerator coefficients and the original row's zero-extended characters. -/
theorem literalCubePairCoefficient_expansion (χ₁ χ₂ ψ₁ ψ₂ : Character)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hχ₁ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₁ P.val=idealCoeff ψ₁ P.val)
    (hχ₂ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₂ P.val=idealCoeff ψ₂ P.val)
    (hbad : ∀ P ∈ bad, ∀ q ∈ allowed P,
      (idealCoeff χ₁ P.val)^q.1*(idealCoeff χ₂ P.val)^q.2=
        (idealCoeff ψ₁ P.val)^q.1*(idealCoeff ψ₂ P.val)^q.2)
    (I J : Ideal HeckeFamily.O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    literalCubePairCoefficient χ₁ χ₂ bad allowed I J=
      ∑ q : BadIndex bad allowed, ∑ j : DeletionIndex bad,
        ∑ T ∈ (goodPairSupport bad I J).powerset, ∑ k : T → Fin 7,
          correctedCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed (j,(q,⟨T,k⟩))*
            correctedResidualKernel χ₁ χ₂ bad allowed
              (ProbePhysical.primeValuations I) (ProbePhysical.primeValuations J)
              (goodPairSupport bad I J) (j,(q,⟨T,k⟩)) := by
  rw [literalCubePairCoefficient,
    ←correctedPairEulerCoefficient_original χ₁ χ₂ ψ₁ ψ₂ bad allowed hχ₁ hχ₂ hbad I J hI hJ,
    correctedPairEulerCoefficient_expansion]
  simp_rw [correctedFiniteKernel_factor]

theorem literalCubePair_finite_convolution (χ₁ χ₂ ψ₁ ψ₂ : Character)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hχ₁ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₁ P.val=idealCoeff ψ₁ P.val)
    (hχ₂ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₂ P.val=idealCoeff ψ₂ P.val)
    (hbad : ∀ P ∈ bad, ∀ q ∈ allowed P,
      (idealCoeff χ₁ P.val)^q.1*(idealCoeff χ₂ P.val)^q.2=
        (idealCoeff ψ₁ P.val)^q.1*(idealCoeff ψ₂ P.val)^q.2)
    (W₁ W₂ : ℝ → ℂ) (x y : ℝ)
    (S : Finset (ProbePhysical.NonzeroIdeal×ProbePhysical.NonzeroIdeal)) :
    (∑ p ∈ S,physicalPairTerm (literalCubePairCoefficient χ₁ χ₂ bad allowed)
      W₁ W₂ x y (p.1.val,p.2.val)) =
    ∑ p ∈ S, ∑ q : BadIndex bad allowed, ∑ j : DeletionIndex bad,
      ∑ T ∈ (goodPairSupport bad p.1.val p.2.val).powerset, ∑ k : T → Fin 7,
        correctedCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed (j,(q,⟨T,k⟩))*
          correctedResidualKernel χ₁ χ₂ bad allowed
            (ProbePhysical.primeValuations p.1.val) (ProbePhysical.primeValuations p.2.val)
            (goodPairSupport bad p.1.val p.2.val) (j,(q,⟨T,k⟩))*
          W₁ ((Ideal.absNorm p.1.val : ℝ)/x)*W₂ ((Ideal.absNorm p.2.val : ℝ)/y) := by
  apply Finset.sum_congr rfl
  intro p _
  unfold physicalPairTerm
  rw [literalCubePairCoefficient_expansion χ₁ χ₂ ψ₁ ψ₂ bad allowed hχ₁ hχ₂ hbad
    p.1.val p.2.val p.1.property p.2.property]
  simp_rw [Finset.sum_mul]

#print axioms literalCubePair_finite_convolution
#print axioms literalCubePairCoefficient_expansion
#print axioms correctedFiniteKernel_factor
end
end QRH.Cycle092.SignedCenter
