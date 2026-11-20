/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.CubePairResidual

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily

lemma OrdinaryRow.prime_coefficient_inducing (R : OrdinaryRow) (P : PrimeIdeal)
    (hc : IsCoprime P.val R.χ.modulus) : idealCoeff R.χ P.val=idealCoeff R.ψ P.val := by
  rw [R.hind P.val,ite_eq_left hc]

/-- Keep flags include the presented modulus holes before adding any further
literal source restriction. -/
def ordinaryPrimeKeep (R : OrdinaryRow) (P : PrimeIdeal) : Bool :=
  decide (IsCoprime P.val R.χ.modulus)

def ordinaryResidualPairs (R₁ R₂ : OrdinaryRow) (keep₁ keep₂ : PrimeIdeal → Bool)
    (P : PrimeIdeal) : Finset (ℕ×ℕ) :=
  residualPairs (ordinaryPrimeKeep R₁ P && keep₁ P) (ordinaryPrimeKeep R₂ P && keep₂ P)

lemma ordinaryResidualPairs_subset (R₁ R₂ : OrdinaryRow) (keep₁ keep₂ : PrimeIdeal → Bool)
    (P : PrimeIdeal) : ordinaryResidualPairs R₁ R₂ keep₁ keep₂ P ⊆ residualPairs true true :=
  residualPairs_subset _ _

/-- Primitive induction is used only on coordinates actually kept by the
original row; zero powers need no character nonvanishing premise. -/
theorem ordinaryResidualPairs_agreement (R₁ R₂ : OrdinaryRow)
    (keep₁ keep₂ : PrimeIdeal → Bool) (P : PrimeIdeal) (q : ℕ×ℕ)
    (hq : q ∈ ordinaryResidualPairs R₁ R₂ keep₁ keep₂ P) :
    (idealCoeff R₁.χ P.val)^q.1*(idealCoeff R₂.χ P.val)^q.2=
      (idealCoeff R₁.ψ P.val)^q.1*(idealCoeff R₂.ψ P.val)^q.2 := by
  apply residualPairs_coefficient_agreement _ _ _ _ _ _ ?_ ?_ q hq
  · intro h
    have hc : IsCoprime P.val R₁.χ.modulus := by
      have hh := h
      simp only [ordinaryPrimeKeep,Bool.and_eq_true,decide_eq_true_eq] at hh
      exact hh.1
    exact R₁.prime_coefficient_inducing P hc
  · intro h
    have hc : IsCoprime P.val R₂.χ.modulus := by
      have hh := h
      simp only [ordinaryPrimeKeep,Bool.and_eq_true,decide_eq_true_eq] at hh
      exact hh.1
    exact R₂.prime_coefficient_inducing P hc

/-- Source-backed instantiation of coefficient extraction for authentic
ordinary rows and any further subset of their actual residual masks. -/
theorem ordinaryRow_guardedPairEulerCoefficient (R₁ R₂ : OrdinaryRow)
    (bad : Finset PrimeIdeal) (keep₁ keep₂ : PrimeIdeal → Bool)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hgood₁ : ∀ P : PrimeIdeal,P ∉ bad → IsCoprime P.val R₁.χ.modulus)
    (hgood₂ : ∀ P : PrimeIdeal,P ∉ bad → IsCoprime P.val R₂.χ.modulus)
    (hallowed : ∀ P ∈ bad,allowed P ⊆ ordinaryResidualPairs R₁ R₂ keep₁ keep₂ P)
    (I J : Ideal HeckeFamily.O) :
    guardedPairEulerCoefficient R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed I J=
      literalCubePairCoefficient R₁.χ R₂.χ bad allowed I J := by
  apply guardedPairEulerCoefficient_eq_literal
  · intro P hP
    exact R₁.prime_coefficient_inducing P (hgood₁ P hP)
  · intro P hP
    exact R₂.prime_coefficient_inducing P (hgood₂ P hP)
  · intro P hP q hq
    exact ordinaryResidualPairs_agreement R₁ R₂ keep₁ keep₂ P q (hallowed P hP hq)

theorem ordinaryRow_finite_convolution (R₁ R₂ : OrdinaryRow)
    (bad : Finset PrimeIdeal) (keep₁ keep₂ : PrimeIdeal → Bool)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hgood₁ : ∀ P : PrimeIdeal,P ∉ bad → IsCoprime P.val R₁.χ.modulus)
    (hgood₂ : ∀ P : PrimeIdeal,P ∉ bad → IsCoprime P.val R₂.χ.modulus)
    (hallowed : ∀ P ∈ bad,allowed P ⊆ ordinaryResidualPairs R₁ R₂ keep₁ keep₂ P)
    (W₁ W₂ : ℝ → ℂ) (x y : ℝ)
    (S : Finset (ProbePhysical.NonzeroIdeal×ProbePhysical.NonzeroIdeal)) :
    (∑ p ∈ S,physicalPairTerm (literalCubePairCoefficient R₁.χ R₂.χ bad allowed)
      W₁ W₂ x y (p.1.val,p.2.val)) =
    ∑ p ∈ S, ∑ q : BadIndex bad allowed, ∑ j : DeletionIndex bad,
      ∑ T ∈ (goodPairSupport bad p.1.val p.2.val).powerset, ∑ k : T → Fin 7,
        correctedCoefficient R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed (j,(q,⟨T,k⟩))*
          correctedResidualKernel R₁.χ R₂.χ bad allowed
            (ProbePhysical.primeValuations p.1.val) (ProbePhysical.primeValuations p.2.val)
            (goodPairSupport bad p.1.val p.2.val) (j,(q,⟨T,k⟩))*
          W₁ ((Ideal.absNorm p.1.val : ℝ)/x)*W₂ ((Ideal.absNorm p.2.val : ℝ)/y) := by
  apply literalCubePair_finite_convolution
  · intro P hP
    exact R₁.prime_coefficient_inducing P (hgood₁ P hP)
  · intro P hP
    exact R₂.prime_coefficient_inducing P (hgood₂ P hP)
  · intro P hP q hq
    exact ordinaryResidualPairs_agreement R₁ R₂ keep₁ keep₂ P q (hallowed P hP hq)

#print axioms ordinaryRow_finite_convolution
#print axioms ordinaryResidualPairs_agreement
#print axioms ordinaryRow_guardedPairEulerCoefficient
end
end QRH.Cycle092.SignedCenter
