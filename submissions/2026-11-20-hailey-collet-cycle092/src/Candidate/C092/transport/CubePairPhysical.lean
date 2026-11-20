/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.CubePairIdeal

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

/-- The original two-ideal row coefficient, with all residual holes explicit. -/
def literalCubePairCoefficient (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (I J : Ideal O) : ℂ :=
  if PairAllowed bad allowed I J then idealCoeff χ₁ I*idealCoeff χ₂ J else 0

/-- The zero ideal is removed before valuation-based coefficient extraction. -/
def guardedPairEulerCoefficient (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (I J : Ideal O) : ℂ :=
  if I=0 ∨ J=0 then 0 else correctedPairEulerCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed I J

theorem guardedPairEulerCoefficient_eq_literal (χ₁ χ₂ ψ₁ ψ₂ : Character)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hχ₁ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₁ P.val=idealCoeff ψ₁ P.val)
    (hχ₂ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₂ P.val=idealCoeff ψ₂ P.val)
    (hbad : ∀ P ∈ bad, ∀ q ∈ allowed P,
      (idealCoeff χ₁ P.val)^q.1*(idealCoeff χ₂ P.val)^q.2=
        (idealCoeff ψ₁ P.val)^q.1*(idealCoeff ψ₂ P.val)^q.2)
    (I J : Ideal O) :
    guardedPairEulerCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed I J=
      literalCubePairCoefficient χ₁ χ₂ bad allowed I J := by
  unfold guardedPairEulerCoefficient literalCubePairCoefficient
  by_cases hi : I=0
  · simp only [hi, true_or, ite_true, map_zero, zero_mul, ite_self]
  · by_cases hj : J=0
    · simp only [hj, or_true, ite_true, map_zero, mul_zero, ite_self]
    · rw [ite_eq_right (not_or.mpr ⟨hi,hj⟩),
        correctedPairEulerCoefficient_original χ₁ χ₂ ψ₁ ψ₂ bad allowed hχ₁ hχ₂ hbad I J hi hj]

def physicalPairTerm (A : Ideal O → Ideal O → ℂ) (W₁ W₂ : ℝ → ℂ)
    (x y : ℝ) (p : Ideal O×Ideal O) : ℂ :=
  A p.1 p.2*W₁ ((Ideal.absNorm p.1 : ℝ)/x)*W₂ ((Ideal.absNorm p.2 : ℝ)/y)

/-- Any coefficient system has finite support under fixed annular profiles;
no convergence or cancellation is assumed to justify the finite physical sum. -/
lemma physicalPairTerm_hasFiniteSupport (A : Ideal O → Ideal O → ℂ) (W₁ W₂ : ℝ → ℂ)
    (b₁ b₂ x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    (physicalPairTerm A W₁ W₂ x y).HasFiniteSupport := by
  apply ((Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil (b₁*x))).prod
    (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil (b₂*y)))).subset
  intro p hp
  have hw₁ : W₁ ((Ideal.absNorm p.1 : ℝ)/x) ≠ 0 := by
    intro hz
    exact hp (by simp [physicalPairTerm,hz])
  have hw₂ : W₂ ((Ideal.absNorm p.2 : ℝ)/y) ≠ 0 := by
    intro hz
    exact hp (by simp [physicalPairTerm,hz])
  have h₁ : (Ideal.absNorm p.1 : ℝ) ≤ b₁*x := (div_le_iff₀ hx).mp (hs₁ hw₁)
  have h₂ : (Ideal.absNorm p.2 : ℝ) ≤ b₂*y := (div_le_iff₀ hy).mp (hs₂ hw₂)
  exact ⟨by exact_mod_cast h₁.trans (Nat.le_ceil (b₁*x)),
    by exact_mod_cast h₂.trans (Nat.le_ceil (b₂*y))⟩

/-- A finite physical sum over the original row equals the coefficient-by-ideal
Euler extraction. This does not yet regroup the result by `CorrectedIndex`. -/
theorem literalCubePair_finite_physical (χ₁ χ₂ ψ₁ ψ₂ : Character)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hχ₁ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₁ P.val=idealCoeff ψ₁ P.val)
    (hχ₂ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₂ P.val=idealCoeff ψ₂ P.val)
    (hbad : ∀ P ∈ bad, ∀ q ∈ allowed P,
      (idealCoeff χ₁ P.val)^q.1*(idealCoeff χ₂ P.val)^q.2=
        (idealCoeff ψ₁ P.val)^q.1*(idealCoeff ψ₂ P.val)^q.2)
    (W₁ W₂ : ℝ → ℂ) (x y : ℝ) (S : Finset (Ideal O×Ideal O)) :
    (∑ p ∈ S,physicalPairTerm (literalCubePairCoefficient χ₁ χ₂ bad allowed) W₁ W₂ x y p)=
      ∑ p ∈ S,physicalPairTerm
        (guardedPairEulerCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed) W₁ W₂ x y p := by
  apply Finset.sum_congr rfl
  intro p _
  simp only [physicalPairTerm,
    guardedPairEulerCoefficient_eq_literal χ₁ χ₂ ψ₁ ψ₂ bad allowed hχ₁ hχ₂ hbad]

theorem literalCubePair_physical_tsum (χ₁ χ₂ ψ₁ ψ₂ : Character)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hχ₁ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₁ P.val=idealCoeff ψ₁ P.val)
    (hχ₂ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₂ P.val=idealCoeff ψ₂ P.val)
    (hbad : ∀ P ∈ bad, ∀ q ∈ allowed P,
      (idealCoeff χ₁ P.val)^q.1*(idealCoeff χ₂ P.val)^q.2=
        (idealCoeff ψ₁ P.val)^q.1*(idealCoeff ψ₂ P.val)^q.2)
    (W₁ W₂ : ℝ → ℂ) (x y : ℝ) :
    (∑' p : Ideal O×Ideal O,
      physicalPairTerm (literalCubePairCoefficient χ₁ χ₂ bad allowed) W₁ W₂ x y p)=
      ∑' p : Ideal O×Ideal O,physicalPairTerm
        (guardedPairEulerCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed) W₁ W₂ x y p := by
  apply tsum_congr
  intro p
  simp only [physicalPairTerm,
    guardedPairEulerCoefficient_eq_literal χ₁ χ₂ ψ₁ ψ₂ bad allowed hχ₁ hχ₂ hbad]

#print axioms literalCubePair_finite_physical
#print axioms physicalPairTerm_hasFiniteSupport
#print axioms literalCubePair_physical_tsum
end
end QRH.Cycle092.SignedCenter
