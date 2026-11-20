/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.CubePairSource

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

/-- Freeze the actual supplying primes first; each coordinate can retain its
own additional punctures. No smoothness of these arithmetic masks is assumed. -/
def supplyingPrimeKeep (supplying holes : Finset PrimeIdeal) (P : PrimeIdeal) : Bool :=
  decide (P ∉ supplying ∧ P ∉ holes)

def supplyingResidualPairs (R₁ R₂ : OrdinaryRow) (supplying holes₁ holes₂ : Finset PrimeIdeal)
    (P : PrimeIdeal) : Finset (ℕ×ℕ) :=
  ordinaryResidualPairs R₁ R₂ (supplyingPrimeKeep supplying holes₁)
    (supplyingPrimeKeep supplying holes₂) P

lemma supplyingResidualPairs_at_supplier (R₁ R₂ : OrdinaryRow)
    (supplying holes₁ holes₂ : Finset PrimeIdeal) (P : PrimeIdeal) (hP : P ∈ supplying) :
    supplyingResidualPairs R₁ R₂ supplying holes₁ holes₂ P={(0,0)} := by
  ext q
  rw [supplyingResidualPairs,mem_ordinaryResidualPairs]
  simp only [supplyingPrimeKeep,hP,not_true_eq_false,false_and,decide_false,
    Bool.false_eq_true,and_false,false_or,Finset.mem_singleton]
  constructor
  · rintro ⟨_,h₁,h₂⟩
    exact Prod.ext h₁ h₂
  · intro h
    subst q
    simp

/-- Every allowed submask retains both supplier deletions; further seeds and
holes may reduce this set, including to the empty source. -/
lemma allowed_supplier_valuations_zero (R₁ R₂ : OrdinaryRow)
    (bad supplying holes₁ holes₂ : Finset PrimeIdeal)
    (hsupply : supplying ⊆ bad) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hallowed : ∀ P ∈ bad,allowed P ⊆ supplyingResidualPairs R₁ R₂ supplying holes₁ holes₂ P)
    (I J : Ideal O) (hIJ : PairAllowed bad allowed I J)
    (P : PrimeIdeal) (hP : P ∈ supplying) :
    ProbePhysical.primeValuations I P=0 ∧ ProbePhysical.primeValuations J P=0 := by
  have h := hallowed P (hsupply hP) (hIJ.2 P (hsupply hP))
  rw [supplyingResidualPairs_at_supplier R₁ R₂ supplying holes₁ holes₂ P hP,
    Finset.mem_singleton] at h
  exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩

/-- Exact source equality after the supplying assignment is frozen, retaining
separate coordinate holes, arbitrary further residual restrictions and the same
two independent heights/profiles as the source. -/
theorem correctedConvolutionSource_eq_supplying (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (bad supplying holes₁ holes₂ : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hgood₁ : ∀ P : PrimeIdeal,P ∉ bad → IsCoprime P.val R₁.χ.modulus)
    (hgood₂ : ∀ P : PrimeIdeal,P ∉ bad → IsCoprime P.val R₂.χ.modulus)
    (hallowed : ∀ P ∈ bad,allowed P ⊆ supplyingResidualPairs R₁ R₂ supplying holes₁ holes₂ P)
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    correctedConvolutionSource R₁ R₂ P₁ P₂ bad allowed x y=
      literalCubePairSource R₁ R₂ P₁ P₂ bad allowed x y :=
  ordinaryRow_correctedConvolutionSource R₁ R₂ P₁ P₂ bad
    (supplyingPrimeKeep supplying holes₁) (supplyingPrimeKeep supplying holes₂)
    allowed hgood₁ hgood₂ hallowed x y hx hy

#print axioms allowed_supplier_valuations_zero
#print axioms correctedConvolutionSource_eq_supplying
end
end QRH.Cycle092.SignedCenter
