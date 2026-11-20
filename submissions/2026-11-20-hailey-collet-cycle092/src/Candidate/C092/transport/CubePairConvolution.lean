/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.CubePairDivisorTransport
import Candidate.C092.transport.CubePairMask
import Candidate.C092.transport.SignedCenterUniform

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentHeckeCancellation CenteredMomentHeckeHeight CenteredMomentTwist
local notation "O" => HeckeFamily.O

/-- The full indexed physical family is finite: annular support bounds the
actual ideal pair, and each fixed pair has finitely many Euler extractions. -/
lemma idealConvolutionPhysical_hasFiniteSupport (χ₁ χ₂ ψ₁ ψ₂ : Character)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    (fun pk : (Ideal O×Ideal O)×CorrectedIndex bad allowed =>
      physicalPairTerm (fun I J => idealConvolutionCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed I J pk.2)
        W₁ W₂ x y pk.1).HasFiniteSupport := by
  have hP := physicalPairTerm_hasFiniteSupport (fun _ _ => 1) W₁ W₂ b₁ b₂ x y hx hy hs₁ hs₂
  have hU := hP.biUnion (fun p _ =>
    (idealConvolutionCoefficient_hasFiniteSupport χ₁ χ₂ ψ₁ ψ₂ bad allowed p.1 p.2).image
      (fun k => (p,k)))
  apply hU.subset
  rintro ⟨p,k⟩ hk
  have hpk : physicalPairTerm (fun _ _ => 1) W₁ W₂ x y p ≠ 0 := by
    intro he
    have he' : W₁ ((Ideal.absNorm p.1 : ℝ)/x)*W₂ ((Ideal.absNorm p.2 : ℝ)/y)=0 := by
      simpa only [physicalPairTerm,one_mul] using he
    apply hk
    dsimp only [physicalPairTerm]
    rw [mul_assoc,he',mul_zero]
  have hkk : idealConvolutionCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed p.1 p.2 k ≠ 0 := by
    intro he
    exact hk (by simp only [physicalPairTerm,he,zero_mul])
  exact Set.mem_iUnion_of_mem p (Set.mem_iUnion_of_mem hpk ⟨k,hkk,rfl⟩)

/-- Genuine Euler coefficient convolution equals the original coupled ideal
sum, before any signed estimate is used. No injectivity of extraction indices
or division by character coefficients is needed. -/
theorem literalCubePair_convolution (χ₁ χ₂ ψ₁ ψ₂ : Character)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hχ₁ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₁ P.val=idealCoeff ψ₁ P.val)
    (hχ₂ : ∀ P : PrimeIdeal,P ∉ bad → idealCoeff χ₂ P.val=idealCoeff ψ₂ P.val)
    (hbad : ∀ P ∈ bad, ∀ q ∈ allowed P,
      (idealCoeff χ₁ P.val)^q.1*(idealCoeff χ₂ P.val)^q.2=
        (idealCoeff ψ₁ P.val)^q.1*(idealCoeff ψ₂ P.val)^q.2)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    (∑' p : Ideal O×Ideal O,physicalPairTerm
      (literalCubePairCoefficient χ₁ χ₂ bad allowed) W₁ W₂ x y p)=
    ∑' k : CorrectedIndex bad allowed,correctedCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed k*
      (idealSum χ₁ W₁ (x/(Ideal.absNorm (correctedIdeal₁ bad allowed k) : ℝ))*
        idealSum χ₂ W₂ (y/(Ideal.absNorm (correctedIdeal₂ bad allowed k) : ℝ))) := by
  have hfin := idealConvolutionPhysical_hasFiniteSupport χ₁ χ₂ ψ₁ ψ₂ bad allowed
    W₁ W₂ b₁ b₂ x y hx hy hs₁ hs₂
  calc
    _ = ∑' p : Ideal O×Ideal O,∑' k : CorrectedIndex bad allowed,
        physicalPairTerm (fun I J => idealConvolutionCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed I J k)
          W₁ W₂ x y p := by
      apply tsum_congr
      intro p
      simp only [physicalPairTerm,
        literalCubePairCoefficient_global χ₁ χ₂ ψ₁ ψ₂ bad allowed hχ₁ hχ₂ hbad,
        tsum_mul_right]
    _ = ∑' k : CorrectedIndex bad allowed,∑' p : Ideal O×Ideal O,
        physicalPairTerm (fun I J => idealConvolutionCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed I J k)
          W₁ W₂ x y p := (summable_of_hasFiniteSupport hfin).prod_symm.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro k
      simp only [physicalPairTerm,idealConvolutionCoefficient,mul_assoc,tsum_mul_left]
      rw [←idealResidualCoefficient_profile_tsum χ₁ χ₂ bad allowed k W₁ W₂ b₁ b₂ x y hx hy hs₁ hs₂]
      simp only [physicalPairTerm,mul_assoc]

/-- Original coupled source at the two independent normalized heights. -/
def literalCubePairSource (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (x y : ℝ) : ℂ :=
  ∑' p : Ideal O×Ideal O,physicalPairTerm
    (literalCubePairCoefficient R₁.χ R₂.χ bad allowed) P₁.normalized P₂.normalized x y p

/-- Source identification for actual ordinary rows, with the original modulus
holes and any additional retained source masks at all exceptional primes. -/
theorem ordinaryRow_correctedConvolutionSource (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (keep₁ keep₂ : PrimeIdeal → Bool)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hgood₁ : ∀ P : PrimeIdeal,P ∉ bad → IsCoprime P.val R₁.χ.modulus)
    (hgood₂ : ∀ P : PrimeIdeal,P ∉ bad → IsCoprime P.val R₂.χ.modulus)
    (hallowed : ∀ P ∈ bad,allowed P ⊆ ordinaryResidualPairs R₁ R₂ keep₁ keep₂ P)
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    correctedConvolutionSource R₁ R₂ P₁ P₂ bad allowed x y=
      literalCubePairSource R₁ R₂ P₁ P₂ bad allowed x y := by
  have hs₁ : Function.support (P₁.normalized : ℝ → ℂ) ⊆ Set.Iic P₁.b :=
    (normPowerProfile_support P₁.W P₁.a P₁.b P₁.ha P₁.hs P₁.hW P₁.t).trans
      (fun _ h => (P₁.hs h).2)
  have hs₂ : Function.support (P₂.normalized : ℝ → ℂ) ⊆ Set.Iic P₂.b :=
    (normPowerProfile_support P₂.W P₂.a P₂.b P₂.ha P₂.hs P₂.hW P₂.t).trans
      (fun _ h => (P₂.hs h).2)
  symm
  exact literalCubePair_convolution R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed
    (fun P hP => R₁.prime_coefficient_inducing P (hgood₁ P hP))
    (fun P hP => R₂.prime_coefficient_inducing P (hgood₂ P hP))
    (fun P hP q hq => ordinaryResidualPairs_agreement R₁ R₂ keep₁ keep₂ P q (hallowed P hP hq))
    P₁.normalized P₂.normalized P₁.b P₂.b x y hx hy hs₁ hs₂

#print axioms literalCubePair_convolution
#print axioms ordinaryRow_correctedConvolutionSource
end
end QRH.Cycle092.SignedCenter
