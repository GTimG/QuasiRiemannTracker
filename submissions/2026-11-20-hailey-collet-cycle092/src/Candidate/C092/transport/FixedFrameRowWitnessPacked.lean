/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Authentic packed/family coefficient transport at every Fourier row. -/
import Candidate.C092.transport.FixedFrameRowWitnessPolynomial
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedFrameRowWitness
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentRowNorm
open CenteredMomentSecondExceptionalFamily CenteredMomentChildRows CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentSourceRow CenteredMomentFirstSectors
open QRH.SilDensitySplit.CubeFree
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L mesh Z : ℝ} {θ : GData L}

lemma packed_coefficient_eq {η : Character} (P : SidePack η) (ξ : RayFourExpansion.RayCharacter)
    {C D : Id} {hC : Supported C} {hD : Supported D}
    {U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D)}
    {τ : RayFourExpansion.RayCharacter→Character}
    (hfam : Family (childCharacter P.base ξ) C D hC hD U τ) (χ : RayFourExpansion.RayCharacter)
    (G : Id) (hG : Supported G)
    (hGc : ∀I,IsCoprime G I → IsCoprime C I ∨ IsCoprime D I)
    (I : Id) (hI : Supported I) (hw : IsCoprime I (Ideal.span {packMask P.Z₀ G})) :
    idealCoeff (τ χ) I=idealCoeff (packedChar η (P.j₀*ξ*χ) (P.V*secondTwist C D U)) I := by
  have hV := mul_ne_zero P.hV (secondTwist_ne_zero C D hC U)
  obtain ⟨hz,hc⟩ := packMask_coprime _ _ I hw
  have h1 := second_packed_side P ξ hfam χ I hI hz (hGc I hc) 0
  rw [Packet.heightCoeff_zero,Packet.heightCoeff_zero] at h1
  rw [h1,packedChar_coef η _ _ hV I hI]

lemma masked_column_coprime {η : Character} (P : SidePack η)
    (G : Id) (hG : Supported G) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a)
    (ω₁ ω₂ : Character) (E : Id) (hCR : P.Cs∣s.R) :
    ∀I∈residualPool G hG.1 (sourceColumns s),Supported I →
      (if IsCoprime G I ∧ E∣I then sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I) else 0)≠0 →
        IsCoprime I (Ideal.span {packMask P.Z₀ G}) := by
  intro I hI hs hc
  have hmask : IsCoprime G I ∧ E∣I := by
    by_contra hn
    exact hc (if_neg hn)
  have h0 : sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I)≠0 := by
    simpa only [if_pos hmask] using hc
  have hcop := ColoredGaussFrameProvider.originalColumn_coprime ω₁ ω₂
    s.S s.H s.pool s.d s.hd s.R 1 s.ν s.Wslot s.P _ _ θ.b s.X₁ s.X₂ s.Y₁ s.Y₂ (G*I)
    (by rwa [←ColoredGaussFrameProvider.sourceColumn_original s ha (idealCoeff ω₁) (idealCoeff ω₂) 1])
  have hz := P.zcop I ((hcop.of_isCoprime_of_dvd_right hCR).of_mul_left_right)
  rw [packMask,ConcretePrimeRowBridge.span_idealGenerator]
  exact IsCoprime.mul_right hz hmask.1.symm

/-- The same masked coefficients have the same polynomial before any tsum. -/
lemma packed_polynomial_eq {η : Character} (P : SidePack η) (ξ : RayFourExpansion.RayCharacter)
    {C D : Id} {hC : Supported C} {hD : Supported D}
    {U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D)}
    {τ : RayFourExpansion.RayCharacter→Character}
    (hfam : Family (childCharacter P.base ξ) C D hC hD U τ) (χ : RayFourExpansion.RayCharacter)
    (G : Id) (hG : Supported G)
    (hGc : ∀I,IsCoprime G I → IsCoprime C I ∨ IsCoprime D I)
    (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ : Character)
    (E : Id) (hCR : P.Cs∣s.R) (v : ℝ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator (residualPool G hG.1 (sourceColumns s)))
      (fun I : supportedColumns (residualPool G hG.1 (sourceColumns s))=>
        (if IsCoprime G (I:Id) ∧ E∣(I:Id) then sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I) else 0)*
          heightCoeff (τ χ) v I) z =
    rowPolynomial Finset.univ (sourceGenerator (residualPool G hG.1 (sourceColumns s)))
      (fun I : supportedColumns (residualPool G hG.1 (sourceColumns s))=>
        (if IsCoprime G (I:Id) ∧ E∣(I:Id) then sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I) else 0)*
          heightCoeff (packedChar η (P.j₀*ξ*χ) (P.V*secondTwist C D U)) v I) z := by
  exact polynomial_character_congr _ _ _ _ (packMask P.Z₀ G) (packMask_ne_zero _ _ P.hZ₀ hG)
    (packed_coefficient_eq P ξ hfam χ G hG hGc) (masked_column_coprime P G hG s ha ω₁ ω₂ E hCR) v z

lemma initialFixed_packed_eq {η : Character} (P : SidePack η) (ξ : RayFourExpansion.RayCharacter)
    {C D : Id} {hC : Supported C} {hD : Supported D}
    {U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D)}
    {τ : RayFourExpansion.RayCharacter→Character}
    (hfam : Family (childCharacter P.base ξ) C D hC hD U τ) (χ : RayFourExpansion.RayCharacter)
    (G : Id) (hG : Supported G)
    (hGc : ∀I,IsCoprime G I → IsCoprime C I ∨ IsCoprime D I) (Q : Id) :
    FixedPhysicalClassLedger.initialFixed (τ χ) Q=
      FixedPhysicalClassLedger.initialFixed (packedChar η (P.j₀*ξ*χ) (P.V*secondTwist C D U)) Q :=
  FixedPhysicalClassLedger.initialFixed_congr _ _ Q (packMask P.Z₀ G) (packMask_ne_zero _ _ P.hZ₀ hG)
    (packed_coefficient_eq P ξ hfam χ G hG hGc)

#print axioms packed_polynomial_eq
#print axioms initialFixed_packed_eq
end
end QRH.Cycle092.FixedFrameRowWitness
