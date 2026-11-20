/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Every actual packed fixed label supplies authentic per-z native H15 data. -/
import Candidate.C092.transport.FixedFrameRowWitnessPacked
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedFrameRowWitness
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSectorLocalization
open CenteredMomentRowNorm CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentSecondExceptionalFamily CenteredMomentChildRows CenteredMomentFirstPhysicalSource
open CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentSourceRow CenteredMomentFirstSectors
open QRH.SilDensitySplit.CubeFree
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.Cycle092.FixedFourierH15 QRH.Cycle092.SignedCenter
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L mesh Z : ℝ} {θ : GData L}

/-- Pointwise authentic witness, before summing any rows. The inherited
    native puncture is used in FixedCubeDatum, with all original masks intact. -/
theorem label_row_witness {η : Character} (P : SidePack η) (ξ : RayFourExpansion.RayCharacter)
    {C E : Id} {hC : Supported C} {hE : Supported E}
    {U : Finset (CenteredMomentCanonicalFirst.CommonIndex C E)}
    {τ : RayFourExpansion.RayCharacter→Character}
    (hfam : Family (childCharacter P.base ξ) C E hC hE U τ) (χ : RayFourExpansion.RayCharacter)
    (G : Id) (hG : Supported G)
    (hGc : ∀I,IsCoprime G I → IsCoprime C I ∨ IsCoprime E I)
    (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ : Character) (rs : GSrc θ mesh Z)
    (hV₀ : rs.V₀=P.V) (hCR : P.Cs∣s.R) (Q : Id) (hQ : Q≠0)
    (x : LabelData) (hj : x.j=P.j₀*ξ*χ) (hA : x.A₂=secondTwist C E U)
    (hxG : x.G=G) (hseed : x.seed=1)
    (hf : Fits η rs (x.toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η)) (v : ℝ) (z : O)
    (hz : FixedPhysicalClassLedger.initialFixed ((x.toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η).char rs) Q z) :
    ∃ D : FixedCubeDatum,
      D.η=childCharacter (childCharacter P.base ξ) χ ∧ D.Q=Q ∧
      D.m=FixedCubeGauss.nativeSourceMask s ∧ D.A=secondTwist C E U ∧ D.z=z ∧
      FixedPhysicalClassLedger.rowEnergy s ha ω₁ ω₂ η rs Q (x.toLabel η) v z =
        nativeRowBallEnergy s ha D ω₁ ω₂ (childCharacter P.base ξ) χ G hG x.D v (dyadicScale (x.n 1)) := by
  subst G
  have hch : (x.toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η).char rs =
      packedChar η (P.j₀*ξ*χ) (P.V*secondTwist C E U) := by
    simp only [LabelData.toLabel,hj,hA,hV₀]
  have hinit := initialFixed_packed_eq P ξ hfam χ x.G hG hGc Q
  have hzf : FixedPhysicalClassLedger.initialFixed (τ χ) Q z := by
    rw [hinit]
    rwa [hch] at hz
  have hmn : FixedCubeGauss.nativeSourceMask s≠0 :=
    mul_ne_zero fixedBadMask_ne_zero (ConcretePrimeRowBridge.idealGenerator_ne_zero s.R s.hR)
  have hml : ConcretePrimeRowBridge.goodLambda∣FixedCubeGauss.nativeSourceMask s :=
    (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  have hm2 : (2:O)∣FixedCubeGauss.nativeSourceMask s :=
    (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  have hkeep : FixedPhysicalClassLedger.fixedKeep (childCharacter P.base ξ) χ Q
      (FixedCubeGauss.nativeSourceMask s) (secondTwist C E U) z := by
    rw [FixedPhysicalClassLedger.family_fixed_keep hfam χ Q _ hmn hml hm2]
    exact hzf
  let D := fixedDatum (childCharacter (childCharacter P.base ξ) χ) Q
    (FixedCubeGauss.nativeSourceMask s) (secondTwist C E U) z hQ hmn
    (secondTwist_ne_zero C E hC U) hkeep.1 hml hm2 hkeep.2
  refine ⟨D,rfl,rfl,rfl,rfl,rfl,?_⟩
  have hp := packed_polynomial_eq P ξ hfam χ x.G hG hGc s ha ω₁ ω₂ x.D hCR v z
  have hn := masked_polynomial_eq_native s ha ω₁ ω₂ (childCharacter P.base ξ) (τ χ) χ D x.G hG x.D
    (fun I hI hc t=>hfam.height_eq χ I hI (hGc I hc) t) v
  unfold FixedPhysicalClassLedger.rowEnergy
  rw [dif_pos hf,if_pos hz]
  change _ = ‖nativeRowPolynomial s ha D ω₁ ω₂ (childCharacter P.base ξ) χ x.G hG x.D v‖^2*
    (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2/dyadicScale (x.n 1))).re
  have he : rowPolynomial Finset.univ
      (sourceGenerator (residualPool x.G hf.G_ne (sourceColumns s)))
      (fun I : supportedColumns (residualPool x.G hf.G_ne (sourceColumns s))=>
        (if IsCoprime x.G (I:Id) ∧ x.D∣(I:Id) then
          sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) x.seed (x.G*I) else 0)*
            heightCoeff ((x.toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η).char rs) v I) z =
      nativeRowPolynomial s ha D ω₁ ω₂ (childCharacter P.base ξ) χ x.G hG x.D v := by
    rw [hch]
    simpa only [hseed] using hp.symm.trans hn
  exact congrArg (fun p : ℂ=>‖p‖^2*
    (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2/dyadicScale (x.n 1))).re) he

#print axioms label_row_witness
end
end QRH.Cycle092.FixedFrameRowWitness
