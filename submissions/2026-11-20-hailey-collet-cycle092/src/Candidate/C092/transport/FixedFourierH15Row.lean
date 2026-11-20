/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual Fourier window retains its full Schwartz moment and height cost. -/
import Candidate.C092.transport.FixedFourierH15Pointwise
import Candidate.C092.transport.FixedPhysicalPaymentAll

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion FourierBridge
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSmooth
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentDivisorAllocation
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedCommonHeights
open CenteredMomentRowNorm CenteredMomentSecondSectorColumns CenteredMomentChildRows CenteredMomentChildAssembly
open QRH.Cycle092.SignedCenter MixedPrincipalWindow MixedCommonRestriction
open CenteredMomentFirstAmplificationChoice ConcreteTraceCRT
open QRH.Cycle092.FixedCubeGauss
namespace QRH.Cycle092.FixedFourierH15
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- This is the literal original colored sector polynomial in H.15. -/
def nativeRowPolynomial (r : Source ι a b) (ha : 0<a) (D : FixedCubeDatum)
    (ω₁ ω₂ η : Character) (χ : RayCharacter) (G : Id) (hG : Supported G) (L : Id)
    (t : ℝ) : ℂ :=
  rowPolynomial Finset.univ (CenteredMomentSecondSectorColumns.sectorElement G hG.1 (sourceColumns r))
    (fun I=>divisorCoefficient L
      (CenteredMomentSecondSectorColumns.sectorElement G hG.1 (sourceColumns r))
      (CenteredMomentSecondScaled.movingCoefficient D.A
        (CenteredMomentSecondSectorColumns.sectorElement G hG.1 (sourceColumns r))
        (fun I=>TwistedRawSource.sourceColumn r ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I)*heightCoeff η t I)) χ I) D.z


/-- Exact unwindowed original row. Both ordinary colors and original height
remain, with the same native mask and fixed inducing datum. -/
lemma nativeRowPolynomial_eq_height (r : Source ι a b) (ha : 0<a) (hb : 0 ≤ b)
    (D : FixedCubeDatum) (ω₁ ω₂ η : Character) (χ : RayCharacter)
    (hη : D.η=childCharacter η χ) (hm : D.m=nativeSourceMask r)
    (G : Id) (hG : Supported G) (L : Id) (hL : Squarefree L) (t : ℝ) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      nativeRowPolynomial r ha D ω₁ ω₂ η χ G hG L t=
      coloredFullyAllocatedPhysicalHeight r ha hb D ω₁ ω₂ G L t := by
  rw [←coloredSectorFixedHeight_eq_physical r ha hb D ω₁ ω₂ G hG L hL]
  congr 1
  have he : nativeRowPolynomial r ha D ω₁ ω₂ η χ G hG L t=
      ∑I : sectorPool G hG.1 (sourceColumns r),nativeGaussArm η t (sourceColumns r)
        (TwistedRawSource.sourceColumn r ha (idealCoeff ω₁) (idealCoeff ω₂) 1) G hG L χ D.A D.z I := by
    simp only [nativeRowPolynomial,rowPolynomial,sectorElement_span,nativeGaussArm]
  rw [he]
  unfold coloredSectorFixedHeight
  apply Finset.sum_congr rfl
  intro I _
  rw [colored_nativeGaussArm_eq_fixedCoefficient r ha (idealCoeff ω₁) (idealCoeff ω₂) D η χ hη hm t G hG L I]
  simp only [heightCoeff,D.row_spec.2.2.2]
  split_ifs <;> ring

/-- The actual ball weight is retained in the native one-row energy. -/
def nativeRowBallEnergy (r : Source ι a b) (ha : 0<a) (D : FixedCubeDatum)
    (ω₁ ω₂ η : Character) (χ : RayCharacter) (G : Id) (hG : Supported G) (L : Id)
    (t H : ℝ) : ℝ :=
  ‖nativeRowPolynomial r ha D ω₁ ω₂ η χ G hG L t‖^2*
    (ballProfile (‖eisEmbedding D.z‖^2/H)).re

lemma nativeRowBallEnergy_nonneg (r : Source ι a b) (ha : 0<a) (D : FixedCubeDatum)
    (ω₁ ω₂ η : Character) (χ : RayCharacter) (G : Id) (hG : Supported G) (L : Id) (t H : ℝ) :
    0 ≤ nativeRowBallEnergy r ha D ω₁ ω₂ η χ G hG L t H :=
  mul_nonneg (sq_nonneg _) (ballProfile_nonneg _)

lemma nativeRowBallEnergy_le_square (r : Source ι a b) (ha : 0<a) (D : FixedCubeDatum)
    (ω₁ ω₂ η : Character) (χ : RayCharacter) (G : Id) (hG : Supported G) (L : Id) (t H : ℝ) :
    nativeRowBallEnergy r ha D ω₁ ω₂ η χ G hG L t H ≤
      ‖nativeRowPolynomial r ha D ω₁ ω₂ η χ G hG L t‖^2 :=
  mul_le_of_le_one_right (sq_nonneg _) (ballProfile_le_one _)

#print axioms nativeRowPolynomial_eq_height
end QRH.Cycle092.FixedFourierH15
