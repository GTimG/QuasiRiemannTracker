/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual fixed-arm Fourier/common/primary source identification. -/
import Candidate.C092.transport.FixedCubeGaussPrimary
import Candidate.C092.transport.FixedCubeGaussShift

set_option autoImplicit false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion FourierBridge
open CenteredMomentSecondSectorColumns CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentSmooth CenteredMomentRowNorm CenteredMomentChildAssembly CenteredMomentSecondScaled
open QRH.Cycle092.SignedCenter
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedCommonHeights
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- All common and second-divisor primary allocations, retaining the native
outside height phase and the original independent ordinary profiles. -/
def fullyAllocatedHeight (r : Source ι a b) (ha : 0<a) (D : FixedCubeDatum)
    (G L : Id) (v : ℝ) : ℂ :=
  residualPhase (r.X₁*r.X₂) r.d G v*
    fullyAllocatedCommonRow r D.row.χ G L (shiftedSlotCoefficient r v)
      (shiftedProfile₁ r ha v) (shiftedProfile₂ r ha v)

theorem sectorFixedHeight_eq_fullyAllocated (r : Source ι a b) (ha : 0<a)
    (D : FixedCubeDatum) (G : Id) (hG : Supported G) (L : Id) (hL : Squarefree L) (v : ℝ) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*sectorFixedHeight r ha D G hG L v=
      fullyAllocatedHeight r ha D G L v := by
  rw [sectorFixedHeight_eq_shifted_common r ha D G hG L v,
    commonMaskedRow_eq_fullyAllocated r D.row.χ G L hL]
  rfl

/-- Exact original fixed Gauss arm, with its full native dyadic column
window, equals the Fourier integral of the simultaneous full primary
allocation. No absolute value or analytic estimate is used. -/
theorem source_nativeGaussArm_window_fullyAllocated (r : Source ι a b) (ha : 0<a)
    (D : FixedCubeDatum) (η : Character) (χ : RayCharacter)
    (hη : D.η=childCharacter η χ) (hm : D.m=nativeSourceMask r)
    (G : Id) (hG : Supported G) (L : Id) (hL : Squarefree L)
    (t θ X : ℝ) (hX : 0<X) (V : ℝ→ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      (∑ I : sectorPool G hG.1 (Second.Concrete.S0 r ha),
        nativeGaussArm η t (Second.Concrete.S0 r ha) (sourceCoefficient r ha 1)
          G hG L χ D.A D.z I*columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ)=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        fullyAllocatedHeight r ha D G L (t+2*Real.pi*(w-θ)) := by
  rw [source_nativeGaussArm_window_integral r ha D η χ hη hm G hG L t θ X hX V hVc hVs,
    ←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with w
  have hh := sectorFixedHeight_eq_fullyAllocated r ha D G hG L hL (t+2*Real.pi*(w-θ))
  calc
    _ = (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X))*
        (MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
          sectorFixedHeight r ha D G hG L (t+2*Real.pi*(w-θ))) := by ring
    _ = _ := by rw [hh]

/-- Direct interface for the original rowPolynomial appearing in the native
second exceptional whole-kernel estimate. -/
theorem source_rowPolynomial_window_fullyAllocated (r : Source ι a b) (ha : 0<a)
    (D : FixedCubeDatum) (η : Character) (χ : RayCharacter)
    (hη : D.η=childCharacter η χ) (hm : D.m=nativeSourceMask r)
    (G : Id) (hG : Supported G) (L : Id) (hL : Squarefree L)
    (t θ X : ℝ) (hX : 0<X) (V : ℝ→ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      rowPolynomial Finset.univ (sectorElement G hG.1 (Second.Concrete.S0 r ha))
        (fun I=>divisorCoefficient L (sectorElement G hG.1 (Second.Concrete.S0 r ha))
          (movingCoefficient D.A (sectorElement G hG.1 (Second.Concrete.S0 r ha))
            (fun I=>sourceCoefficient r ha 1 (G*I)*heightCoeff η t I)) χ I*
          columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ) D.z=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        fullyAllocatedHeight r ha D G L (t+2*Real.pi*(w-θ)) := by
  have he : rowPolynomial Finset.univ (sectorElement G hG.1 (Second.Concrete.S0 r ha))
        (fun I=>divisorCoefficient L (sectorElement G hG.1 (Second.Concrete.S0 r ha))
          (movingCoefficient D.A (sectorElement G hG.1 (Second.Concrete.S0 r ha))
            (fun I=>sourceCoefficient r ha 1 (G*I)*heightCoeff η t I)) χ I*
          columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ) D.z=
      ∑I : sectorPool G hG.1 (Second.Concrete.S0 r ha),
        nativeGaussArm η t (Second.Concrete.S0 r ha) (sourceCoefficient r ha 1)
          G hG L χ D.A D.z I*columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ := by
    simp only [rowPolynomial,sectorElement_span,nativeGaussArm]
    apply Finset.sum_congr rfl
    intro I _
    ring
  rw [he]
  exact source_nativeGaussArm_window_fullyAllocated r ha D η χ hη hm G hG L hL t θ X hX V hVc hVs

#print axioms sectorFixedHeight_eq_fullyAllocated
#print axioms source_nativeGaussArm_window_fullyAllocated
#print axioms source_rowPolynomial_window_fullyAllocated
end
end QRH.Cycle092.FixedCubeGauss
