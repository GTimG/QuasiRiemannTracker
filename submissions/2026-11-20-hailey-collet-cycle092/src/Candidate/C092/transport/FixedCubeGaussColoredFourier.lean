/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussColoredMask
import Candidate.C092.transport.TwistedRawSourceColumns

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion FourierBridge
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSecondSectorColumns CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentSmooth CenteredMomentChildAssembly CenteredMomentSecondScaled QRH.Cycle092.SignedCenter
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- Multiplicative ordinary colors cannot remove the original R-puncture. -/
theorem coloredSourceColumn_coprime (r : Source ι a b) (ha : 0<a)
    (ω₁ ω₂ : Id→ℂ) (seed J : Id)
    (hβ : TwistedRawSource.sourceColumn r ha ω₁ ω₂ seed J≠0) : IsCoprime J r.R := by
  by_contra hcop
  apply hβ
  unfold TwistedRawSource.sourceColumn finiteColumnCoefficient
  apply Finset.sum_eq_zero
  intro v hv
  have he : finiteTupleProduct v=J := (Finset.mem_filter.mp hv).2
  have hc : ¬IsCoprime (finiteTupleProduct v) r.R := he ▸ hcop
  unfold MixedOriginalSecondZero.originalTuple profileCoefficient
  simp only [hc,ite_false,mul_zero,zero_mul]

def coloredSectorFixedHeight (r : Source ι a b) (ha : 0<a)
    (ω₁ ω₂ : Id→ℂ) (D : FixedCubeDatum) (G : Id) (hG : Supported G) (L : Id) (v : ℝ) : ℂ :=
  ∑I : sectorPool G hG.1 (sourceColumns r),
    (if L∣(I:Id) then TwistedRawSource.sourceColumn r ha ω₁ ω₂ 1 (G*I) else 0)*heightCoeff D.row.χ v I

/-- Completion at the actual colored source, using the full original column
pool. Old uncolored active-column cancellations are not assumed to survive. -/
theorem colored_nativeGaussArm_eq_fixedCoefficient (r : Source ι a b) (ha : 0<a)
    (ω₁ ω₂ : Id→ℂ) (D : FixedCubeDatum) (η : Character) (χ : RayCharacter)
    (hη : D.η=childCharacter η χ) (hm : D.m=nativeSourceMask r)
    (t : ℝ) (G : Id) (hG : Supported G) (L : Id)
    (I : sectorPool G hG.1 (sourceColumns r)) :
    nativeGaussArm η t (sourceColumns r) (TwistedRawSource.sourceColumn r ha ω₁ ω₂ 1) G hG L χ D.A D.z I=
      if L∣(I:Id) then TwistedRawSource.sourceColumn r ha ω₁ ω₂ 1 (G*I)*
        (Ideal.absNorm (I:Id):ℂ)^(Complex.I*t)*D.actualCoefficient I else 0 := by
  by_cases hβ : TwistedRawSource.sourceColumn r ha ω₁ ω₂ 1 (G*I)=0
  · simp only [nativeGaussArm,divisorCoefficient,movingCoefficient,hβ,zero_mul,ite_self]
  · apply nativeGaussArm_eq_fixedCoefficient D η χ hη t _ _ G hG L I
    rw [hm]
    exact supported_coprime_nativeSourceMask r I (sectorPool_supported G hG.1 _ I)
      ((coloredSourceColumn_coprime r ha ω₁ ω₂ 1 (G*I) hβ).of_isCoprime_of_dvd_left (dvd_mul_left _ _))

/-- Actual colored second fixed Gauss arm, before any allocation estimates. -/
theorem colored_nativeGaussArm_window_integral (r : Source ι a b) (ha : 0<a)
    (ω₁ ω₂ : Id→ℂ) (D : FixedCubeDatum) (η : Character) (χ : RayCharacter)
    (hη : D.η=childCharacter η χ) (hm : D.m=nativeSourceMask r)
    (G : Id) (hG : Supported G) (L : Id) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ→ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) :
    (∑I : sectorPool G hG.1 (sourceColumns r),
      nativeGaussArm η t (sourceColumns r) (TwistedRawSource.sourceColumn r ha ω₁ ω₂ 1)
        G hG L χ D.A D.z I*columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ)=
    ∫w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      coloredSectorFixedHeight r ha ω₁ ω₂ D G hG L (t+2*Real.pi*(w-θ)) := by
  let c (I : sectorPool G hG.1 (sourceColumns r)) : ℂ :=
    if L∣(I:Id) then TwistedRawSource.sourceColumn r ha ω₁ ω₂ 1 (G*I) else 0
  have he (I : sectorPool G hG.1 (sourceColumns r)) :
      nativeGaussArm η t (sourceColumns r) (TwistedRawSource.sourceColumn r ha ω₁ ω₂ 1)
        G hG L χ D.A D.z I=c I*heightCoeff D.row.χ t I := by
    rw [colored_nativeGaussArm_eq_fixedCoefficient r ha ω₁ ω₂ D η χ hη hm t G hG L I]
    simp only [c,heightCoeff,D.row_spec.2.2.2]
    split_ifs <;> ring
  simp_rw [he]
  have hi (I : sectorPool G hG.1 (sourceColumns r)) :
      Integrable (fun w : ℝ=>c I*(columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff D.row.χ (t+2*Real.pi*(w-θ)) I)) :=
    (height_column_integrable V hVc hVs D.row.χ I
      (sectorPool_supported G hG.1 _ I).1 t θ X hX).const_mul _
  calc
    _ = ∑I : sectorPool G hG.1 (sourceColumns r),∫w : ℝ,
        c I*(columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
          heightCoeff D.row.χ (t+2*Real.pi*(w-θ)) I) := by
      apply Finset.sum_congr rfl
      intro I _
      rw [integral_const_mul,←height_column_integral V hVc hVs D.row.χ I
        (sectorPool_supported G hG.1 _ I).1 t θ X hX]
      ring
    _ = _ := by
      rw [←integral_finsetSum _ (fun I _=>hi I)]
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [coloredSectorFixedHeight,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      dsimp only [c]
      ring

#print axioms coloredSourceColumn_coprime
#print axioms colored_nativeGaussArm_eq_fixedCoefficient
#print axioms colored_nativeGaussArm_window_integral
end
end QRH.Cycle092.FixedCubeGauss
