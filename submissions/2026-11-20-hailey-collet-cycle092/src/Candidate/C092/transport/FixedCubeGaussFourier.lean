/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Remove the entire native column window before allocation/H8. -/
import Candidate.C092.transport.FixedCubeGaussMask

set_option autoImplicit false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion FourierBridge
open CenteredMomentSecondSectorColumns CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentSmooth QRH.Cycle092.SignedCenter
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def sectorFixedHeight (r : Source ι a b) (ha : 0<a) (D : FixedCubeDatum)
    (G : Id) (hG : Supported G) (L : Id) (v : ℝ) : ℂ :=
  ∑ I : sectorPool G hG.1 (Second.Concrete.S0 r ha),
    (if L∣(I:Id) then sourceCoefficient r ha 1 (G*I) else 0)*heightCoeff D.row.χ v I

/-- Full Fourier inversion of the actual native column window. The shift is
`t + 2*pi*(w-theta)` and the scale phase remains outside the signed source. -/
theorem source_nativeGaussArm_window_integral (r : Source ι a b) (ha : 0<a)
    (D : FixedCubeDatum) (η : Character) (χ : RayCharacter)
    (hη : D.η=childCharacter η χ) (hm : D.m=nativeSourceMask r)
    (G : Id) (hG : Supported G) (L : Id) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ→ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) :
    (∑ I : sectorPool G hG.1 (Second.Concrete.S0 r ha),
      nativeGaussArm η t (Second.Concrete.S0 r ha) (sourceCoefficient r ha 1)
        G hG L χ D.A D.z I*
      columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ)=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        sectorFixedHeight r ha D G hG L (t+2*Real.pi*(w-θ)) := by
  let c (I : sectorPool G hG.1 (Second.Concrete.S0 r ha)) : ℂ :=
    if L∣(I:Id) then sourceCoefficient r ha 1 (G*I) else 0
  have he (I : sectorPool G hG.1 (Second.Concrete.S0 r ha)) :
      nativeGaussArm η t (Second.Concrete.S0 r ha) (sourceCoefficient r ha 1)
        G hG L χ D.A D.z I=c I*heightCoeff D.row.χ t I := by
    rw [source_nativeGaussArm_eq_fixedCoefficient r ha D η χ hη hm t G hG L I]
    simp only [c,heightCoeff,D.row_spec.2.2.2]
    split_ifs <;> ring
  simp_rw [he]
  have hi (I : sectorPool G hG.1 (Second.Concrete.S0 r ha)) :
      Integrable (fun w : ℝ=>c I*(columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff D.row.χ (t+2*Real.pi*(w-θ)) I)) :=
    (height_column_integrable V hVc hVs D.row.χ I
      (sectorPool_supported G hG.1 _ I).1 t θ X hX).const_mul _
  calc
    _ = ∑ I : sectorPool G hG.1 (Second.Concrete.S0 r ha),∫ w : ℝ,
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
      simp only [sectorFixedHeight,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      dsimp only [c]
      ring

#print axioms source_nativeGaussArm_window_integral
end
end QRH.Cycle092.FixedCubeGauss
