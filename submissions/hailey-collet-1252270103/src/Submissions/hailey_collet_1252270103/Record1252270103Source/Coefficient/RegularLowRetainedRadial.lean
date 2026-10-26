/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The LOW radial exponent is the literal retained-frequency coordinate once
the actual Fourier loss and reserve are paid. Both first orientations remain. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.HighScalar.ModifiedGeometry
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstFamilyGeometry
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceWidth
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularLowRetainedRadial
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentAmplificationChildInput
open Cycle61Moment Cycle61InitialMass Cycle61HighGeometry
open Record12518109Natural Record1252270103CommonGeometry
open Record1252270103Finite QRH.Record1252270103Source.Admission
open Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O

theorem label_radial_coordinate (reflected second:Bool) (l:FirstSourceLabel)
    (hC:Supported l.1.1) (hD:Supported l.1.2)
    (heq:primeSupport l.1.1=primeSupport l.1.2)
    (hbC:ValuationAtMostTwo l.1.1) (hbD:ValuationAtMostTwo l.1.2)
    (C₂ D₂:Ideal O) (U:Finset (CommonIndex C₂ D₂))
    (Z M A amp ξ reserve err errv:ℝ) :
    childHighCoordinates (actualHighCoordinates reflected (!reflected) second l C₂ D₂ U
      Z M A amp ξ reserve err) errv 2 =
      M-6*amp-max (labelD reflected l Z-labelC reflected l Z) 0-
        (frequencyLoss Z 32 ξ+reserve)+err := by
  have h:=first_source_raw_exponent (!reflected) l hC hD heq hbC hbD Z M
  cases reflected <;>
    simp [childHighCoordinates,actualHighCoordinates,labelC,labelD,normLog] at h ⊢ <;>
    linarith only [h]

theorem modified_deficit_and_coordinate {α:Type} [Fintype α] [DecidableEq α]
    (n low:Source) (b:ℝ) (s:Input α) (A₁ A₂ D K R seed:Ideal O)
    (F:Ideal O→ℂ) (H Z ξ:ℝ) (hH:0<H) (hZ:1<Z)
    (bin:ℤ×(Fin 5→ℤ))
    (j:FirstColumnIndex (High.CoupledFirst.geometryFirstSource s
      (markedSourceModifier A₁ A₂ D K F) R seed H Z ξ hH bin))
    (reflected second:Bool) (C₂ D₂:Ideal O) (U:Finset (CommonIndex C₂ D₂))
    (A reserve err errv:ℝ) :
    let l:=FirstFamily.firstLabel s (markedSourceModifier A₁ A₂ D K F) R seed H Z ξ hH bin j
    let delta:=max (labelD reflected l Z-labelC reflected l Z) 0
    let rho:=frequencyLoss Z 32 ξ+reserve-err
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l C₂ D₂ U
      Z 1 A (sourceAReal n low b) ξ reserve err) errv
    delta≤labelC reflected l Z ∧ x 2=sourceFReal n low b-delta-rho := by
  intro l delta rho x
  have hs:=FirstFamily.label_supported s (markedSourceModifier A₁ A₂ D K F) R seed H Z ξ hH bin j
  have hv:=HighScalar.modified_first_label_valuations s A₁ A₂ D K R seed F H Z ξ hH bin j
  have hd:=first_source_deficit_bounds (!reflected) l hs.1 hs.2.1 hs.2.2 hv.1 hv.2 Z hZ
  refine ⟨?_,?_⟩
  · cases reflected <;> simpa [delta,labelC,labelD,normLog] using hd.1
  · have he:=label_radial_coordinate reflected second l hs.1 hs.2.1 hs.2.2 hv.1 hv.2
      C₂ D₂ U Z 1 A (sourceAReal n low b) ξ reserve err errv
    dsimp only [x,delta,rho,sourceFReal]
    rw [he]
    ring

/-- These are the precise two-sided reserve conditions. In particular a
larger rho cannot be chosen independently of the retained row radius. -/
theorem rho_bounds (Z ξ reserve err allowance:ℝ) (hZ:1<Z) (hξ:0≤ξ)
    (hreserve:err≤reserve)
    (hupper:frequencyLoss Z 32 ξ+reserve≤allowance/4+err) :
    0≤frequencyLoss Z 32 ξ+reserve-err ∧
      frequencyLoss Z 32 ξ+reserve-err≤allowance/4 := by
  have hω:=frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ
  constructor <;> linarith

end
end QRH.Record1252270103Source.RegularLowRetainedRadial
#print axioms QRH.Record1252270103Source.RegularLowRetainedRadial.label_radial_coordinate
#print axioms QRH.Record1252270103Source.RegularLowRetainedRadial.modified_deficit_and_coordinate
#print axioms QRH.Record1252270103Source.RegularLowRetainedRadial.rho_bounds
