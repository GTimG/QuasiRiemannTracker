/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
LOW coordinate payment for actual marked modified first columns. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalLowPayment
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstFamilyGeometry
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentCommonRadialData CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization
open Cycle61HighGeometry Cycle61InitialMass Cycle61Moment
open Record12518109Natural Record1252270103CommonGeometry
open HighScalar Admission Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O
variable {ι:Type}[Fintype ι][DecidableEq ι]

theorem actual_low_raw_radius (reflected second:Bool)(l:FirstSourceLabel)
    (hC:Supported l.1.1)(hD:Supported l.1.2)
    (heq:primeSupport l.1.1=primeSupport l.1.2)
    (hbC:ValuationAtMostTwo l.1.1)(hbD:ValuationAtMostTwo l.1.2)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(Z M A a ξ reserve err errv:ℝ):
    (childHighCoordinates (actualHighCoordinates reflected (!reflected) second l C D U
      Z M A a ξ reserve err) errv) 2=
      M-6*a-(frequencyLoss Z 32 ξ+reserve)+err-
        max (labelD reflected l Z-labelC reflected l Z) 0 := by
  have h:=first_source_raw_exponent (!reflected) l hC hD heq hbC hbD Z
    (M-6*a-(frequencyLoss Z 32 ξ+reserve)+err)
  cases reflected <;>
    dsimp [childHighCoordinates,actualHighCoordinates,labelC,labelD,normLog] at h ⊢ <;>
    linarith only [h]

theorem modified_low_coordinate_payment (s:Input ι)(A₁ A₂ Dmark Kmark R seed:Ideal O)
    (Fmark:Ideal O→ℂ)(H Z ξ:ℝ)(hH:0<H)(bin:ℤ×(Fin 5→ℤ))
    (j:FirstColumnIndex (CoupledFirst.geometryFirstSource s
      (markedSourceModifier A₁ A₂ Dmark Kmark Fmark) R seed H Z ξ hH bin))
    (reflected second:Bool)(d₂:SecondInputDatum ι)(U:Finset (CommonIndex d₂.C d₂.D))
    (M A a reserve err errv q B lam h F t b c f loss rho mesh erased g radial radialRound:ℝ)
    (hZ:1<Z)(hq:0≤q)(hB0:0≤B)(hB:B≤1)(hlam:1<lam):
    let l:=FirstFamily.firstLabel s (markedSourceModifier A₁ A₂ Dmark Kmark Fmark) R seed H Z ξ hH bin j
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l d₂.C d₂.D U
      Z M A a ξ reserve err) errv
    labelC reflected l Z≤c→0≤f→0≤h→q*h≤1→
    g=a-q*(b+(t-B*F)/lam)→(B*F-t)/lam≤h*F→0≤loss→0≤rho→
    erased≤max 0 (max
      (b-f-(B*(F-max (labelD reflected l Z-labelC reflected l Z) 0-rho)-(t-c+f+loss))/lam)
      (b-f-h*(F-max (labelD reflected l Z-labelC reflected l Z) 0-rho)))+mesh→
    radial≤x 2+radialRound→
    x 0+x 1+radial-
      balancedGeometrySide reflected A (CoupledFirst.geometryExponents s
        (markedSourceModifier A₁ A₂ Dmark Kmark Fmark) R seed H Z ξ j.1.val)+q*erased≤
      -min a g+q*(max ((B*rho+loss)/lam) (h*rho)+mesh)+err+errv+radialRound := by
  intro l x hc hf hh hqh hgap hcap hloss hrho herased hrad
  have hl:=FirstFamily.label_supported s (markedSourceModifier A₁ A₂ Dmark Kmark Fmark) R seed H Z ξ hH bin j
  obtain ⟨hbC,hbD⟩:=modified_first_label_valuations s A₁ A₂ Dmark Kmark R seed Fmark H Z ξ hH bin j
  have hp:=actual_low_coordinate_payment reflected second l hl.1 hl.2.1 hl.2.2 hbC hbD
    d₂.C d₂.D d₂.hC d₂.hD d₂.sameSupport U Z M A a ξ reserve err errv q B lam h F t b c f loss rho mesh erased g radial radialRound
    hZ hq hB0 hB hlam hc hf hh hqh hgap hcap hloss hrho herased hrad
  have hside:=modified_balanced_side s (markedSourceModifier A₁ A₂ Dmark Kmark Fmark) R seed H Z ξ hH bin j reflected A
  change balancedGeometrySide reflected A _=labelSide reflected l Z A+labelSurplus reflected l Z at hside
  rw [hside]
  convert hp using 1 <;> ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_low_raw_radius
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_low_coordinate_payment
