/- Repeated marks: fork of Record1252270103Source.HighScalar.NonregularModified (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.HighScalar.NonregularModified
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.GainC
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.CountWrappersK
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.GainPaymentK
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.PaymentWrappersK
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.WitnessWrappersK
import Submissions.runbo_li_arvi_face_8746074_20261026.Finite.SourceValid2
import Submissions.runbo_li_arvi_face_8746074_20261026.Fork.Record1252270103Source.HighScalar.NonregularLabels
import Submissions.runbo_li_arvi_face_8746074_20261026.Fork.Record1252270103Source.HighScalar.ModifiedPayment
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal fixed/tiny HIGH payment for the actual marked modified source. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.HighScalar
noncomputable section
open OAI OAI.SevenEighths Record12518109Natural Record1252270103CommonGeometry
open Cycle61HighGeometry Cycle61InitialMass JointHigh LocalMoment
open Record1252270103Finite PhysicalScalar CanonicalQuadraticSieve HeckeFamily
open CenteredMomentCommonRadialData CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondCanonical CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization CenteredMomentRankinRadical Cycle61Moment
open Record1252270103Source.Collision Admission
local notation "O" => HeckeFamily.O
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Both marked and plain projectors are retained in the source coordinate.
The actual frequency ledger is proved from the amplifier and rounding caps;
the full live width remains at most the original slot budget. Tiny rows
also retain the literal raw-frequency cap D/50. -/
theorem nonregular_modified_retained_high_exponent_rm (n low : Source) (high : Option Source)
    (sector : HighSector) (hsector : sector≠.regular) (s : Input ι) (A₁ A₂ Dmark Kmark R seed : Ideal O)
    (F : Ideal O→ℂ) (H Z ξ : ℝ) (hH : 0<H) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (High.CoupledFirst.geometryFirstSource s
      (markedSourceModifier A₁ A₂ Dmark Kmark F) R seed H Z ξ hH key))
    (reflected second : Bool) (d2 : SecondInputDatum ι) (U : Finset (CommonIndex d2.C d2.D))
    (D A amp reserveGeom err errv ν b live forced reserve : ℝ)
    (hZ : 1<Z) (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hD0 : 0≤D)
    (hforced : 0≤forced) (hA : A≤D*(sourceTReal n b+b))
    (hamp : amp≤D*sourceAReal n low b)
    (hOmega : frequencyLoss Z 32 ξ+reserveGeom≤D*(n.allowance:ℝ)) (herr : 0≤err)
    (hlive : live≤D*b) (hg : ActualGaps_rm n low high b ν reserve) :
    let l:=FirstFamily.firstLabel s (markedSourceModifier A₁ A₂ Dmark Kmark F) R seed H Z ξ hH key j
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U
      Z D A amp ξ reserveGeom err) errv
    let side:=balancedGeometrySide reflected A
      (High.CoupledFirst.geometryExponents s (markedSourceModifier A₁ A₂ Dmark Kmark F) R seed H Z ξ j.1.val)
    0≤x 2 → (sector=.tiny →x 2≤D/50) →
    retainedHighExponent ν (sectorSharpGain sector ν live (D/50)) x-ν*forced≤side+
      ((1-unmarkedDensity ν)*(frequencyLoss Z 32 ξ+reserveGeom)+unmarkedDensity ν*err+errv)-
      D*((n.highFee:ℝ)+reserve) := by
  intro l x side hq htiny
  let src:=High.CoupledFirst.geometryFirstSource s (markedSourceModifier A₁ A₂ Dmark Kmark F)
    R seed H Z ξ hH key j.1
  have hC : Supported l.1.1:=src.hC
  have hD : Supported l.1.2:=src.hD
  have heq : CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2:=src.sameSupport
  obtain ⟨hbC,hbD⟩:=modified_first_label_valuations s A₁ A₂ Dmark Kmark R seed F H Z ξ hH key j
  have hfreq:=actual_label_frequency_lower n low b reflected second l hC hD d2 U
    Z D A amp ξ reserveGeom err errv hZ hamp hOmega herr
  have hpaid:=nonregular_label_retained_payment_rm n low high sector hsector reflected second l hC hD heq hbC hbD
    d2 U Z D A amp ξ reserveGeom err errv ν b live forced reserve
    hZ hν0 hν1 hD0 hforced hA hamp hlive hg hq htiny hfreq
  have hs:=modified_balanced_side s (markedSourceModifier A₁ A₂ Dmark Kmark F)
    R seed H Z ξ hH key j reflected A
  change side=labelSide reflected l Z A+labelSurplus reflected l Z at hs
  rw [←hs] at hpaid
  exact hpaid

end
end QRH.Record1252270103Source.HighScalar
