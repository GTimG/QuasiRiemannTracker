/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal regular HIGH payment for the actual marked modified source. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.HighScalar.ModifiedGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.HighScalar.Frequency
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

lemma gainParameters_of_sourceValid (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) : GainParameters high := by
  intro h hh
  obtain ⟨hB,hB',hL,hcap,hcap'⟩:=hv.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  refine ⟨?_,?_,?_,?_,?_⟩
  · have hh:=(Rat.cast_le (K:=ℝ)).mpr hB
    norm_num at hh ⊢
    exact hh
  · exact_mod_cast hB'
  · exact_mod_cast hL
  · exact_mod_cast hcap
  · exact_mod_cast hcap'.le

/-- Both marked and plain projectors are retained in the source coordinate.
The actual frequency ledger is proved from the amplifier and rounding caps;
only the literal surviving-slot conservation ledger is supplied. -/
theorem modified_retained_high_exponent (n low : Source) (high : Option Source)
    (hp : GainParameters high) (s : Input ι) (A₁ A₂ Dmark Kmark R seed : Ideal O)
    (F : Ideal O→ℂ) (H Z ξ : ℝ) (hH : 0<H) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (High.CoupledFirst.geometryFirstSource s
      (markedSourceModifier A₁ A₂ Dmark Kmark F) R seed H Z ξ hH key))
    (reflected second : Bool) (d2 : SecondInputDatum ι) (U : Finset (CommonIndex d2.C d2.D))
    (D A amp reserveGeom err errv ν b live forced reserve : ℝ)
    (hZ : 1<Z) (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hD0 : 0≤D)
    (hforced : 0≤forced) (hA : A≤D*(sourceTReal n b+b))
    (hamp : amp≤D*sourceAReal n low b)
    (hOmega : frequencyLoss Z 32 ξ+reserveGeom≤D*(n.allowance:ℝ)) (herr : 0≤err)
    (hg : ActualGaps n low high b ν reserve) :
    let l:=FirstFamily.firstLabel s (markedSourceModifier A₁ A₂ Dmark Kmark F) R seed H Z ξ hH key j
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U
      Z D A amp ξ reserveGeom err) errv
    let side:=balancedGeometrySide reflected A
      (High.CoupledFirst.geometryExponents s (markedSourceModifier A₁ A₂ Dmark Kmark F) R seed H Z ξ j.1.val)
    D*(b-2*(n.allowance:ℝ))≤live+labelC reflected l Z+
      Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)+forced →
    retainedHighExponent ν (gainAt high ν live) x-ν*forced≤side+
      ((1-unmarkedDensity ν)*(frequencyLoss Z 32 ξ+reserveGeom)+unmarkedDensity ν*err+errv)-
      D*((n.highFee:ℝ)+reserve)-
      (labelC reflected l Z+Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)+forced)/12 := by
  intro l x side hslots
  let src:=High.CoupledFirst.geometryFirstSource s (markedSourceModifier A₁ A₂ Dmark Kmark F)
    R seed H Z ξ hH key j.1
  have hC : Supported l.1.1:=src.hC
  have hD : Supported l.1.2:=src.hD
  have heq : CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2:=src.sameSupport
  obtain ⟨hbC,hbD⟩:=modified_first_label_valuations s A₁ A₂ Dmark Kmark R seed F H Z ξ hH key j
  have hfreq:=actual_label_frequency_lower n low b reflected second l hC hD d2 U
    Z D A amp ξ reserveGeom err errv hZ hamp hOmega herr
  have hpaid:=first_label_retained_payment n low high hp reflected second l hC hD heq hbC hbD
    d2 U Z D A amp ξ reserveGeom err errv ν b live forced reserve
    hZ hν0 hν1 hD0 hforced hA hamp hg hslots hfreq
  have hs:=modified_balanced_side s (markedSourceModifier A₁ A₂ Dmark Kmark F)
    R seed H Z ξ hH key j reflected A
  change side=labelSide reflected l Z A+labelSurplus reflected l Z at hs
  rw [←hs] at hpaid
  exact hpaid

end
end QRH.Record1252270103Source.HighScalar
#print axioms QRH.Record1252270103Source.HighScalar.gainParameters_of_sourceValid
#print axioms QRH.Record1252270103Source.HighScalar.modified_retained_high_exponent
