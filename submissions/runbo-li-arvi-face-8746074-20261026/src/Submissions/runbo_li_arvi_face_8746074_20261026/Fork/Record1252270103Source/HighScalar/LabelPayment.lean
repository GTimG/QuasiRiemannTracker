/- Repeated marks: fork of Record1252270103Source.HighScalar.LabelPayment (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.HighScalar.LabelPayment
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.GainC
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.CountWrappersK
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.GainPaymentK
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.PaymentWrappersK
import Submissions.runbo_li_arvi_face_8746074_20261026.Source.WitnessWrappersK
import Submissions.runbo_li_arvi_face_8746074_20261026.Finite.SourceValid2
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual signed labels, exact child coordinates, and the source scalar reserve. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.HighScalar
noncomputable section
open OAI OAI.SevenEighths
open Record12518109Natural Record1252270103CommonGeometry Cycle61HighGeometry Cycle61InitialMass
open Record1252270103Finite PhysicalScalar LocalMoment JointHigh
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization
open CenteredMomentRankinRadical CanonicalQuadraticSieve Cycle61Moment
local notation "O" => ActualEisensteinCubic.O
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The only geometric scalar premises are the actual volume/amplifier caps
and the live/frozen width ledger. No high-exponent conclusion is assumed.
The optional forced width is charged to the ordinary amplitude explicitly. -/
theorem first_label_retained_payment_rm (n low : Source) (high : Option Source)
    (hp : GainParameters high) (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2)
    (hbC : ValuationAtMostTwo l.1.1) (hbD : ValuationAtMostTwo l.1.2)
    (d2 : SecondInputDatum α) (U : Finset (CommonIndex d2.C d2.D))
    (Z D A amp ξ reserveGeom err errv ν b live forced reserve : ℝ)
    (hZ : 1<Z) (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hD0 : 0≤D)
    (hforced : 0≤forced) (hA : A≤D*(sourceTReal n b+b))
    (hamp : amp≤D*sourceAReal n low b) (hg : ActualGaps_rm n low high b ν reserve) :
    let x:=childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U
        Z D A amp ξ reserveGeom err) errv
    D*(b-2*(n.allowance:ℝ))≤live+labelC reflected l Z+
      Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)+forced →
    D*(sourceFReal n low b-(n.allowance:ℝ))≤x 2+2*labelC reflected l Z+
      2*Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ) →
    retainedHighExponent ν (gainAt_rm high ν live) x-ν*forced≤
      labelSide reflected l Z A+labelSurplus reflected l Z+
        ((1-unmarkedDensity ν)*(frequencyLoss Z 32 ξ+reserveGeom)+
          unmarkedDensity ν*err+errv)-D*((n.highFee:ℝ)+reserve) := by
  intro x hslots hrows
  have hr:=local_rho_bounds hν0 hν1
  have hcmt:=first_label_common_price reflected l hC hD heq hbC hbD Z ν
    (unmarkedDensity ν) hZ hr.1 (by linarith [hr.2])
  have hcmt' : labelFirstCommon reflected l Z ν-labelSurplus reflected l Z≤
      -ν*labelC reflected l Z := hcmt
  have hraw:=actual_high_coordinate_relative_payment reflected second l hC hD heq
    d2.C d2.D d2.hC d2.hD d2.sameSupport U Z ν D A amp ξ reserveGeom err
    (-ν*labelC reflected l Z) hZ hcmt'
  have hc : 0≤labelC reflected l Z := by
    apply Real.logb_nonneg hZ
    cases reflected
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hd : 0≤Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    cases second
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr d2.hC.1)
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr d2.hD.1)
  have hAm:=mul_le_mul_of_nonneg_left hA (show 0≤ν by linarith)
  have hampm:=mul_le_mul_of_nonneg_right hamp (show 0≤5-6*unmarkedDensity ν by linarith [hr.2])
  have he : High.rho ν=unmarkedDensity ν := High.rho_eq_original ν
  have hbase : -(D*(1-unmarkedDensity ν)-ν*A-amp*(5-6*unmarkedDensity ν))≤
      D*(sourceBase n low b ν-1) := by
    dsimp only [sourceBase,physicalBase]
    rw [he]
    nlinarith only [hAm,hampm]
  have hpaid:=actual_gap_gain_payment_rm n low high hp b ν reserve D live (x 2)
    (labelC reflected l Z) (Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)) forced
    hν0 hν1 hD0 hc hd hforced hg hslots hrows
  dsimp only [retainedHighExponent]
  have hx : highExponentValue ν x=
      highExponentValue ν (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U
        Z D A amp ξ reserveGeom err)+errv := child_high_exponent_value _ _ _
  rw [hx]
  nlinarith only [hraw,hbase,hpaid]

end
end QRH.Record1252270103Source.HighScalar
