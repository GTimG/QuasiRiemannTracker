/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual pre-payment HIGH retains the complete first common value for coupled
independent-density cones; only channels2,3,4 price the schedule. -/
import Submissions.hailey_collet_1252270103.Record12518109Natural.HighPaidGeometry

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Record12518109Natural
noncomputable section
open scoped Classical BigOperators
open Record12518109Gain HighAdmission LocalMoment
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentSectorLocalization CenteredMomentAmplificationChildInput CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonical Cycle61Moment Cycle61InitialMass Cycle61HighGeometry Cycle61FinalCapacity
open CenteredMomentCommonRadialData CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O
theorem actual_high_joint_relative_valuation (reflected second : Bool)
    (l : FirstSourceLabel) (hC : Supported l.1.1) (hD : Supported l.1.2)
    (C2 D2 : Ideal O) (hC2 : Supported C2) (hD2 : Supported D2)
    (heq2 : primeSupport C2=primeSupport D2) (U : Finset (CommonIndex C2 D2))
    (Z delta M A a commonBound : ℝ) (hZ : 1<Z)
    (hfirst : labelFirstCommon reflected l Z delta-labelSurplus reflected l Z≤
      commonBound) :
    highJointExcess M A a delta
      (labelC reflected l Z) (labelD reflected l Z) (labelP l Z) (labelR l Z) (labelE l Z)
      (max (3*labelC reflected l Z-5*labelD reflected l Z-labelR l Z) 0/6)
      (Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ))
      (Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ))
      (Real.logb Z ((if second then D2 else C2).absNorm:ℝ))
      (Real.logb Z (normValue (commonFrequencyGenerator C2 D2)))
      (Real.logb Z ((∏P∈U,P.val).absNorm:ℝ))-labelSurplus reflected l Z≤
      M*(unmarkedDensity delta-1)+delta*A+a*(5-6*unmarkedDensity delta)+commonBound-delta*Real.logb Z ((if second then D2 else C2).absNorm:ℝ) := by
  have hg2 : Real.logb Z (normValue (commonFrequencyGenerator C2 D2))≤
      Real.logb Z ((if second then D2 else C2).absNorm:ℝ) := by
    apply Real.logb_le_logb_of_le hZ
      (normValue_pos _ (commonFrequencyGenerator_ne_zero C2 D2 hC2))
    cases second
    · exact actual_common_norm_le C2 D2 hC2 hD2 heq2
    · exact actual_common_norm_le_right C2 D2 hC2 hD2 heq2
  have ht2 := Cycle61FinalCapacity.actual_unit_log_nonneg C2 D2 hC2 U Z hZ
  dsimp [highJointExcess,labelFirstCommon,Valuation.firstCommon] at *
  linarith

/-- Literal first-label and second-child coordinates, with physical orientation
left=!reflected throughout. No historical rho<=.4 estimate is used. -/
theorem actual_high_coordinate_relative_payment (reflected second : Bool)
    (l : FirstSourceLabel) (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C2 D2 : Ideal O) (hC2 : Supported C2) (hD2 : Supported D2)
    (heq2 : primeSupport C2=primeSupport D2) (U : Finset (CommonIndex C2 D2))
    (Z delta M A a xi reserve err commonBound : ℝ) (hZ : 1<Z)
    (hfirst : labelFirstCommon reflected l Z delta-labelSurplus reflected l Z≤
      commonBound) :
    highExponentValue delta
      (actualHighCoordinates reflected (!reflected) second l C2 D2 U Z M A a xi reserve err)≤
      labelSide reflected l Z A+labelSurplus reflected l Z+
        (1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err-
        (M*(1-unmarkedDensity delta)-delta*A-a*(5-6*unmarkedDensity delta))+commonBound-delta*Real.logb Z ((if second then D2 else C2).absNorm:ℝ) := by
  have hid := actual_high_coordinate_excess_identity
    reflected (!reflected) second l hC hD heq C2 D2 hC2 hD2 heq2 U Z delta M A a xi reserve err hZ
  have hh := actual_high_joint_relative_valuation reflected second l hC hD C2 D2 hC2 hD2 heq2
    U Z delta M A a commonBound hZ hfirst
  dsimp only at hid
  dsimp [labelC,labelD,labelR,labelE,labelP,labelSide] at hh ⊢
  rw [hid]
  linarith

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
theorem actual_geometry_relative_high_payment
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (D A a reserve err errv delta commonBound : ℝ) (hZ : 1<Z)
    (hfirst : labelFirstCommon reflected (geometryFirstLabel s R seed K Z xi hK bin j) Z delta-
      labelSurplus reflected (geometryFirstLabel s R seed K Z xi hK bin j) Z≤
      commonBound) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let side:=balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z D A a xi reserve err) errv) side
    highExponentValue delta x≤
      (1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err+errv-
        (D*(1-unmarkedDensity delta)-delta*A-a*(5-6*unmarkedDensity delta))+commonBound-delta*Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ) := by
  intro l side x
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z xi hK bin j.1).hC
  have hD : Supported l.1.2 := (geometryFirstSource s R seed K Z xi hK bin j.1).hD
  have heq : primeSupport l.1.1=primeSupport l.1.2 :=
    (geometryFirstSource s R seed K Z xi hK bin j.1).sameSupport
  have hh := actual_high_coordinate_relative_payment reflected second l hC hD heq
    d2.C d2.D d2.hC d2.hD d2.sameSupport U Z delta D A a xi reserve err commonBound hZ hfirst
  have he := actual_geometry_high_side_identity s R seed K Z xi hK bin j reflected A
  have hside := balanced_geometry_side_eq s R seed K Z xi hK bin j reflected A
  change side=geometryHighSide reflected A (geometryExponents s R seed K Z xi j.1.val)+
    labelSurplus reflected l Z at hside
  change geometryHighSide reflected A (geometryExponents s R seed K Z xi j.1.val)=labelSide reflected l Z A at he
  rw [he] at hside
  rw [←hside] at hh
  dsimp only [x]
  rw [compensated_high_exponent,child_high_exponent_value]
  linarith only [hh]


/-- Three genuine gain channels price the source target, while the full
relative common term remains available to the paired or mixed cone. -/
theorem actual_geometry_three_channel_prepaid
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (D A a reserve err errv ν T amp S F live : ℝ) (hZ : 1<Z)
    (hνlo : 31/50≤ν) (hνhi : ν≤3/4) (hD : 0≤D)
    (hA : A≤D*T) (ha : a≤D*amp)
    (hregular : ∀k : Fin 3,0<Record12518109Admission.regular T amp S F ν (k.val+2)) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z D A a xi reserve err) errv)
      (balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val))
    highExponentValue ν x-gain ν live (x 2)≤
      (1-unmarkedDensity ν)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity ν*err+errv-
        D*Record12518109Admission.highFee+
        (labelFirstCommon reflected l Z ν-labelSurplus reflected l Z+labelE l Z+
          D*gain ν S F-ν*Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)-gain ν live (x 2)) := by
  intro l x
  have hsource:=actual_geometry_relative_high_payment s R seed K Z xi hK bin j d2 reflected second U
    D A a reserve err errv ν (labelFirstCommon reflected l Z ν-labelSurplus reflected l Z) hZ (le_refl _)
  change highExponentValue ν x≤_ at hsource
  have hν : 0≤ν:=by linarith
  have hr:=Valuation.rho_extended_range (show (405/662:ℝ)≤ν by linarith) hνhi
  have hr' : unmarkedDensity ν≤23/50:=hr.2
  have hAm:=mul_le_mul_of_nonneg_left hA hν
  have ham:=mul_le_mul_of_nonneg_right ha (show 0≤5-6*unmarkedDensity ν by linarith [hr'])
  have hb : highExponentValue ν x≤
      (1-unmarkedDensity ν)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity ν*err+errv-
        D*baseMargin T amp ν+labelFirstCommon reflected l Z ν-labelSurplus reflected l Z-
          ν*Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ) := by
    dsimp only [baseMargin]
    change _≤_-D*(1-ν*T-5*amp-unmarkedDensity ν*(1-6*amp))+_-_-_
    nlinarith only [hsource,hAm,ham]
  have hprice:=regular_gain_payment T amp S F ν hνlo hνhi (hregular 0) (hregular 1) (hregular 2)
  have hp : Record12518109Admission.highFee≤baseMargin T amp ν+gain ν S F:=by
    dsimp only [baseMargin]
    linarith only [hprice]
  have hscaled:=mul_le_mul_of_nonneg_left hp hD
  have hC : Supported l.1.1:=(geometryFirstSource s R seed K Z xi hK bin j.1).hC
  have hE : 0≤labelE l Z:=by
    apply Real.logb_nonneg hZ
    have hh : 1≤(∏P∈l.2.val,P.val).absNorm:=firstCommonSubsetNorm_pos l.1.1 l.1.2 hC l.2.val
    exact_mod_cast hh
  linarith only [hb,hscaled,hE]

end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.actual_geometry_relative_high_payment

#print axioms OAI.SevenEighths.Record12518109Natural.actual_geometry_three_channel_prepaid
