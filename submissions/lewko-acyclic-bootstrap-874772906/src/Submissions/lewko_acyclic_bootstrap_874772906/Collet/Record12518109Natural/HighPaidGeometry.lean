/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal compensated two-allocation geometry and all five certified ordinary
HIGH channels. No physical moment estimate is assumed. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.HighActualAllocation
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.GainAllocation

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Record12518109Natural
noncomputable section
open scoped Classical BigOperators
open Record12518109Gain HighAdmission LocalMoment
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentSectorLocalization CenteredMomentAmplificationChildInput
open Cycle61Moment Cycle61InitialMass
local notation "O" => HeckeFamily.O

lemma regular_joint_admission (T amp S F ν : ℝ) (hνlo : 31/50≤ν) (hνhi : ν≤3/4)
    (hregular : ∀j : Fin 5,0<Record12518109Admission.regular T amp S F ν j) :
    Record12518109Admission.highFee≤
      baseMargin T amp ν+min (firstGamma ν*S) (gain ν S F) := by
  have hcommon := regular_common_payment T amp S F ν hνhi (hregular 0) (hregular 1)
  have hgain := regular_gain_payment T amp S F ν hνlo hνhi (hregular 2) (hregular 3) (hregular 4)
  have hg : Record12518109Admission.highFee-baseMargin T amp ν<gain ν S F := by
    dsimp [baseMargin]
    linarith
  have hm := lt_min (show Record12518109Admission.highFee-baseMargin T amp ν<firstGamma ν*S by linarith) hg
  linarith

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

/-- Actual balanced first and second common geometry pays the chosen source
schedule. The width inlet is the literal conservation ledger for surviving
original slots; all analytical supplier losses remain in the explicit errors. -/
theorem actual_geometry_full_gain_payment
    (s : CenteredMomentCommonRadialData.Input alpha) (R seed : Ideal O)
    (K Z xi : ℝ) (hK : 0<K) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (D A a reserve err errv ν T amp S F core live omegaCap : ℝ) (hZ : 1<Z)
    (hνlo : 31/50≤ν) (hνhi : ν≤3/4) (hD : 0≤D)
    (hA : A≤D*T) (ha : a≤D*amp)
    (hregular : ∀k : Fin 5,0<Record12518109Admission.regular T amp S F ν k)
    (hlive : 0≤live)
    (hwidth : D*S≤labelC reflected (geometryFirstLabel s R seed K Z xi hK bin j) Z+
      Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)+live)
    (hcore : 0≤core) (hcore' : core≤1)
    (hOmega : frequencyLoss Z 32 xi+reserve≤D*omegaCap)
    (hFcap : F≤core*(1-6*amp-omegaCap))
    (hF : 0≤core*(compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second
        (geometryFirstLabel s R seed K Z xi hK bin j) d2.C d2.D U Z D A a xi reserve err) errv)
      (balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val))) 2)
    (herr : 0≤err) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z D A a xi reserve err) errv)
      (balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val))
    highExponentValue ν x-gain ν live (core*x 2)≤
      (1-unmarkedDensity ν)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity ν*err+errv-
        D*Record12518109Admission.highFee := by
  intro l x
  have hactual := actual_geometry_balanced_common_payment s R seed K Z xi hK bin j d2
    reflected second U D A a reserve err errv ν hZ hνlo hνhi
  have hfreq := actual_geometry_balanced_moving_frequency s R seed K Z xi hK bin j d2
    reflected second U D A a reserve err errv amp omegaCap core
    (balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val))
    hZ ha hOmega herr hcore hcore'
  dsimp only at hactual hfreq
  have hf : D*F-2*(labelC reflected l Z+
      Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ))≤core*x 2 := by
    have hs := mul_le_mul_of_nonneg_left hFcap hD
    nlinarith only [hfreq.2.2.2,hs]
  have hγ : Valuation.commonGamma ν=firstGamma ν := rfl
  have hr := Valuation.rho_extended_range (show (405/662:ℝ)≤ν by linarith) hνhi
  have hr' : unmarkedDensity ν≤23/50 := hr.2
  have hν : 0≤ν := by linarith
  have hAm := mul_le_mul_of_nonneg_left hA hν
  have ham := mul_le_mul_of_nonneg_right ha (show 0≤5-6*unmarkedDensity ν by linarith)
  have hsource : highExponentValue ν x≤
      (1-unmarkedDensity ν)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity ν*err+errv-
        D*baseMargin T amp ν-firstGamma ν*labelC reflected l Z-
          ν*Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ) := by
    rw [hγ] at hactual
    change highExponentValue ν x≤_ at hactual
    dsimp [baseMargin]
    change _≤ _-D*(1-ν*T-5*amp-unmarkedDensity ν*(1-6*amp))-_ -_
    nlinarith only [hactual,hAm,ham]
  have hp := gain_two_allocation_payment hνlo hνhi hfreq.1 hfreq.2.1 hlive hF hwidth hf
  have heq : min (firstGamma ν*(D*S)) (gain ν (D*S) (D*F))=
      D*min (firstGamma ν*S) (gain ν S F) := by
    rw [gain_homogeneous ν S F D hD,mul_min_of_nonneg _ _ hD]
    congr 1
    ring
  rw [heq] at hp
  have hadmit := regular_joint_admission T amp S F ν hνlo hνhi hregular
  have hscaled := mul_le_mul_of_nonneg_left hadmit hD
  linarith

end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.actual_geometry_full_gain_payment
