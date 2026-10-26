/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal first-label four strata pay the LOW missing-radical count.
Both the second common cost and the inactive projector retain their signs. -/
import Submissions.hailey_collet_1252270103.Record12518109Raw.RawWeight
import Submissions.hailey_collet_1252270103.Record1252270103Source.HighScalar.ModifiedGeometry
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.CommonCost
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
open CenteredMomentSectorLocalization
open Cycle61FinalCapacity Cycle61HighGeometry Cycle61InitialMass Cycle61Moment
open Record12518109Natural Record12518109Raw Record1252270103CommonGeometry
open QRH.Record12518109Source QRH.Record1252270103Low
local notation "O"=>HeckeFamily.O

def lowTypePenalty (reflected:Bool)(l:FirstSourceLabel)(Z:ℝ):ℝ:=
  if reflected then stratumWidth Z l.1.1 l.1.2 2 1 else stratumWidth Z l.1.1 l.1.2 1 2

def lowSecondPenalty (second:Bool)(C D:Ideal O)(U:Finset (CommonIndex C D))(Z:ℝ):ℝ:=
  Real.logb Z ((if second then D else C).absNorm:ℝ)-
    Real.logb Z (normValue (commonFrequencyGenerator C D))+
    Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)

theorem four_type_low_first (reflected:Bool)(l:FirstSourceLabel)
    (hC:Supported l.1.1)(hD:Supported l.1.2)
    (heq:primeSupport l.1.1=primeSupport l.1.2)
    (hbC:ValuationAtMostTwo l.1.1)(hbD:ValuationAtMostTwo l.1.2)
    (Z:ℝ)(hZ:1<Z):
    -2*labelR l Z-max (3*labelC reflected l Z-5*labelD reflected l Z-labelR l Z) 0/6+
      Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ)+
      Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ)-
      labelSurplus reflected l Z = -lowTypePenalty reflected l Z-stratumWidth Z l.1.1 l.1.2 2 2 := by
  have hc:=commonPart_eq_left l.1.1 l.1.2 hC.1 heq
  have hd:=commonPart_eq_left l.1.2 l.1.1 hD.1 heq.symm
  have hcl:=left_common_width Z l.1.1 l.1.2 hbC hbD
  have hdr:=right_common_width Z l.1.1 l.1.2 hbC hbD
  rw [hc] at hcl
  rw [hd] at hdr
  have hp:=common_radical_width Z l.1.1 l.1.2 hbC hbD
  have hr:=active_width Z l.1.1 l.1.2 hbC hbD
  have hn m n:=stratumWidth_nonneg Z hZ l.1.1 l.1.2 m n
  cases reflected
  · have hl:=left_numerator_width Z l.1.1 l.1.2 hC hbC hbD
    have hk:=left_cancelled_width Z l.1.1 l.1.2 hbC hbD
    change -2*normLog Z (Ideal.span {activeConductor l.1.1 l.1.2})-
      max (3*normLog Z l.1.1-5*normLog Z l.1.2-normLog Z (Ideal.span {activeConductor l.1.1 l.1.2})) 0/6+
      normLog Z (Ideal.span {firstLeftUncancelled l.1.1 l.1.2})+normLog Z (firstLeftCancelledRadical l.1.1 l.1.2)-
      Valuation.surplus (normLog Z l.1.1) (normLog Z l.1.2) (normLog Z (commonRadical l.1.1 l.1.2))
        (normLog Z (Ideal.span {activeConductor l.1.1 l.1.2})) = _
    rw [hcl,hdr,hp,hr,hl,hk]
    unfold Valuation.surplus
    rw [max_eq_right (by linarith [hn 1 1,hn 1 2,hn 2 1,hn 2 2]),
      max_eq_right (by linarith [hn 1 1,hn 1 2,hn 2 1,hn 2 2])]
    simp only [lowTypePenalty,Bool.false_eq_true,ite_false]
    ring
  · have hl:=right_numerator_width Z l.1.1 l.1.2 hC hbC hbD
    have hk:=right_cancelled_width Z l.1.1 l.1.2 hbC hbD
    change -2*normLog Z (Ideal.span {activeConductor l.1.1 l.1.2})-
      max (3*normLog Z l.1.2-5*normLog Z l.1.1-normLog Z (Ideal.span {activeConductor l.1.1 l.1.2})) 0/6+
      normLog Z (Ideal.span {firstRightUncancelled l.1.1 l.1.2})+normLog Z (firstRightCancelledRadical l.1.1 l.1.2)-
      Valuation.surplus (normLog Z l.1.2) (normLog Z l.1.1) (normLog Z (commonRadical l.1.1 l.1.2))
        (normLog Z (Ideal.span {activeConductor l.1.1 l.1.2})) = _
    rw [hcl,hdr,hp,hr,hl,hk]
    unfold Valuation.surplus
    rw [max_eq_right (by linarith [hn 1 1,hn 1 2,hn 2 1,hn 2 2]),
      max_eq_right (by linarith [hn 1 1,hn 1 2,hn 2 1,hn 2 2])]
    simp only [lowTypePenalty,ite_true]
    ring

theorem actual_low_coordinate_identity (reflected second:Bool)(l:FirstSourceLabel)
    (hC:Supported l.1.1)(hD:Supported l.1.2)
    (heq:primeSupport l.1.1=primeSupport l.1.2)
    (hbC:ValuationAtMostTwo l.1.1)(hbD:ValuationAtMostTwo l.1.2)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(Z M A a ξ reserve err errv:ℝ)(hZ:1<Z):
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l C D U Z M A a ξ reserve err) errv
    x 0+x 1+x 2-labelSide reflected l Z A-labelSurplus reflected l Z=
      -a-lowTypePenalty reflected l Z-
        (stratumWidth Z l.1.1 l.1.2 2 2+labelE l Z+lowSecondPenalty second C D U Z)+err+errv := by
  intro x
  rw [actual_raw_coordinate_identity reflected second l hC C D U Z M A a ξ reserve err errv]
  have hf:=four_type_low_first reflected l hC hD heq hbC hbD Z hZ
  dsimp only [rawExcess,lowSecondPenalty]
  linarith only [hf]

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.four_type_low_first
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_low_coordinate_identity
