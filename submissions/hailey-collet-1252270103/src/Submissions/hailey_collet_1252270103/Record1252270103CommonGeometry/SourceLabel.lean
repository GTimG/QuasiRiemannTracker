/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Exact geometry in the existing first-source label and signed numerator API. -/
import Submissions.hailey_collet_1252270103.Record1252270103CommonGeometry.ActualPair
import Submissions.hailey_collet_1252270103.Cycle61.Moment.FirstSourceCount

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103CommonGeometry
noncomputable section
open scoped Classical BigOperators
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentSecondCanonical
open CenteredMomentRankinRadical CanonicalQuadraticSieve Cycle61Moment
local notation "O" => ActualEisensteinCubic.O

/-- `left=true` uses c=C,d=D and the actual left numerator; `left=false`
uses c=D,d=C and the actual right numerator. The inactive subset is retained
in the source label and is not replaced or independently enlarged. -/
theorem first_source_raw_exponent (left : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2)
    (hbC : ValuationAtMostTwo l.1.1) (hbD : ValuationAtMostTwo l.1.2) (Z F : ℝ) :
    let c := normLog Z (if left then l.1.1 else l.1.2)
    let d := normLog Z (if left then l.1.2 else l.1.1)
    F-normLog Z (Ideal.span {activeConductor l.1.1 l.1.2})-max (c-d) 0+
      normLog Z (Ideal.span {firstSourceNumerator left l})=F-max (d-c) 0 := by
  have hc := commonPart_eq_left l.1.1 l.1.2 hC.1 heq
  have hd := commonPart_eq_left l.1.2 l.1.1 hD.1 heq.symm
  cases left
  · simpa only [Bool.false_eq_true,ite_false,firstSourceNumerator,hc,hd]
      using restored_raw_exponent_right Z F l.1.1 l.1.2 hC hbC hbD
  · simpa only [ite_true,firstSourceNumerator,hc,hd]
      using restored_raw_exponent Z F l.1.1 l.1.2 hC hbC hbD

theorem first_source_deficit_bounds (left : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2)
    (hbC : ValuationAtMostTwo l.1.1) (hbD : ValuationAtMostTwo l.1.2)
    (Z : ℝ) (hZ : 1<Z) :
    let c := normLog Z (if left then l.1.1 else l.1.2)
    let d := normLog Z (if left then l.1.2 else l.1.1)
    max (d-c) 0≤c ∧ 2*max (d-c) 0≤d := by
  have hc := commonPart_eq_left l.1.1 l.1.2 hC.1 heq
  have hd := commonPart_eq_left l.1.2 l.1.1 hD.1 heq.symm
  cases left
  · simpa only [Bool.false_eq_true,ite_false,hc,hd]
      using (deficit_bounds Z hZ l.1.2 l.1.1 hbD hbC).2
  · simpa only [ite_true,hc,hd]
      using (deficit_bounds Z hZ l.1.1 l.1.2 hbC hbD).2

/-- Exact counted missing radical with the original inactive projector. -/
theorem first_source_missing_width (left : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1)
    (hbC : ValuationAtMostTwo l.1.1) (hbD : ValuationAtMostTwo l.1.2) (Z : ℝ) :
    normLog Z (firstSourceMissing left l)=stratumWidth Z l.1.1 l.1.2 1 1+
      (if left then stratumWidth Z l.1.1 l.1.2 1 2 else stratumWidth Z l.1.1 l.1.2 2 1)+
      stratumWidth Z l.1.1 l.1.2 2 2-normLog Z (firstProjectorRadical l.1.1 l.1.2 l.2.val) := by
  have hp := common_radical_width Z l.1.1 l.1.2 hbC hbD
  have hr := active_width Z l.1.1 l.1.2 hbC hbD
  cases left
  · have h := actual_first_right_missing_width l.1.1 l.1.2 hC l.2.val l.2.property Z
    change normLog Z (firstSourceMissing false l)=_
    change normLog Z (firstSourceMissing false l)=
      normLog Z (commonRadical l.1.1 l.1.2)-normLog Z (Ideal.span {activeConductor l.1.1 l.1.2})-
        normLog Z (firstProjectorRadical l.1.1 l.1.2 l.2.val)+normLog Z (firstRightCancelledRadical l.1.1 l.1.2) at h
    rw [h,hp,hr,right_cancelled_width Z l.1.1 l.1.2 hbC hbD]
    simp only [Bool.false_eq_true,ite_false]
    ring
  · have h := actual_first_left_missing_width l.1.1 l.1.2 hC l.2.val l.2.property Z
    change normLog Z (firstSourceMissing true l)=_
    change normLog Z (firstSourceMissing true l)=
      normLog Z (commonRadical l.1.1 l.1.2)-normLog Z (Ideal.span {activeConductor l.1.1 l.1.2})-
        normLog Z (firstProjectorRadical l.1.1 l.1.2 l.2.val)+normLog Z (firstLeftCancelledRadical l.1.1 l.1.2) at h
    rw [h,hp,hr,left_cancelled_width Z l.1.1 l.1.2 hbC hbD]
    simp only [ite_true]
    ring

end
end OAI.SevenEighths.Record1252270103CommonGeometry

#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.first_source_raw_exponent
#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.first_source_deficit_bounds
#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.first_source_missing_width
