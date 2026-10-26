/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal four-type first common geometry pays the full selected width. -/
import Submissions.hailey_collet_1252270103.Record1252270103CommonGeometry.SourceLabel
import Submissions.hailey_collet_1252270103.Record12518109Natural.HighRelativePayment
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.HighScalar
noncomputable section
open OAI OAI.SevenEighths
open Record12518109Natural Record1252270103CommonGeometry Cycle61HighGeometry
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentSecondCanonical
open CenteredMomentRankinRadical CanonicalQuadraticSieve Cycle61Moment
local notation "O" => ActualEisensteinCubic.O

lemma four_type_common (ρ ν a b c d E : ℝ)
    (hρ : 0≤ρ) (hρ1 : ρ≤1) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (hd : 0≤d) (hE : 0≤E) :
    Valuation.firstCommon ρ ν (a+b+2*c+2*d) (a+2*b+c+2*d) (b+c) E (2*c) b-
      Valuation.surplus (a+b+2*c+2*d) (a+2*b+c+2*d) (a+b+c+d) (b+c)≤
      -ν*(a+b+2*c+2*d) := by
  have h1 : 3*(a+b+2*c+2*d)-5*(a+2*b+c+2*d)-(b+c)≤0 := by linarith
  have h2 : 3*(a+2*b+c+2*d)-5*(a+b+2*c+2*d)-(b+c)≤0 := by linarith
  unfold Valuation.firstCommon Valuation.surplus
  rw [max_eq_right h1,max_eq_right h2]
  rw [max_def]
  split_ifs with h
  · nlinarith [mul_nonneg hρ hb,mul_nonneg (sub_nonneg.mpr hρ1) hc]
  · nlinarith

/-- No restriction beyond the actual at-most-two column valuations is used.
The inactive first projector remains present with its favorable sign. -/
theorem first_label_common_price (reflected : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2)
    (hbC : ValuationAtMostTwo l.1.1) (hbD : ValuationAtMostTwo l.1.2)
    (Z ν ρ : ℝ) (hZ : 1<Z) (hρ : 0≤ρ) (hρ1 : ρ≤1) :
    Valuation.firstCommon ρ ν (labelC reflected l Z) (labelD reflected l Z)
      (labelR l Z) (labelE l Z)
      (Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ))
      (Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ))-
      labelSurplus reflected l Z ≤ -ν*labelC reflected l Z := by
  have hc := commonPart_eq_left l.1.1 l.1.2 hC.1 heq
  have hd := commonPart_eq_left l.1.2 l.1.1 hD.1 heq.symm
  have hcl := left_common_width Z l.1.1 l.1.2 hbC hbD
  have hdr := right_common_width Z l.1.1 l.1.2 hbC hbD
  rw [hc] at hcl
  rw [hd] at hdr
  have hp := common_radical_width Z l.1.1 l.1.2 hbC hbD
  have hr := active_width Z l.1.1 l.1.2 hbC hbD
  have he : 0≤labelE l Z := by
    apply Real.logb_nonneg hZ
    exact_mod_cast firstCommonSubsetNorm_pos l.1.1 l.1.2 hC l.2.val
  have hn m n := stratumWidth_nonneg Z hZ l.1.1 l.1.2 m n
  cases reflected
  · have hl := left_numerator_width Z l.1.1 l.1.2 hC hbC hbD
    have hcancel := left_cancelled_width Z l.1.1 l.1.2 hbC hbD
    change Valuation.firstCommon ρ ν (normLog Z l.1.1) (normLog Z l.1.2)
      (normLog Z (Ideal.span {activeConductor l.1.1 l.1.2})) (labelE l Z)
      (normLog Z (Ideal.span {firstLeftUncancelled l.1.1 l.1.2}))
      (normLog Z (firstLeftCancelledRadical l.1.1 l.1.2))-
      Valuation.surplus (normLog Z l.1.1) (normLog Z l.1.2)
        (normLog Z (commonRadical l.1.1 l.1.2))
        (normLog Z (Ideal.span {activeConductor l.1.1 l.1.2}))≤-ν*normLog Z l.1.1
    rw [hcl,hdr,hp,hr,hl,hcancel]
    exact four_type_common ρ ν _ _ _ _ _ hρ hρ1 (hn 1 1) (hn 1 2) (hn 2 1) (hn 2 2) he
  · have hl := right_numerator_width Z l.1.1 l.1.2 hC hbC hbD
    have hcancel := right_cancelled_width Z l.1.1 l.1.2 hbC hbD
    change Valuation.firstCommon ρ ν (normLog Z l.1.2) (normLog Z l.1.1)
      (normLog Z (Ideal.span {activeConductor l.1.1 l.1.2})) (labelE l Z)
      (normLog Z (Ideal.span {firstRightUncancelled l.1.1 l.1.2}))
      (normLog Z (firstRightCancelledRadical l.1.1 l.1.2))-
      Valuation.surplus (normLog Z l.1.2) (normLog Z l.1.1)
        (normLog Z (commonRadical l.1.1 l.1.2))
        (normLog Z (Ideal.span {activeConductor l.1.1 l.1.2}))≤-ν*normLog Z l.1.2
    rw [hcl,hdr,hp,hr,hl,hcancel]
    convert four_type_common ρ ν (stratumWidth Z l.1.1 l.1.2 1 1)
      (stratumWidth Z l.1.1 l.1.2 2 1) (stratumWidth Z l.1.1 l.1.2 1 2)
      (stratumWidth Z l.1.1 l.1.2 2 2) (labelE l Z) hρ hρ1
      (hn 1 1) (hn 2 1) (hn 1 2) (hn 2 2) he using 1 <;> congr 1 <;> ring

end
end QRH.Record1252270103Source.HighScalar
#print axioms QRH.Record1252270103Source.HighScalar.four_type_common
#print axioms QRH.Record1252270103Source.HighScalar.first_label_common_price
