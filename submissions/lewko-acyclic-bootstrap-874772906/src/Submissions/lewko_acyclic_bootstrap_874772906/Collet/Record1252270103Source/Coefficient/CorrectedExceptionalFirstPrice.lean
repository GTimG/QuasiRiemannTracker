/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual first common geometry pays an inverse radical and two-thirds of
the chosen common width. Centering then pays the advertised 499/1000 gate. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103CommonGeometry.SourceLabel
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Assembly.BalancedGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103StepScalar.Geometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.HighLedgerGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.HighAllocation
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryMainRadius

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Record1252270103CommonGeometry Cycle61HighGeometry Record12518109Natural
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentSecondCanonical
open CenteredMomentRankinRadical CanonicalQuadraticSieve Cycle61Moment
open Record1252270103Finite Record1252270103StepScalar
open Cycle61InitialMass CenteredMomentFirstAmplificationChoice CenteredMomentFirstScale
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentFirstCanonicalFamily
local notation "O" => ActualEisensteinCubic.O

def commonPrice (c d R E : ℝ) : ℝ :=
  R/3-E/6-2*c/3-4*d/3+5*max (d-c) 0/6-
    (QRH.Record12518109Assembly.Scalar.side c d R-
      QRH.Record12518109Assembly.Scalar.side d c R)/2

theorem four_type_price (a b c d E : ℝ)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) (hE : 0≤E) :
    commonPrice (a+b+2*c+2*d) (a+2*b+c+2*d) (b+c) E+
      (a+b+c+d)≤-2*(a+b+2*c+2*d)/3 := by
  have h1 : 3*(a+b+2*c+2*d)-5*(a+2*b+c+2*d)-(b+c)≤0 := by linarith
  have h2 : 3*(a+2*b+c+2*d)-5*(a+b+2*c+2*d)-(b+c)≤0 := by linarith
  unfold commonPrice QRH.Record12518109Assembly.Scalar.side
  rw [max_eq_right h1,max_eq_right h2,max_def]
  split_ifs <;> linarith

theorem actual_first_common_price (reflected : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2)
    (hbC : ValuationAtMostTwo l.1.1) (hbD : ValuationAtMostTwo l.1.2)
    (Z : ℝ) (hZ : 1<Z) :
    commonPrice (labelC reflected l Z) (labelD reflected l Z) (labelR l Z) (labelE l Z)+
      labelP l Z≤-2*labelC reflected l Z/3 := by
  have hc:=commonPart_eq_left l.1.1 l.1.2 hC.1 heq
  have hd:=commonPart_eq_left l.1.2 l.1.1 hD.1 heq.symm
  have hcl:=left_common_width Z l.1.1 l.1.2 hbC hbD
  have hdr:=right_common_width Z l.1.1 l.1.2 hbC hbD
  rw [hc] at hcl
  rw [hd] at hdr
  have hp:=common_radical_width Z l.1.1 l.1.2 hbC hbD
  have hr:=active_width Z l.1.1 l.1.2 hbC hbD
  have he : 0≤labelE l Z := by
    apply Real.logb_nonneg hZ
    exact_mod_cast firstCommonSubsetNorm_pos l.1.1 l.1.2 hC l.2.val
  have hn m n:=stratumWidth_nonneg Z hZ l.1.1 l.1.2 m n
  cases reflected
  · change commonPrice (normLog Z l.1.1) (normLog Z l.1.2)
      (normLog Z (Ideal.span {activeConductor l.1.1 l.1.2})) (labelE l Z)+
        normLog Z (commonRadical l.1.1 l.1.2)≤-2*normLog Z l.1.1/3
    rw [hcl,hdr,hp,hr]
    exact four_type_price _ _ _ _ _ (hn 1 1) (hn 1 2) (hn 2 1) (hn 2 2) he
  · change commonPrice (normLog Z l.1.2) (normLog Z l.1.1)
      (normLog Z (Ideal.span {activeConductor l.1.1 l.1.2})) (labelE l Z)+
        normLog Z (commonRadical l.1.1 l.1.2)≤-2*normLog Z l.1.2/3
    rw [hcl,hdr,hp,hr]
    convert four_type_price (stratumWidth Z l.1.1 l.1.2 1 1)
      (stratumWidth Z l.1.1 l.1.2 2 1) (stratumWidth Z l.1.1 l.1.2 1 2)
      (stratumWidth Z l.1.1 l.1.2 2 2) (labelE l Z)
      (hn 1 1) (hn 2 1) (hn 1 2) (hn 2 2) he using 1 <;> congr 1 <;> ring

/-- Squared centering may be weakened to one copy only after keeping its
common-width shift. This is valid even when the shifted raw scale is subunit. -/
theorem centered_common_payment (L c α : ℝ) (hc : 0≤c) (hα : 0≤α) (hαmax : α≤2/3) :
    -2*c/3-2*α*max (L-c) 0≤-α*L := by
  have hmax : L-c≤max (L-c) 0:=le_max_left _ _
  have hm0 : 0≤max (L-c) 0:=le_max_right _ _
  nlinarith [mul_nonneg hα hm0,mul_nonneg (sub_nonneg.mpr hαmax) hc]

theorem first_exponent_identity (A M c d R E amp omega : ℝ) :
    (A-c)/3+5*(2*A-M+R+E-c-d+max (d-c) 0+6*amp+omega)/6-
      QRH.Record12518109Assembly.Scalar.left A c d R E=
    A-5*M/6+5*amp+5*omega/6+commonPrice c d R E := by
  unfold QRH.Record12518109Assembly.Scalar.left commonPrice
  ring

theorem first_nominal_log (C D E : Ideal O) (hC : Supported C) (hD : Supported D)
    (heq : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (hE : E≠0)
    (Z M V : ℝ) (hZ : 1<Z) (hV : 0<V) :
    nominalLog C D E (Z^M) V Z=2*Real.logb Z V-M+
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)+
      Real.logb Z (E.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ) := by
  have hc:=norm_pos C hC.1
  have hd:=norm_pos D hD.1
  have he:=norm_pos E hE
  have hr:=active_norm_pos C D
  unfold nominalLog firstNominalScale
  rw [commonPart_eq_left C D hC.1 heq,commonPart_eq_left D C hD.1 heq.symm]
  simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow,
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

/-- Exact declared MAIN radius, with the original parent volume. -/
theorem actual_first_main_log (reflected : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2)
    (Z M V ξ amp reserve : ℝ) (hZ : 1<Z) (hV : 0<V) :
    Real.logb Z (firstMainRadius reflected (Z^M) V Z ξ (3*amp) reserve l)=
      2*Real.logb Z V-M+labelR l Z+labelE l Z-labelC reflected l Z-labelD reflected l Z+
        max (labelD reflected l Z-labelC reflected l Z) 0+6*amp+frequencyLoss Z 32 ξ+reserve := by
  have he:=(subsetGenerator_supported l.1.1 l.1.2 hC l.2.val).1
  rw [firstMainRadius,mainCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',
    first_nominal_log l.1.1 l.1.2 _ hC hD heq he Z M V hZ hV,first_projector_span]
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true,labelC,labelD,labelR,labelE]
  all_goals ring

/-- The literal finite-node centered gate leaves four amplification widths
after the one prime average and the stated total small error. -/
theorem node_centered_payment (K : ℚ) (n low : Source) (b A c d R E p omega loss plainError : ℝ)
    (hg : RealGeometry K n low b) (hc : 0≤c)
    (hcommon : commonPrice c d R E+p≤-2*c/3)
    (hA : A≤sourceTReal n b+b+plainError)
    (herr : plainError+5*omega/6+loss≤sourceAReal n low b) :
    (A-c)/3+5*(2*A-1+R+E-c-d+max (d-c) 0+6*sourceAReal n low b+omega)/6-
      QRH.Record12518109Assembly.Scalar.left A c d R E+p-
      2*(499/1000)*max ((49/100-(K:ℝ)*b)-c) 0-sourceAReal n low b+loss<
      -(n.highFee:ℝ)-4*sourceAReal n low b := by
  rw [first_exponent_identity]
  have hcenter:=centered_common_payment (49/100-(K:ℝ)*b) c (499/1000) hc (by norm_num) (by norm_num)
  have hgate:=hg.centered_499
  linarith

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.four_type_price
#print axioms QRH.Record1252270103Source.ExceptionalPrice.actual_first_common_price
#print axioms QRH.Record1252270103Source.ExceptionalPrice.centered_common_payment
#print axioms QRH.Record1252270103Source.ExceptionalPrice.first_exponent_identity
#print axioms QRH.Record1252270103Source.ExceptionalPrice.first_nominal_log
#print axioms QRH.Record1252270103Source.ExceptionalPrice.actual_first_main_log
#print axioms QRH.Record1252270103Source.ExceptionalPrice.node_centered_payment
