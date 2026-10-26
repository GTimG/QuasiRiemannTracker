/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual first MAIN radius and clipped divided reference length pay the
centered finite-node gate. Both orientations use the same parent volume. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedExceptionalFirstPrice
import Submissions.hailey_collet_1252270103.Record1252270103Source.HighScalar.ModifiedGeometry

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Cycle61Moment Cycle61HighGeometry
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentSecondCanonical
open Record12518109Natural Record1252270103CommonGeometry
open Record1252270103Finite Record1252270103StepScalar
open Cycle61InitialMass CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

theorem clipped_reference_power (Z r c : ℝ) (hZ : 1<Z) :
    max 1 (Z^(r-c))=Z^(max (r-c) 0) := by
  by_cases h : 0≤r-c
  · rw [max_eq_left h, max_eq_right (Real.one_le_rpow hZ.le h)]
  · have h' : r-c≤0 := le_of_not_ge h
    rw [max_eq_right h',Real.rpow_zero,
      max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hZ.le h')]

def firstScalarCost (reflected : Bool) (l : FirstSourceLabel)
    (Z V r amp ξ reserve loss : ℝ) : ℝ :=
  let C : Ideal O:=if reflected then l.1.2 else l.1.1
  (V/(C.absNorm:ℝ))^(1/3:ℝ)*
    (firstMainRadius reflected Z V Z ξ (3*amp) reserve l)^(5/6:ℝ)*
    (max 1 (Z^r/(C.absNorm:ℝ)))^(-(2*(499/1000:ℝ)))*Z^(-amp+loss)/
    Z^(QRH.Record12518109Assembly.Scalar.left (Real.logb Z V)
      (labelC reflected l Z) (labelD reflected l Z) (labelR l Z) (labelE l Z))

theorem actual_first_scalar_cost (K : ℚ) (n low : Source) (b : ℝ)
    (hg : RealGeometry K n low b) (reflected : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (hbC : ValuationAtMostTwo l.1.1) (hbD : ValuationAtMostTwo l.1.2)
    (Z V ξ reserve loss plainError : ℝ) (hZ : 1<Z) (hV : 0<V)
    (hA : Real.logb Z V≤sourceTReal n b+b+plainError)
    (herr : plainError+5*(frequencyLoss Z 32 ξ+reserve)/6+loss≤sourceAReal n low b) :
    firstScalarCost reflected l Z V (49/100-(K:ℝ)*b)
      (sourceAReal n low b) ξ reserve loss≤
      Z^(-(n.highFee:ℝ)-4*sourceAReal n low b-labelP l Z) := by
  let C : Ideal O:=if reflected then l.1.2 else l.1.1
  have hc : C≠0 := by cases reflected <;> first | exact hC.1 | exact hD.1
  have hcpos : (0:ℝ)<C.absNorm := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hc)
  have hcn : Real.logb Z (C.absNorm:ℝ)=labelC reflected l Z := by
    cases reflected <;> rfl
  have hcl : 0≤labelC reflected l Z := by
    rw [←hcn]
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hc)
  have hZ0:=zero_lt_one.trans hZ
  have hce : (C.absNorm:ℝ)=Z^(labelC reflected l Z) := by
    rw [←hcn,Real.rpow_logb hZ0 hZ.ne' hcpos]
  have hve : V=Z^(Real.logb Z V):=(Real.rpow_logb hZ0 hZ.ne' hV).symm
  have hH:=actual_first_main_log reflected l hC hD heq Z 1 V ξ
    (sourceAReal n low b) reserve hZ hV
  simp only [Real.rpow_one] at hH
  have hhe : firstMainRadius reflected Z V Z ξ (3*sourceAReal n low b) reserve l=
      Z^(2*Real.logb Z V-1+labelR l Z+labelE l Z-labelC reflected l Z-labelD reflected l Z+
        max (labelD reflected l Z-labelC reflected l Z) 0+6*sourceAReal n low b+frequencyLoss Z 32 ξ+reserve) := by
    rw [←hH,Real.rpow_logb hZ0 hZ.ne' (first_main_radius_pos reflected Z V Z ξ
      (3*sourceAReal n low b) reserve hZ0 l)]
  have hp:=node_centered_payment K n low b (Real.logb Z V) (labelC reflected l Z)
    (labelD reflected l Z) (labelR l Z) (labelE l Z) (labelP l Z)
    (frequencyLoss Z 32 ξ+reserve) loss plainError hg hcl
    (actual_first_common_price reflected l hC hD heq hbC hbD Z hZ) hA herr
  have hratio : V/(C.absNorm:ℝ)=Z^(Real.logb Z V-labelC reflected l Z) := by
    rw [Real.rpow_sub hZ0,←hve,←hce]
  have href : Z^(49/100-(K:ℝ)*b)/(C.absNorm:ℝ)=
      Z^(49/100-(K:ℝ)*b-labelC reflected l Z) := by
    rw [Real.rpow_sub hZ0 (49/100-(K:ℝ)*b) (labelC reflected l Z),←hce]
  unfold firstScalarCost
  change (V/(C.absNorm:ℝ))^(1/3:ℝ)*_*(max 1 (Z^_/(C.absNorm:ℝ)))^_*_/_≤_
  rw [hratio,href,clipped_reference_power Z _ _ hZ,hhe]
  simp only [←Real.rpow_mul hZ0.le,←Real.rpow_add hZ0,←Real.rpow_sub hZ0]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  nlinarith

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.clipped_reference_power
#print axioms QRH.Record1252270103Source.ExceptionalPrice.actual_first_scalar_cost
