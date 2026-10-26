/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The full second family keeps its first-geometry factor through both
unrestricted Mellin integrals. The large-height input is the finite absolute budget. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalNormalizedHeights
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.FirstTruncatedBalance
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily Cycle61InitialMass CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform

def regularGeometryFloor (C:ℝ):ℝ:=max 1 ((2*C^2)⁻¹)

theorem regular_geometry_floor (C Z B:ℝ)(hC:0<C)(hZ:0<Z)
    (bin:ℤ×(Fin 5→ℤ))(reflected:Bool)
    (hbalance:1≤(if reflected then (geometryDCompensator bin)⁻¹ else geometryDCompensator bin)*Z^B):
    1≤regularGeometryFloor C*geometryHighFactor reflected C bin*Z^B:=by
  have hH:=geometryDCompensator_pos bin
  have hfloor:1≤regularGeometryFloor C:=le_max_left _ _
  have hpow:=Real.rpow_pos_of_pos hZ B
  cases reflected
  · simp only [Bool.false_eq_true,ite_false,geometryHighFactor] at hbalance ⊢
    have hC2:0<2*C^2:=by positivity
    have hf:1≤regularGeometryFloor C*(2*C^2):=by
      have h:=mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) ((2*C^2)⁻¹)) hC2.le
      simpa only [regularGeometryFloor,inv_mul_cancel₀ hC2.ne'] using h
    have h:=mul_le_mul_of_nonneg_right hf (mul_nonneg hH.le hpow.le)
    nlinarith only [hbalance,h]
  · simp only [Bool.true_eq_false,ite_true,geometryHighFactor] at hbalance ⊢
    have h:=mul_le_mul_of_nonneg_right hfloor (mul_nonneg (inv_nonneg.mpr hH.le) hpow.le)
    nlinarith only [hbalance,h]

/-- The integration degree precedes all moving data. The bounded estimate
and the absolute envelope are exactly the two genuine caller outputs. -/
theorem regular_normalized_height_extension (τ absoluteExponent balanceExponent saving:ℝ)
    (hτ:0<τ)(smallDegree:ℕ):
    ∃J:ℕ,∀{α Label:Type*}[Fintype α][DecidableEq α][Fintype Label]
      (second:Bool)(d:Label→SecondInputDatum α)(modifier:∀l,Tuple (d l).slots→ℂ)
      (weight:Label→ℂ)(Z control geometry external Csmall Cabs Cgeom:ℝ),
      1≤Z→0≤control→0≤geometry→1≤external→0≤Csmall→0≤Cabs→0≤Cgeom→
      1≤Cgeom*geometry*Z^balanceExponent→
      (∀t u:ℝ,(1+‖t‖)*(1+‖u‖)≤Z^τ→
        modifiedSecondNormalizedSum second d modifier weight t u≤
          Csmall*geometry*control*external^smallDegree*((1+‖t‖)*(1+‖u‖))^smallDegree*Z^(-saving))→
      secondAbsoluteBudget d modifier weight≤Cabs*control*Z^absoluteExponent→
      ∀t u:ℝ,modifiedSecondNormalizedSum second d modifier weight t u≤
        ((Csmall+Cabs*Cgeom)*geometry*control*external^smallDegree*Z^(-saving)*(1+‖t‖)^J)*(1+‖u‖)^(2*J):=by
  obtain ⟨J,hJ⟩:=modified_normalized_height_extension τ (absoluteExponent+balanceExponent) (-saving) hτ smallDegree
  refine ⟨J,?_⟩
  intro α Label _ _ _ second d modifier weight Z control geometry external Cs Ca Cg hZ hc hg he hCs hCa hCg hfloor hsmall habs t u
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hepow:1≤external^smallDegree:=one_le_pow₀ he
  have hcoarse:secondAbsoluteBudget d modifier weight≤
      (Ca*Cg)*(geometry*control*external^smallDegree)*Z^(0+(absoluteExponent+balanceExponent)):=by
    have hnon:0≤Ca*control*Z^absoluteExponent:=by positivity
    have hm:=mul_le_mul_of_nonneg_left hfloor hnon
    have hm':Ca*control*Z^absoluteExponent≤Ca*Cg*geometry*control*Z^(absoluteExponent+balanceExponent):=by
      calc
        _≤(Ca*control*Z^absoluteExponent)*(Cg*geometry*Z^balanceExponent):=by simpa using hm
        _=_:=by rw [Real.rpow_add hz];ring
    have hp:=mul_le_mul_of_nonneg_left hepow
      (show 0≤Ca*Cg*geometry*control*Z^(absoluteExponent+balanceExponent) by positivity)
    exact habs.trans (hm'.trans (by convert hp using 1 <;> first | rfl | ring))
  have hh:=hJ second d modifier weight Z 0 (geometry*control*external^smallDegree) Cs (Ca*Cg)
    hZ (by positivity) hCs (mul_nonneg hCa hCg)
    (fun t u ht=>by simpa only [zero_add,mul_assoc] using hsmall t u ht) hcoarse t u
  simpa only [zero_add,mul_assoc] using hh
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_geometry_floor
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_normalized_height_extension
