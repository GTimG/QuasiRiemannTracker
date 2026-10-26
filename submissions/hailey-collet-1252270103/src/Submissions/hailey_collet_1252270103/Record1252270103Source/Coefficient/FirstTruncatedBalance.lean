/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual modified first geometry supplies the balance cap required by the
Mellin extension, with the physical D compensator retained literally. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalScalarCompensation
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryHighPayment
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.FirstTruncatedHeights
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open Cycle61InitialMass CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentOriginalCommonHarmonic
open QRH.Record1252270103Source.High.CoupledFirst
local notation "O"=>HeckeFamily.O

theorem actual_geometry_balance_cap {ι:Type*}[Fintype ι]
    (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)(K Z ξ B:ℝ)
    (hZ:2≤Z)(hs:Squarefree seed)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (hsource:sourceRadius s≤Z^B)(key:ℤ×(Fin 5→ℤ))
    (hkey:key∈commonGeometryBins s modifier R seed K Z ξ)(reflected:Bool) :
    1≤(if reflected then (geometryDCompensator key)⁻¹ else geometryDCompensator key)*Z^(max B 1) := by
  obtain ⟨q,hq,hkey⟩:=Finset.mem_image.mp hkey
  let qf:CommonGeometryFiber s modifier R seed K Z ξ key:=⟨q,hkey⟩
  have hd:=actual_geometry_D_compensation s modifier R seed K Z ξ B hs hz₁ hz₂ hsource key qf
  have hn:=actual_geometry_norm_caps s modifier R seed K Z ξ B hs hz₁ hz₂ hsource q 1
  have hH:=geometryDCompensator_pos key
  have hZ1:1≤Z:=by linarith
  have hupper:geometryDCompensator key≤Z^(max B 1):=hd.1.trans (hn.2.trans
    (Real.rpow_le_rpow_of_exponent_le hZ1 (le_max_left _ _)))
  have htwo:2≤Z^(max B 1):=hZ.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ1 (le_max_right B 1))
  have hlower:1≤2*geometryDCompensator key:=by
    change 1≤(q.1.val.2.absNorm:ℝ) ∧ _ at hn
    linarith [hn.1,hd.2]
  cases reflected
  · simp only [Bool.false_eq_true,ite_false]
    nlinarith [mul_le_mul_of_nonneg_left htwo hH.le]
  · simp only [ite_true]
    have hh:1≤Z^(max B 1)/geometryDCompensator key:=(one_le_div hH).mpr hupper
    simpa only [div_eq_mul_inv,mul_comm] using hh

/-- One fixed common factor matches the left and right scalar payments. -/
theorem high_factor_balanced (C V:ℝ)(hV:0≤V)(key:ℤ×(Fin 5→ℤ))(reflected:Bool) :
    geometryHighFactor reflected C key*V≤
      if reflected then (max 1 (2*C^2)*V)/geometryDCompensator key
      else (max 1 (2*C^2)*V)*geometryDCompensator key := by
  have hp:0<geometryDCompensator key:=geometryDCompensator_pos key
  cases reflected
  · simp only [geometryHighFactor,Bool.false_eq_true,ite_false]
    have hh:=mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (2*C^2)) (mul_nonneg hV hp.le)
    nlinarith only [hh]
  · simp only [geometryHighFactor,ite_true]
    have hh:=mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) (2*C^2))
      (mul_nonneg hV (inv_nonneg.mpr hp.le))
    simpa only [one_mul,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

end
end QRH.Record1252270103Source.FirstTruncatedHeights
#print axioms QRH.Record1252270103Source.FirstTruncatedHeights.actual_geometry_balance_cap
#print axioms QRH.Record1252270103Source.FirstTruncatedHeights.high_factor_balanced
