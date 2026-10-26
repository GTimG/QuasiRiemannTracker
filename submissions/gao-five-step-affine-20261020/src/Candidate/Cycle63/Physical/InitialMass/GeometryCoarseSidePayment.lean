/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- Restore the outer physical side factor in a coarse bound. The extra
scale power is used only on the coarse branch of height extension. -/
theorem geometry_coarse_side_unit (reflected : Bool) (C Z B : ℝ)
    (key : ℤ×(Fin 5→ℤ)) (hC : 0<C) (hZ : 1≤Z) (hB : 0≤B)
    (hlo : 1≤2*geometryDCompensator key)
    (hhi : geometryDCompensator key≤Z^B) :
    1≤(1+C⁻¹^2)*geometryHighFactor reflected C key*Z^B := by
  have hz : 1≤Z^B:=Real.one_le_rpow hZ hB
  have hh : 0<geometryDCompensator key:=geometryDCompensator_pos key
  have hc : 1≤1+C⁻¹^2:=by nlinarith [sq_nonneg C⁻¹]
  cases reflected
  · simp only [geometryHighFactor,Bool.false_eq_true,ite_false]
    have he : (1+C⁻¹^2)*(2*C^2*geometryDCompensator key)=
        2*(C^2+1)*geometryDCompensator key := by field_simp
    rw [he]
    have hone : 1≤2*(C^2+1)*geometryDCompensator key := by
      nlinarith [mul_nonneg (sq_nonneg C) hh.le]
    nlinarith [mul_nonneg (sub_nonneg.mpr hone) (sub_nonneg.mpr hz)]
  · simp only [geometryHighFactor,ite_true]
    have he : 1≤(geometryDCompensator key)⁻¹*Z^B := by
      rw [←div_eq_inv_mul]
      exact (le_div_iff₀ hh).mpr (by simpa using hhi)
    have hm : 1≤(1+C⁻¹^2)*((geometryDCompensator key)⁻¹*Z^B) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr he)]
    simpa only [mul_assoc] using hm

/-- Actual nonempty first geometry supplies both compensator bounds. No
extra restriction on moving Mellin heights is needed. -/
theorem actual_geometry_coarse_side_unit {ι : Type*} [Fintype ι]
    (reflected : Bool) (C : ℝ) (hC : 0<C)
    (s : Input ι) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hZ : 1≤Z) (hB : 0≤B) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤Z^B)
    (key : ℤ×(Fin 5→ℤ)) (q : CommonGeometryFiber s R seed K Z ξ key) :
    1≤(1+C⁻¹^2)*geometryHighFactor reflected C key*Z^B := by
  have hn:=actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource q.val 1
  have hd:=actual_geometry_D_compensation s R seed K Z ξ B hs hz₁ hz₂ hsource key q
  exact geometry_coarse_side_unit reflected C Z B key hC hZ hB
    (hn.1.trans hd.2.le) (hd.1.trans hn.2)

/-- Reinsert the side factor before extending heights, increasing the
coarse exponent only. Small-height exponents keep their strict saving. -/
theorem geometry_coarse_side_bound (reflected : Bool) (C Z B coarse E K control : ℝ)
    (key : ℤ×(Fin 5→ℤ)) (hZ : 0<Z) (hK : 0≤K) (hc : 0≤ control)
    (hunit : 1≤(1+C⁻¹^2)*geometryHighFactor reflected C key*Z^B)
    (hbound : E≤K*control*Z^coarse) :
    E≤(K*(1+C⁻¹^2))*control*geometryHighFactor reflected C key*Z^(coarse+B) := by
  have hm:=mul_le_mul_of_nonneg_left hunit
    (mul_nonneg (mul_nonneg hK hc) (Real.rpow_nonneg hZ.le coarse))
  rw [mul_one] at hm
  apply hbound.trans
  convert hm using 1
  rw [Real.rpow_add hZ]
  ring

end
end OAI.SevenEighths.Cycle63InitialMass
