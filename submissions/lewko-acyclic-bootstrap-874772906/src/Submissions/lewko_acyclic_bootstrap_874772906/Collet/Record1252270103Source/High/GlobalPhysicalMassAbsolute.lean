/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Polynomial bounds for the actual modified first mass, used only outside
the bounded Mellin-height range. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalHighMass
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61InitialMass Record12518109Natural
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentOriginalCommonHarmonic CenteredMomentCanonicalFirst
local notation "O"=>HeckeFamily.O

private theorem mass_factor_coarse (reflected:Bool)(C Z B:ℝ)(bin:ℤ×(Fin 5→ℤ))
    (hZ:1≤Z)(hB:0≤B)(hlo:1≤2*geometryDCompensator bin)(hhi:geometryDCompensator bin≤Z^B):
    geometryHighFactor reflected C bin≤2*(C^2+1)*Z^B := by
  have hp:=geometryDCompensator_pos bin
  have hz:=Real.one_le_rpow hZ hB
  cases reflected
  · change 2*C^2*geometryDCompensator bin≤_
    nlinarith [mul_le_mul_of_nonneg_left hhi (sq_nonneg C)]
  · change (geometryDCompensator bin)⁻¹≤_
    have hi:(geometryDCompensator bin)⁻¹≤2:=by
      rw [←one_div]
      exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hlo)
    nlinarith [sq_nonneg C]

theorem actual_modified_mass_coarse {α:Type}[Fintype α][DecidableEq α]
    (reflected:Bool)(N:ℕ)(lo ap:ℝ)(hlo:0<lo)(hap:0<ap)
    (s:Input α)(modifier:CenteredMomentAddedZeroUniform.Tuple α→ℂ)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))
    (M Z ξ B ε:ℝ)(hZ:1<Z)(hK:0<Z^M)(hB:0≤B)(hε:0≤ε)
    (hcard:Fintype.card α≤N)(hlower:lo≤s.lower)(hs:Squarefree seed)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(hsource:sourceRadius s≤Z^B)
    (hs₁:∀x,s.W₁ x≠0→ap≤x)(hs₂:∀x,s.W₂ x≠0→ap≤x)
    (hA:|Real.logb Z (volume s.toData)|≤B)(bin:ℤ×(Fin 5→ℤ))
    (j:FirstColumnIndex (geometryFirstSource s modifier R seed (Z^M) Z ξ hK bin)):
    balancedFirstHighMass reflected s modifier R seed W M Z ξ ε hK bin j≤
      2*((geometrySupportConstant N lo ap ap)^2+1)*Z^(B*ε+6*B) := by
  have hn:=actual_geometry_norm_caps s modifier R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource j.1.val
  have hd:=actual_geometry_D_compensation s modifier R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource bin j.1
  have hdlo:1≤(j.1.val.1.val.2.absNorm:ℝ):=(hn 1).1
  have hg:=mass_factor_coarse reflected (geometrySupportConstant N lo ap ap) Z B bin hZ.le hB
    (by linarith [hd.2]) (hd.1.trans (hn 1).2)
  have hm:=actual_balanced_uniform_high_mass reflected N lo ap hlo hap s modifier R seed W M Z ξ B ε
    hZ hK hε hcard hlower hs hz₁ hz₂ hsource hs₁ hs₂ bin j
  have hb:=balanced_geometry_side_box reflected (Real.logb Z (volume s.toData)) B
    (geometryExponents s modifier R seed (Z^M) Z ξ j.1.val) hB hA (fun k=>
      ⟨Real.logb_nonneg hZ (hn k).1,
       (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (hn k).1)).mpr (hn k).2⟩)
  have hZ0:=zero_lt_one.trans hZ
  have hi:(Z^(balancedGeometrySide reflected (Real.logb Z (volume s.toData))
      (geometryExponents s modifier R seed (Z^M) Z ξ j.1.val)))⁻¹≤Z^(5*B):=by
    rw [←Real.rpow_neg hZ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [(abs_le.mp hb).1])
  calc
    _≤geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*ε)*
        (Z^(balancedGeometrySide reflected (Real.logb Z (volume s.toData))
          (geometryExponents s modifier R seed (Z^M) Z ξ j.1.val)))⁻¹ :=by
            simpa only [div_eq_mul_inv] using hm
    _≤(2*((geometrySupportConstant N lo ap ap)^2+1)*Z^B)*Z^(B*ε)*Z^(5*B):=by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hZ0.le _)
      · exact hi
      · positivity
      · positivity
    _=_:=by
      rw [show B*ε+6*B=B+B*ε+5*B by ring,Real.rpow_add hZ0,Real.rpow_add hZ0]
      ring

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_modified_mass_coarse
