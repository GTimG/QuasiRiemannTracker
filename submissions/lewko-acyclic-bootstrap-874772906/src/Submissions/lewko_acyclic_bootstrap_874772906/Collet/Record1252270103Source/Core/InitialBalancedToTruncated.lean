/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialRegularToTruncatedBalancedContract
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalNestedHeights
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialRegularToTruncated
noncomputable section
open OAI OAI.SevenEighths Filter HeckeFamily CanonicalQuadraticSieve
open scoped Classical BigOperators SchwartzMap ContDiff
open QRH.Record1252270103Low Record1252270103Finite Record1252270103StepScalar
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open Cycle61InitialMass ConcretePrimeRowBridge
open High.CoupledFirst High.GlobalPhysical FirstTruncatedHeights InitialTruncated
local notation "O"=>HeckeFamily.O

theorem truncated_of_balanced (K:ℚ)(n low:Source)(b mesh ξ width:ℝ)
    (hg:RealGeometry K n low b)
    (h:BalancedInitialSupplier K n low b mesh ξ width) :
    FixedSubsetTruncatedSupplier (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) (crossing n low:ℝ)
      (K:ℝ) mesh ξ 0 b width := by
  intro α instα decα rayM instRay H hH W hW hsW bΦ hbΦ η η₀ Q hQr hQ0 hQt hQ72 R₀ hR T
  obtain ⟨degree,S,hS,C,τ,hC,hτ,hbound⟩:=h T rayM H hH W hW hsW bΦ hbΦ η η₀ Q hQr hQ0 hQt hQ72 R₀ hR
  let A:ℝ:=2+2*Real.pi
  let D:ℝ:=geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)
  let F:ℝ:=max 1 (2*D^2)
  have hA:0<A:=by dsimp only [A];positivity
  have hF:0<F:=zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨degree,S,hS,C*F*A^degree,τ/2,by positivity,by positivity,?_⟩
  filter_upwards [hbound,(tendsto_rpow_atTop (show 0<τ/2 by positivity)).eventually
    (eventually_ge_atTop A)] with Z hz hAZ
  intro hZ θ w v t height hwp hwm hh hv hext p X₁ X₂ hX₁ hX₂ hadm hcross hwlo hwhi r hl₁ hl₂
    Y₂ Y₁ hY₂ hY₁ hprod s
  intro key hkey reflected u v' huv
  let V:ℝ:=(1+‖u‖)*(1+‖v'‖)*(1+|t|+height)
  let ht:ℝ:=mellinShift t reflected u v'
  have hZ0:0<Z:=zero_lt_one.trans hZ
  have hE:1≤1+|t|+height:=by linarith [abs_nonneg t]
  have hV1:1≤V:=by
    simpa only [one_mul,mellinPairHeight,V] using mul_le_mul (mellin_pair_height_one u v') hE
      zero_le_one (zero_le_one.trans (mellin_pair_height_one u v'))
  have hV0:0≤V:=zero_le_one.trans hV1
  have hExt:1+|t|+height≤V:=by
    exact le_mul_of_one_le_left (by linarith [abs_nonneg t]) (mellin_pair_height_one u v')
  have hshift:1+|ht|+height≤A*V:=by
    have hs:=literal_mellin_shift_height t height u v' reflected hh
    have hs : 1+|ht|+height≤mellinShiftConstant*V := by
      simpa only [ht,V,mellinPairHeight,mul_assoc] using hs
    exact hs.trans (mul_le_mul_of_nonneg_right (by dsimp [A,mellinShiftConstant];linarith) hV0)
  have hgate:1+|t|+|ht|+height≤Z^τ:=by
    have htV:|t|≤V:=by linarith [hExt]
    have hs:=literal_mellin_shift_height t height u v' reflected hh
    have hs : 1+|ht|+height≤mellinShiftConstant*V := by
      simpa only [ht,V,mellinPairHeight,mul_assoc] using hs
    have hb:1+|t|+|ht|+height≤A*V:=by dsimp [A,mellinShiftConstant] at *;linarith
    apply hb.trans
    have hc:=mul_le_mul hAZ huv hV0 (Real.rpow_nonneg hZ0.le _)
    simpa only [←Real.rpow_add hZ0,add_halves] using hc
  have hy₂:1≤Y₂:=Real.one_le_rpow hZ.le hg.reference_pos.le
  have hb:=hz.2 hZ θ w v t ht height hwp hwm hh hv hgate p X₁ X₂ hX₁ hX₂ hadm hcross hwlo hwhi
    hy₂ hl₁ hl₂ reflected key
  have hpow:(1+|ht|+height)^degree≤(A*V)^degree:=
    pow_le_pow_left₀ (by linarith [abs_nonneg ht]) hshift degree
  have hgeom:=high_factor_balanced D ((p.control S)^2) (sq_nonneg _) key reflected
  have hside:0≤geometryHighFactor reflected D key:=(geometry_high_factor_pos reflected D key
    (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  apply hb.trans
  have hp:=mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (mul_nonneg hC.le (sq_nonneg (p.control S))) hside)
  have hg':=mul_le_mul_of_nonneg_left hgeom hC.le
  have hq:=mul_le_mul_of_nonneg_right hg' (pow_nonneg (mul_nonneg hA.le hV0) degree)
  apply hp.trans
  apply (show C*(p.control S)^2*geometryHighFactor reflected D key*(A*V)^degree≤
      C*(if reflected then F*(p.control S)^2/geometryDCompensator key
        else F*(p.control S)^2*geometryDCompensator key)*(A*V)^degree from by
      convert hq using 1 <;> ring).trans_eq
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true,Real.rpow_zero,mul_one,mul_pow] <;>
    simp only [V,mul_pow] <;> ring
end
end QRH.Record1252270103Source.InitialRegularToTruncated
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.truncated_of_balanced
