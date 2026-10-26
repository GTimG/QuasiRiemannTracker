/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.SourceContextFactory
import Candidate.Research.RecursiveAffine.PhysicalMaskBridge

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Cycle153SourceSchedule
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Filter Set Cycle153Reachable Cycle153.RegionalSchedule
open Cycle63InitialMass

/-- Fixed source and mask constants are absorbed uniformly at every
actual child base Z^U, U>=1/50. The cutoff precedes U and all source rows. -/
theorem eventually_rebased_fixed_log (C eps : ℝ) (heps : 0<eps) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀U : ℝ,(1/50:ℝ)≤U →
      Real.logb (Z^U) (max 1 C)≤eps := by
  have hp : 0<(1/50:ℝ)*eps := by positivity
  filter_upwards [(tendsto_rpow_atTop hp).eventually (eventually_ge_atTop (max 1 C)),
    eventually_gt_atTop (1:ℝ)] with Z hC hZ
  refine ⟨hZ,?_⟩
  intro U hU
  have hu : 0<U := by linarith only [hU]
  have hlocal : 1<Z^U := Real.one_lt_rpow hZ hu
  apply (Real.logb_le_iff_le_rpow hlocal (by positivity : 0< max 1 C)).mpr
  rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
  exact hC.trans (Real.rpow_le_rpow_of_exponent_le hZ.le
    (mul_le_mul_of_nonneg_right hU heps.le))

/-- One actual threshold absorbs the complete finite collection of fixed
source costs before the moving natural state, profile and history. -/
theorem eventually_rebased_fixed_costs {I : Type} [Fintype I]
    (cost : I→ℝ) (eps : ℝ) (heps : 0<eps) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀U : ℝ,(1/50:ℝ)≤U →
      ∀i,Real.logb (Z^U) (max 1 (cost i))≤eps := by
  filter_upwards [Filter.eventually_all.2 (fun i=>eventually_rebased_fixed_log (cost i) eps heps),
    eventually_gt_atTop (1:ℝ)] with Z h hZ
  exact ⟨hZ,fun U hU i=>(h i).2 U hU⟩

/-- A fixed nonnegative native norm can be used literally, including
zero, instead of replacing the physical logarithm by a new scale. -/
theorem eventually_rebased_native_fixed_log (C eps : ℝ) (hC : 0≤C) (heps : 0<eps) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀U : ℝ,(1/50:ℝ)≤U →
      Real.logb (Z^U) C≤eps := by
  filter_upwards [eventually_rebased_fixed_log C eps heps] with Z hz
  refine ⟨hz.1,?_⟩
  intro U hU
  rcases eq_or_lt_of_le hC with hzero | hpositive
  · rw [←hzero,Real.logb_zero]
    exact heps.le
  · have hlocal : 1<Z^U := Real.one_lt_rpow hz.1 (by linarith only [hU])
    have hlog : Real.logb (Z^U) C≤Real.logb (Z^U) (max 1 C) := by
      unfold Real.logb
      exact div_le_div_of_nonneg_right
        (Real.log_le_log hpositive (le_max_right _ _)) (Real.log_pos hlocal).le
    exact hlog.trans (hz.2 U hU)

/-- The true fixed-parent state has row scale1 and additional character
width log_Z Norm(eta.modulus). This is absorbed at the new native mu;
its width is never replaced by1. A genuine fixed conductor/phase cost
is absorbed at the same threshold, before moving sources and heights. -/
theorem eventually_root_fixed_source_fit (etaSeed : Character) (fixedPhaseCost : ℝ) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
      1+Real.logb Z (etaSeed.modulus.absNorm:ℝ)≤1+nativeMu/16 ∧
      Real.logb Z (max 1 fixedPhaseCost)≤nativeMu/1024 := by
  filter_upwards [eventually_rebased_native_fixed_log (etaSeed.modulus.absNorm:ℝ)
      (nativeMu/16) (Nat.cast_nonneg _) (div_pos nativeMu_pos (by norm_num)),
    eventually_rebased_fixed_log fixedPhaseCost (nativeMu/1024)
      (div_pos nativeMu_pos (by norm_num))] with Z heta hphase
  have he:=heta.2 1 (by norm_num : (1/50:ℝ)≤1)
  have hp:=hphase.2 1 (by norm_num : (1/50:ℝ)≤1)
  rw [Real.rpow_one] at he hp
  exact ⟨heta.1,by linarith only [he],hp⟩

def logPadRate (N : ℕ) : ℝ := 1/((10:ℝ)^22*(2*(N:ℝ)+2))

theorem logPadRate_pos (N : ℕ) : 0<logPadRate N := by
  unfold logPadRate
  positivity

/-- The finite pad used by the actual physical coordinate constructors is
small at every actual source base and for every surviving cardinality.
The source profile upper bound is the fixed native9/4, not a moving
profile seminorm. Its residual products are handled monotonically. -/
theorem eventually_actual_native_pad (N : ℕ) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀U : ℝ,(1/50:ℝ)≤U →
      ∀n : ℕ,n≤N → ∀b b1 b2 : ℝ,1≤b → b≤9/4 → b1≤9/4 → b2≤9/4 →
      Real.logb (Z^U) 128+252/(gridSize:ℝ)+
        2*(n:ℝ)*Real.logb (Z^U) b+
        Real.logb (Z^U) (max 1 b1*max 1 b2)≤1/(10:ℝ)^20 := by
  filter_upwards [eventually_rebased_fixed_log 128 (logPadRate N) (logPadRate_pos N),
    eventually_rebased_fixed_log (9/4) (logPadRate N) (logPadRate_pos N),
    eventually_rebased_fixed_log (81/16) (logPadRate N) (logPadRate_pos N)] with Z h1 h2 h3
  refine ⟨h1.1,?_⟩
  intro U hU n hn b b1 b2 hbpos hb hb1 hb2
  have hlocal : 1<Z^U := Real.one_lt_rpow h1.1 (by linarith only [hU])
  have h128 := h1.2 U hU
  have hb0 := h2.2 U hU
  have hp0 : Real.logb (Z^U) ((9/4:ℝ)^2)≤logPadRate N := by
    simpa only [show max (1:ℝ) (81/16)=81/16 by norm_num,
      show ((9/4:ℝ)^2)=81/16 by norm_num] using h3.2 U hU
  rw [show max (1:ℝ) 128=128 by norm_num] at h128
  rw [show max (1:ℝ) (9/4)=9/4 by norm_num] at hb0
  have hblog : Real.logb (Z^U) b≤Real.logb (Z^U) (9/4) := by
    unfold Real.logb
    exact div_le_div_of_nonneg_right (Real.log_le_log (zero_lt_one.trans_le hbpos) hb)
      (Real.log_pos hlocal).le
  have hprodpos : 0< max 1 b1*max 1 b2 := by positivity
  have hprod : max 1 b1*max 1 b2≤(9/4:ℝ)^2 := by
    have h1 : max 1 b1≤(9/4:ℝ) := max_le (by norm_num) hb1
    have h2 : max 1 b2≤(9/4:ℝ) := max_le (by norm_num) hb2
    nlinarith [mul_le_mul h1 h2 (by positivity : 0≤ max 1 b2) (by norm_num : (0:ℝ)≤9/4)]
  have hplog : Real.logb (Z^U) (max 1 b1*max 1 b2)≤logPadRate N := by
    apply le_trans _ hp0
    unfold Real.logb
    exact div_le_div_of_nonneg_right (Real.log_le_log hprodpos hprod) (Real.log_pos hlocal).le
  have hnb : 2*(n:ℝ)*Real.logb (Z^U) b≤2*(n:ℝ)*logPadRate N :=
    mul_le_mul_of_nonneg_left (hblog.trans hb0) (by positivity)
  have hcast : (n:ℝ)≤N := by exact_mod_cast hn
  have hsize : 2*(n:ℝ)*logPadRate N≤2*(N:ℝ)*logPadRate N := by
    nlinarith only [mul_le_mul_of_nonneg_right hcast (logPadRate_pos N).le]
  have heq : (2*(N:ℝ)+2)*logPadRate N=1/(10:ℝ)^22 := by
    unfold logPadRate
    field_simp
  have hg : 252/(gridSize:ℝ)+(1/(10:ℝ)^22)≤1/(10:ℝ)^20 := by
    norm_num [gridSize]
  nlinarith only [h128,hplog,hnb,hsize,heq,hg]
end
end OAI.SevenEighths.Cycle153SourceSchedule
