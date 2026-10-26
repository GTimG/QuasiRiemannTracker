/- Genuine finite-buffer source-height threshold before all moving inputs.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeFiniteDaughterSource
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowSelected

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle153SourceSchedule
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CenteredMomentSecondHeightFamily Cycle63InitialMass
open Cycle153SourceUniform CenteredMomentSectorLocalization
open CenteredMomentEnergyBands Cycle63FinalLow Cycle63FinalNatural Cycle63FinalCapacity
open LocalMoment ConcretePrimeRowBridge CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentInductionEnergy
open CenteredMomentNaturalFixedRaySource

/-- The finite canonical buffer family is fixed before the source base.
Its true height ceiling fits the native source exponent at every actual
rebase. This is a threshold conclusion, not an assumed source gate. -/
theorem eventually_actual_canonical_buffer_high (e tau : ℝ)(htau : tau ≤ 1) :
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧ ∀ U : ℝ,(1/50:ℝ) ≤ U →
      ∀ buffer : BufferIndex e,
      (3+(3*buffer.1.val+2:ℕ)*(Z^U)^tau)^2 ≤ ((Z^U)^(31:ℝ))^(3:ℝ) :=by
  have hlocal : ∀ᶠ Y : ℝ in atTop,1 < Y ∧ ∀ buffer : BufferIndex e,
      (3+(3*buffer.1.val+2:ℕ)*Y^tau)^2 ≤ (Y^(31:ℝ))^(3:ℝ) :=by
    have hb : ∀ᶠ Y : ℝ in atTop,∀ buffer : BufferIndex e,
        ((3*buffer.1.val+2:ℕ):ℝ)+3 ≤ Y :=
      Filter.eventually_all.mpr (fun buffer=>eventually_ge_atTop
        ((((3*buffer.1.val+2:ℕ):ℝ))+3))
    filter_upwards [hb,eventually_gt_atTop (1:ℝ)] with Y hb hY
    refine ⟨hY,?_⟩
    intro buffer
    let c : ℝ := (3*buffer.1.val+2:ℕ)
    have hc : 0 ≤ c := Nat.cast_nonneg _
    have hpow : Y^tau ≤ Y :=by
      calc
        _ ≤ Y^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hY.le htau
        _ = Y := Real.rpow_one Y
    have ha : 3+c*Y^tau ≤ Y^2 :=by
      have hm:=mul_le_mul_of_nonneg_left hpow hc
      have hcb : c+3 ≤ Y :=hb buffer
      have hY0 : 0 ≤ Y :=(zero_lt_one.trans hY).le
      have hscale:=mul_le_mul_of_nonneg_right hcb hY0
      nlinarith only [hm,hscale,hY]
    change (3+c*Y^tau)^2 ≤ _
    calc
      _ ≤ (Y^2)^2 :=pow_le_pow_left₀ (by positivity) ha 2
      _ = Y^(4:ℝ) :=by rw [←pow_mul];norm_num [Real.rpow_natCast]
      _ ≤ Y^(93:ℝ) := Real.rpow_le_rpow_of_exponent_le hY.le (by norm_num)
      _ = (Y^(31:ℝ))^(3:ℝ) :=by
        rw [←Real.rpow_mul (zero_lt_one.trans hY).le]
        norm_num
  filter_upwards [eventually_all_rebased_sources _ hlocal] with Z hz
  exact ⟨hz.1,fun U hU=>(hz.2 U hU).2⟩

end
end OAI.SevenEighths.Cycle153SourceSchedule
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.eventually_actual_canonical_buffer_high
