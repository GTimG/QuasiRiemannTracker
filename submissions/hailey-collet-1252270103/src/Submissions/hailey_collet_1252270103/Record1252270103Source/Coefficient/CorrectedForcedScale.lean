/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Both powers of the actual marked control survive centered forced allocation. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.ForcedCost.CenteredScale
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedChildDictionary
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentAllocatedDetectorAmplitude
open QRH.Record1252270103Source.ForcedCost
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

lemma centered_power_square (L α : ℝ) :
    ((max 1 L)^(-α))^2=(max 1 L)^(-(2*α)) := by
  rw [←Real.rpow_mul_natCast (show (0:ℝ)≤max 1 L by positivity)]
  congr 1
  norm_num
  ring

def centeredEnergyScale (s : Input ι) (L α : ℝ) : ℝ :=
  slotControl s.toData^2*volume s*(max 1 L)^(-(2*α))

lemma centeredEnergyScale_nonneg (s : Input ι) (L α : ℝ) :
    0≤centeredEnergyScale s L α := by
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (volume_pos s).le)
    (Real.rpow_nonneg (by positivity) _)

theorem child_centered_energy_scale (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t L α : ℝ)
    (hP : ∀i,1≤s.P i) (hα0 : 0≤α) (hα : α<1/2) :
    centeredEnergyScale (child s C R B τ t) (L/ordinaryNorm B.val) α≤
      centeredEnergyScale s L α := by
  unfold centeredEnergyScale
  rw [mul_assoc,mul_assoc]
  exact mul_le_mul
    (pow_le_pow_left₀ (slotControl_nonneg (child s C R B τ t).toData)
      (child_slotControl s C R B τ t) 2)
    (child_centered_scale s C R B τ t L α hP hα0 hα)
    (mul_nonneg (volume_pos (child s C R B τ t)).le
      (Real.rpow_nonneg (by positivity) _)) (sq_nonneg _)

lemma centered_energy_factor (s : Input ι) (C L α : ℝ) :
    (C*(max 1 L)^(-α)*slotControl s.toData)^2*volume s=
      C^2*centeredEnergyScale s L α := by
  rw [mul_pow,mul_pow,centered_power_square]
  unfold centeredEnergyScale
  ring

theorem child_centered_energy_factor (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t L α K : ℝ)
    (hP : ∀i,1≤s.P i) (hα0 : 0≤α) (hα : α<1/2) :
    (K*(max 1 (L/ordinaryNorm B.val))^(-α)*slotControl (child s C R B τ t).toData)^2*
        volume (child s C R B τ t)≤
      (K*(max 1 L)^(-α)*slotControl s.toData)^2*volume s := by
  rw [centered_energy_factor,centered_energy_factor]
  exact mul_le_mul_of_nonneg_left
    (child_centered_energy_scale s C R B τ t L α hP hα0 hα) (sq_nonneg _)
end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.child_centered_energy_scale
#print axioms OAI.SevenEighths.Record1252270103Source.child_centered_energy_factor
