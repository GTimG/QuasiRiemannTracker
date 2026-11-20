/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform authentic Poisson gates on the actual reference arm, with its collar. -/
import Candidate.C092.transport.ReferenceArmRadialGeometry
import Candidate.C092.transport.ReferenceShortP3Gates
set_option autoImplicit false
namespace QRH.Cycle092.ReferenceArmRadial
noncomputable section
open scoped BigOperators
open Filter QRH.Cycle092.ReferenceShortP3

theorem uniform_arm_gates :
    ∀ᶠ U : ℝ in atTop, 1≤ U ∧
    ∀ {Slot : Type} [Fintype Slot] (w : Slot→ℝ) (X V : ℝ),
    0≤ X → X≤ U^shortCap → (∑i,w i)≤ widthCap →
    X^2*(∏i,U^(w i))^2≤ U^(2:ℝ) ∧
    4*((X^2*(∏i,U^(w i))^2)^2/U^(max V markedRadius))*U^(cutoffBuffer/2)<1 := by
  filter_upwards [eventually_short_cutoff genuine_short_capacity.1] with U hU
  refine ⟨hU.1,?_⟩
  intro Slot _ w X V hX hshort hslots
  have hv := original_fourth_volume_le w hU.1 hX hshort hslots
  refine ⟨hv.trans (Real.rpow_le_rpow_of_exponent_le hU.1 ?_),?_⟩
  · norm_num [shortCap,widthCap]
  have hcut := short_cutoff_of_power hU.1 (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hv rfl hU.2
  have hp : 0< U^markedRadius := Real.rpow_pos_of_pos (zero_lt_one.trans_le hU.1) _
  have hm : U^markedRadius≤ U^(max V markedRadius) :=
    Real.rpow_le_rpow_of_exponent_le hU.1 (le_max_right _ _)
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (sq_nonneg _) hp hm) (by norm_num))
    (Real.rpow_nonneg (zero_le_one.trans hU.1) _)) hcut

end
end QRH.Cycle092.ReferenceArmRadial
#print axioms QRH.Cycle092.ReferenceArmRadial.uniform_arm_gates
