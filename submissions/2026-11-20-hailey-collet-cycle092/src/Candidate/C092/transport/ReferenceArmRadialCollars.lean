/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal log_U(3) opened-length collar is paid by a fixed early threshold. -/
import Candidate.C092.transport.ReferenceArmRadialEither
set_option autoImplicit false
namespace QRH.Cycle092.ReferenceArmRadial
noncomputable section
open Filter OAI.SevenEighths.CenteredMomentEnergyBands

 theorem eventual_opened_arm_caps :
    ∀ᶠ U : ℝ in atTop, 1<U ∧ ∀ X Y : ℝ,0<X → 0<Y →
      length U X≤(23/200:ℝ)+length U 3 →
      length U Y≤(18023/25000:ℝ)+length U 3 →
      X≤U^shortCap ∧ Y≤U := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/1000000)).eventually
    (eventually_ge_atTop (3:ℝ))
  filter_upwards [ht,eventually_gt_atTop (1:ℝ)] with U ht hU
  refine ⟨hU,?_⟩
  intro X Y hX hY hx hy
  have hu : 0<U := zero_lt_one.trans hU
  have hthree : U^(length U 3)=(3:ℝ) := by
    norm_num only [length,show max (1:ℝ) 3=3 by norm_num]
    exact Real.rpow_logb hu hU.ne' (by norm_num)
  have hrepr (Z:ℝ) : Z≤U^(length U Z) := by
    rw [length,Real.rpow_logb hu hU.ne' (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  have hbound (Z b:ℝ) (hZ:0<Z) (hz:length U Z≤b+length U 3) :
      Z≤U^(b+1/1000000) := by
    apply (hrepr Z).trans
    apply (Real.rpow_le_rpow_of_exponent_le hU.le hz).trans
    rw [Real.rpow_add hu,Real.rpow_add hu,hthree]
    exact mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hu.le _)
  refine ⟨hbound X (23/200) hX hx,?_⟩
  apply (hbound Y (18023/25000) hY hy).trans
  simpa only [Real.rpow_one,longCap] using Real.rpow_le_rpow_of_exponent_le hU.le genuine_short_capacity.2.2.2.2.le

end
end QRH.Cycle092.ReferenceArmRadial
#print axioms QRH.Cycle092.ReferenceArmRadial.eventual_opened_arm_caps
