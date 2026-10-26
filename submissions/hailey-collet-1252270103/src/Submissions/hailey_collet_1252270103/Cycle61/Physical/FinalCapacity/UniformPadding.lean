import Submissions.hailey_collet_1252270103.Cycle61.Physical.FinalCapacity.Final

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61FinalCapacity
noncomputable section
open scoped BigOperators
open Filter

/-- A common threshold pays the fixed support costs before every live input,
 allocation, row, height and nominal exponent. -/
theorem support_padding_eventually (N : ℕ) (b b₁ b₂ ε : ℝ)
    (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧ supportPadding N b b₁ b₂ Z ≤ ε := by
  let A := b^(2*N)*(max 1 b₁*max 1 b₂)
  have hA : 0 < A := by dsimp [A]; positivity
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) A,
    Filter.eventually_gt_atTop (1:ℝ)] with Z hAZ hZ
  refine ⟨hZ,?_⟩
  have hh := Real.logb_le_logb_of_le hZ hA hAZ
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  dsimp [A] at hh
  rw [Real.logb_mul (pow_pos hb _).ne' (by positivity),Real.logb_pow] at hh
  unfold supportPadding
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hh
  exact hh

/-- Compact positive mass intervals permit the same threshold to pay an
 arbitrarily small error proportional to the live original mass. -/
theorem support_padding_eventually_mass (N : ℕ) (b b₁ b₂ ε Mmin : ℝ)
    (hb : 0 < b) (hε : 0 < ε) (hMmin : 0 < Mmin) :
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧ ∀M:ℝ,Mmin ≤ M → supportPadding N b b₁ b₂ Z ≤ ε*M := by
  filter_upwards [support_padding_eventually N b b₁ b₂ (ε*Mmin) hb (mul_pos hε hMmin)]
    with Z hZ
  exact ⟨hZ.1,fun M hM => hZ.2.trans (mul_le_mul_of_nonneg_left hM hε.le)⟩

#print axioms support_padding_eventually
#print axioms support_padding_eventually_mass
end
end OAI.SevenEighths.Cycle61FinalCapacity
