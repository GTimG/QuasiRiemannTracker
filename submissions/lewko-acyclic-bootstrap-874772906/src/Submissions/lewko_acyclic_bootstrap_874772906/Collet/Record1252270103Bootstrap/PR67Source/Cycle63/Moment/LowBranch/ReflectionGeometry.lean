import Mathlib
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- A child that exceeds the old capacity by at most `δ` and whose reflected state has margin `δ` has, after deleting
primes of the puncture from its plain scales, either old capacity or a reflected state with old capacity.
Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section

/-- A shift of a nonnegative amount raises the clipped value by at most that amount. -/
theorem max_zero_add_le {y a : ℝ} (ha : 0 ≤ a) : max 0 (y + a) ≤ max 0 y + a :=
  max_le (by linarith [le_max_left 0 y]) (by linarith [le_max_right 0 y])

/-- A deleted version of a child that exceeds the old capacity by at most `δ`, with its second plain factor reflectable
with margin `δ`, has old capacity itself or a reflected version with old capacity and bounded lengths. -/
theorem deleted_reflection_cases {W ξ δ κ z zF x₁ x₂ a₁ a₂ : ℝ}
    (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (hz : 0 ≤ z) (hzF : zF ≤ z) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hover : max 0 x₁ + max 0 x₂ + 6 * κ * z ≤ W + δ)
    (hrefl : max 0 (W - x₂ + ξ) + max 0 x₁ + 6 * κ * z + δ ≤ W) :
    max 0 (x₁ - a₁) + max 0 (x₂ - a₂) + 6 * κ * zF ≤ W ∨
    (a₂ ≤ δ ∧ ξ ≤ x₂ - a₂ ∧
      max 0 (W - (x₂ - a₂) + ξ) + max 0 (x₁ - a₁) + 6 * κ * zF ≤ W ∧
      max 0 (W - (x₂ - a₂) + ξ) ≤ W ∧ max 0 (x₁ - a₁) ≤ W) := by
  have hslot : 6 * κ * zF ≤ 6 * κ * z := mul_le_mul_of_nonneg_left hzF (by positivity)
  have hz6 : 0 ≤ 6 * κ * z := by positivity
  have h1 : 0 ≤ max 0 x₁ := le_max_left _ _
  have h2 : 0 ≤ max 0 (W - x₂ + ξ) := le_max_left _ _
  have h3 : W - x₂ + ξ ≤ max 0 (W - x₂ + ξ) := le_max_right _ _
  have hx₁ : max 0 (x₁ - a₁) ≤ max 0 x₁ := max_le_max le_rfl (by linarith)
  by_cases ha : a₂ ≤ δ
  · right
    have hshift : max 0 (W - (x₂ - a₂) + ξ) ≤ max 0 (W - x₂ + ξ) + a₂ := by
      have := max_zero_add_le (y := W - x₂ + ξ) ha₂
      rwa [show W - (x₂ - a₂) + ξ = W - x₂ + ξ + a₂ by ring]
    refine ⟨ha, by linarith, by linarith, by linarith, by linarith⟩
  · left
    have ha' : δ < a₂ := not_le.mp ha
    by_cases hx : a₂ ≤ x₂
    · have h4 : max 0 (x₂ - a₂) = x₂ - a₂ := max_eq_right (by linarith)
      have h5 : max 0 x₂ = x₂ := max_eq_right (by linarith)
      rw [h5] at hover
      rw [h4]
      linarith
    · have hx' : x₂ < a₂ := not_le.mp hx
      have h4 : max 0 (x₂ - a₂) = 0 := max_eq_left (by linarith)
      rw [h4]
      linarith

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
