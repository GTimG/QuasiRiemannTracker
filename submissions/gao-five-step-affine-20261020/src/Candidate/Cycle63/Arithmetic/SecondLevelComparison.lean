/- The comparison daughter of a state of the second step: the plain lengths of the comparison and the two
inequalities of its capacity, from the facts of the position of the state and its overshoot. Released under
Apache 2.0. -/
import Candidate.Cycle63.Arithmetic.SecondLevelFamily

set_option autoImplicit false

namespace Cycle63

noncomputable section
open Cycle63.Optimization

/-- The comparison of the plain factors of a state, in any unit `W`. Let the plain lengths `x₁`, `x₂` and the slot
length `z` of a state of width `W` lie at a position whose facts hold (`hfacts`, a statement about the ratios `x/W`),
let the state exceed the old capacity by at most `δ` (`hF`), let the margin `δ` and a slack `ξ` of the reflection be at
most a hundredth of the width (`hmargin`, `hδW`), and let `Lc = W * secondComparisonLength (x₁/W) (x₂/W) (z/W)` be the
comparison length. Then the plain lengths are positive with sum at most `W`, and the comparison pair of lengths `Lc`
and `x₁ + x₂ - Lc` has the lengths in `[0, W/4]` and `[0, W]`, exceeds the unit by at most the margin `δ`, and its
reflected state (the long factor reflected) has the margin `δ`:

* `Lc + (x₁ + x₂ - Lc) + 6 slotPrice z ≤ W + δ`;
* `max 0 (W - (x₁ + x₂ - Lc) + ξ) + Lc + 6 slotPrice z + δ ≤ W`.

These are the two inequalities of the energy bound of a state that exceeds the old capacity by at most `δ` and whose
reflected state has margin `δ`, for the plain factors `Z^Lc` and `Z^(x₁ + x₂ - Lc)` and the slots of length `z`. The
statement is invariant under the change of base `Z ↦ Z^W`, which divides the lengths and the width by `W`. -/
theorem comparison_core_of_facts {G : ℕ} {x₁ x₂ z W δ ξ Lc : ℝ} (hG : 0 < G) (hz : 0 ≤ z) (hW : 0 < W)
    (hfacts : (childPosition (1 / G) (x₁ / W) (x₂ / W) (z / W)).Facts)
    (hF : x₁ + x₂ + 6 * slotPrice * z - W ≤ δ) (hmargin : δ + ξ ≤ W / 100) (hδW : δ ≤ W / 100)
    (hLc : Lc = W * secondComparisonLength (x₁ / W) (x₂ / W) (z / W)) :
    0 < x₁ ∧ 0 < x₂ ∧ x₁ + x₂ ≤ W ∧ 0 ≤ Lc ∧ Lc ≤ W / 4 ∧ 0 ≤ x₁ + x₂ - Lc ∧
      Lc + (x₁ + x₂ - Lc) + 6 * slotPrice * z ≤ W + δ ∧
      max 0 (W - (x₁ + x₂ - Lc) + ξ) + Lc + 6 * slotPrice * z + δ ≤ W := by
  have hg : (0 : ℝ) < 1 / G := by
    have : (0 : ℝ) < G := by exact_mod_cast hG
    positivity
  have hκ := slotPrice_bounds
  have hslope := secondSlope_bounds
  -- the plain lengths are positive and below the unit
  have hmin : 0 < min (x₁ / W) (x₂ / W) := lt_of_lt_of_le hfacts.windowBottom_pos (gridDown_le hg _)
  have hx₁ : 0 < x₁ := (div_pos_iff_of_pos_right hW).mp (lt_of_lt_of_le hmin (min_le_left _ _))
  have hx₂ : 0 < x₂ := (div_pos_iff_of_pos_right hW).mp (lt_of_lt_of_le hmin (min_le_right _ _))
  have hI : x₁ / W + x₂ / W + secondSlope * (z / W) ≤ 1 := (le_gridUp hg _).trans hfacts.intercept_le_one
  have hsum : x₁ + x₂ ≤ W := by
    have h1 := mul_le_mul_of_nonneg_left hI hW.le
    have hW0 : W ≠ 0 := hW.ne'
    have h2 : W * (x₁ / W + x₂ / W + secondSlope * (z / W)) = x₁ + x₂ + secondSlope * z := by
      field_simp
    have h3 : 0 ≤ secondSlope * z := mul_nonneg (by linarith only [hslope.1]) hz
    linarith only [h1, h2, h3]
  -- the comparison length is nonnegative: the reflected daughter fits in the old region
  have hcl0 : 0 ≤ secondComparisonLength (x₁ / W) (x₂ / W) (z / W) := by
    have hge := secondComparisonLength_ge (childPosition_window (n₁ := x₁ / W) (n₂ := x₂ / W) (ζ := z / W) hg)
    refine le_trans (le_min (by norm_num) ?_) hge
    have := hfacts.comparison_room
    linarith
  have hLc0 : 0 ≤ Lc := by
    rw [hLc]
    exact mul_nonneg hW.le hcl0
  -- the two bounds of the definition of the comparison length
  have hc1 : secondComparisonLength (x₁ / W) (x₂ / W) (z / W) ≤ 1 / 4 := min_le_left _ _
  have hc2 : secondComparisonLength (x₁ / W) (x₂ / W) (z / W) ≤
      (x₁ / W + x₂ / W - (9 / 2) * (z / W) - 1 / 100) / 2 := min_le_right _ _
  have hLc1 : Lc ≤ W / 4 := by
    rw [hLc]
    calc W * secondComparisonLength (x₁ / W) (x₂ / W) (z / W) ≤ W * (1 / 4) :=
          mul_le_mul_of_nonneg_left hc1 hW.le
      _ = W / 4 := by ring
  have hLc2 : 2 * Lc ≤ x₁ + x₂ - (9 / 2) * z - W / 100 := by
    rw [hLc]
    have h1 := mul_le_mul_of_nonneg_left hc2 hW.le
    have hW0 : W ≠ 0 := hW.ne'
    have h2 : W * ((x₁ / W + x₂ / W - (9 / 2) * (z / W) - 1 / 100) / 2) =
        (x₁ + x₂ - (9 / 2) * z - W / 100) / 2 := by
      field_simp
    linarith only [h1, h2]
  have hκz : 6 * slotPrice * z ≤ (9 / 2) * z := by
    have := mul_le_mul_of_nonneg_right hκ.2 hz
    linarith only [this]
  refine ⟨hx₁, hx₂, hsum, hLc0, hLc1, ?_, ?_, ?_⟩
  · linarith only [hLc2, hLc0, hz, hW]
  · linarith only [hF]
  · rcases le_total 0 (W - (x₁ + x₂ - Lc) + ξ) with h0 | h0
    · rw [max_eq_right h0]
      linarith only [hLc2, hmargin, hκz]
    · rw [max_eq_left h0]
      linarith only [hLc2, hF, hκz, hz, hδW, hW]

/-- The comparison of the plain factors of a state of the second step, in the unit of the state. Under the arithmetic
conditions of the second step, with a slack `ξ ≤ 1/1000` of the reflection, the plain lengths and the comparison pair
have the properties of `comparison_core_of_facts` for the margin `δ = 7/2500`. -/
theorem SecondStepArithmetic.comparison_core {G : ℕ} {lossFloor width x₁ x₂ z W length amp loss ξ Lc : ℝ}
    (hG : 0 < G) (hz : 0 ≤ z) (h : SecondStepArithmetic G lossFloor width x₁ x₂ z W length amp loss)
    (hξ : ξ ≤ 1 / 1000) (hLc : Lc = W * secondComparisonLength (x₁ / W) (x₂ / W) (z / W)) :
    0 < x₁ ∧ 0 < x₂ ∧ x₁ + x₂ ≤ W ∧ 0 ≤ Lc ∧ Lc ≤ W / 4 ∧ 0 ≤ x₁ + x₂ - Lc ∧
      Lc + (x₁ + x₂ - Lc) + 6 * slotPrice * z ≤ W + 7 / 2500 ∧
      max 0 (W - (x₁ + x₂ - Lc) + ξ) + Lc + 6 * slotPrice * z + 7 / 2500 ≤ W := by
  obtain ⟨-, hfloor, hfacts, -, -, -, hover⟩ := h
  have hW2 : 2 / 5 ≤ W := hfloor
  exact comparison_core_of_facts hG hz (by linarith only [hW2]) hfacts hover (by linarith only [hξ, hW2])
    (by linarith only [hW2]) hLc

end

end Cycle63
