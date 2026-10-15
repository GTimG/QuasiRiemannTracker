import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Variable-κ conductor damping for the Cycle25 physical numerator.

The finite coefficient-removal argument is adapted from
akashlevy/QuasiRiemannTracker, commit
2fd60c0926b66ea18d7436f5ed55250fd006ab5d,
WeightedQRH/NumeratorDamping.lean (Apache-2.0).

These are scalar and finite-sum lemmas. Their use in a physical moment still
requires the actual coefficient/conductor dictionary, which is not an axiom
or an implicit hypothesis of this file.
-/

noncomputable section
open scoped BigOperators

namespace Cycle25.Numerator

def selectedCapacity (κ z t : ℝ) : ℝ := max 0 (z - t / (3 * κ))

theorem selectedCapacity_nonneg (κ z t : ℝ) : 0 ≤ selectedCapacity κ z t :=
  le_max_left _ _

theorem capacity_damping {κ δ q z t : ℝ}
    (hκ : 0 < κ) (hq : 0 ≤ q) (hqδ : q ≤ δ / 2) (ht : 0 ≤ t) :
    -δ * t / 4 - q * selectedCapacity κ z t / 2 ≤
      -q * z / 2 - δ * t * (1 / 4 - 1 / (12 * κ)) := by
  have hcap : z - t / (3 * κ) ≤ selectedCapacity κ z t := le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_left hcap hq
  have hqt := mul_le_mul_of_nonneg_right hqδ ht
  have hcost : q * t / (3 * κ) ≤ δ * t / (6 * κ) := by
    calc
      _ ≤ (δ / 2) * t / (3 * κ) := div_le_div_of_nonneg_right hqt (by positivity)
      _ = _ := by field_simp; ring
  have hmul' : q * z - q * t / (3 * κ) ≤ q * selectedCapacity κ z t := by
    nlinarith [show q * (z - t / (3 * κ)) = q * z - q * t / (3 * κ) by ring]
  have hidentity : δ * t * (1 / 4 - 1 / (12 * κ)) =
      δ * t / 4 - (δ * t / (6 * κ)) / 2 := by field_simp; ring
  rw [hidentity]
  linarith

theorem damping_reserve {κ : ℝ} (hκ : 7 / 10 ≤ κ) :
    11 / 84 ≤ 1 / 4 - 1 / (12 * κ) := by
  have hκpos : 0 < κ := by linarith
  have hfrac : 1 / (12 * κ) ≤ 5 / 42 := by
    apply (div_le_iff₀ (show 0 < 12 * κ by positivity)).2
    linarith
  linarith

theorem capacity_damping_uniform {κ δ q z t : ℝ}
    (hκ : 7 / 10 ≤ κ) (hq : 0 ≤ q) (hqδ : q ≤ δ / 2) (ht : 0 ≤ t) :
    -δ * t / 4 - q * selectedCapacity κ z t / 2 ≤
      -q * z / 2 - 11 * δ * t / 84 := by
  have hδ : 0 ≤ δ := by linarith
  have h := capacity_damping (by linarith : 0 < κ) hq hqδ ht (z := z)
  have hr := mul_le_mul_of_nonneg_left (damping_reserve hκ) (mul_nonneg hδ ht)
  nlinarith

theorem capacity_damping_weak {κ δ q z t : ℝ}
    (hκ : 7 / 10 ≤ κ) (hq : 0 ≤ q) (hqδ : q ≤ δ / 2) (ht : 0 ≤ t) :
    -δ * t / 4 - q * selectedCapacity κ z t / 2 ≤ -q * z / 2 := by
  have hδ : 0 ≤ δ := by linarith
  have h := capacity_damping_uniform hκ hq hqδ ht (z := z)
  have := mul_nonneg hδ ht
  linarith

theorem capacity_feasible {κ n z t : ℝ} (hκ : 0 < κ)
    (hbase : 2 * n + 6 * κ * z ≤ 1) (hbranch : 0 ≤ z - t / (3 * κ)) :
    2 * (n + t) + 6 * κ * selectedCapacity κ z t ≤ 1 := by
  rw [selectedCapacity, max_eq_right hbranch]
  have hid : 2 * (n + t) + 6 * κ * (z - t / (3 * κ)) = 2 * n + 6 * κ * z := by
    field_simp
    nlinarith [ne_of_gt hκ]
  rw [hid]
  exact hbase

/-- Remove the finite row-dependent coefficient expansion before applying a
common moment estimate. The weighted mass remains an explicit proved input. -/
theorem coefficient_mass_removal {ι : Type*} (s : Finset ι) (A S : ι → ℂ)
    (w : ι → ℝ) (M B : ℝ) (hM : 0 ≤ M)
    (hmass : ∑ i ∈ s, ‖A i‖ * w i ≤ B)
    (hS : ∀ i ∈ s, ‖S i‖ ≤ M * w i) :
    ‖∑ i ∈ s, A i * S i‖ ≤ M * B := by
  calc
    _ ≤ ∑ i ∈ s, ‖A i * S i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖A i‖ * (M * w i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hS i hi) (norm_nonneg _)
    _ = M * ∑ i ∈ s, ‖A i‖ * w i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ M * B := mul_le_mul_of_nonneg_left hmass hM

end Cycle25.Numerator
