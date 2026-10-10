import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Coefficient removal and capacity damping.  The selected-slot capacity here uses
the original fixed value κ = 3/4. -/
noncomputable section
open scoped BigOperators
namespace WeightedQRH.Numerator

/-- Removing a finite row-dependent coefficient expansion before taking a moment. -/
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

/-- The genuine weighted-mass combination, with its necessary nonnegativity. -/
theorem max_weighted_mass_nonneg {ι : Type*} (s : Finset ι) (a t : ι → ℝ)
    (B C : ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (ht : ∀ i ∈ s, 0 ≤ t i)
    (hcentral : ∑ i ∈ s, a i ≤ B)
    (hleft : ∑ i ∈ s, a i * t i ≤ C) :
    ∑ i ∈ s, a i * max 1 (t i) ≤ B + C := by
  calc
    _ ≤ ∑ i ∈ s, a i * (1 + t i) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (ha i hi)
      exact max_le (by linarith [ht i hi]) (by linarith)
    _ = (∑ i ∈ s, a i) + ∑ i ∈ s, a i * t i := by
      simp_rw [mul_add, mul_one, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add hcentral hleft

def selectedCapacity (z v : ℝ) : ℝ := max 0 (z - 4 * v / 9)

/-- Exact capacity damping, with a strictly positive residual saving when δ>0 and
v>0.  This is the analytic reason large coefficient dilations do not destroy the
weighted-moment gain. -/
theorem capacity_damping (delta q z v : ℝ) (hq : 0 ≤ q)
    (hqdelta : q ≤ delta / 2) (hv : 0 ≤ v) :
    -delta * v / 4 - q * selectedCapacity z v / 2 ≤
      -q * z / 2 - 5 * delta * v / 36 := by
  have hcap : z - 4 * v / 9 ≤ selectedCapacity z v := le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_left hcap hq
  have hqv := mul_le_mul_of_nonneg_right hqdelta hv
  nlinarith

theorem capacity_damping_weak (delta q z v : ℝ) (hdelta : 0 ≤ delta)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta / 2) (hv : 0 ≤ v) :
    -delta * v / 4 - q * selectedCapacity z v / 2 ≤ -q * z / 2 := by
  have h := capacity_damping delta q z v hq hqdelta hv
  have := mul_nonneg hdelta hv
  linarith

theorem capacity_feasible (n z v : ℝ) (hbase : 2 * n + (9 / 2) * z ≤ 1)
    (hbranch : 0 ≤ z - 4 * v / 9) :
    2 * (n + v) + (9 / 2) * selectedCapacity z v ≤ 1 := by
  rw [selectedCapacity, max_eq_right hbranch]
  linarith

end WeightedQRH.Numerator
