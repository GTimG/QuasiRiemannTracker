import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Finite-row inequalities for the weighted physical numerator.

These are unconditional inequalities about the actual finite sums.  In particular, the
selected prime factors occur inside the fourth moment with exponent two, not four.
-/

noncomputable section
open scoped BigOperators
namespace WeightedQRH.Numerator

theorem sum_fourth_le_card_cube {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 4 := by
  have h₁ := Finset.sum_mul_sq_le_sq_mul_sq s f (fun _ => (1 : ℝ))
  have h₂ := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => f i ^ 2) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h₁ h₂
  have h₁' : ((∑ i ∈ s, f i) ^ 2) ^ 2 ≤
      ((∑ i ∈ s, f i ^ 2) * (s.card : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ (sq_nonneg _) h₁ 2
  have h₂' := mul_le_mul_of_nonneg_right h₂ (sq_nonneg (s.card : ℝ))
  simp only [← pow_mul] at h₂
  calc
    _ ≤ ((∑ i ∈ s, f i ^ 2) * (s.card : ℝ)) ^ 2 := by
      simpa only [← pow_mul] using h₁'
    _ = (s.card : ℝ) ^ 2 * (∑ i ∈ s, f i ^ 2) ^ 2 := by ring
    _ ≤ (s.card : ℝ) ^ 2 * ((∑ i ∈ s, f i ^ 4) * (s.card : ℝ)) :=
      mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
    _ = _ := by ring

/-- The exact fourth-power form of the weighted Hölder step.  Only a pointwise lower
bound for the selected prime product is required. -/
theorem weighted_row_holder {ι : Type*} (s : Finset ι) (S Q : ι → ℂ)
    (L : ℝ) (hL : 0 ≤ L) (hQ : ∀ i ∈ s, L ≤ ‖Q i‖) :
    L ^ 2 * (∑ i ∈ s, ‖S i‖) ^ 4 ≤
      (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4 * ‖Q i‖ ^ 2 := by
  calc
    _ ≤ L ^ 2 * ((s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4) :=
      mul_le_mul_of_nonneg_left (sum_fourth_le_card_cube s (fun i => ‖S i‖))
        (sq_nonneg _)
    _ = (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4 * L ^ 2 := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL (hQ i hi) 2)
        (by positivity)

/-- Full prime factors may be removed using their upper amplitude bound, while the
selected factors remain in the fourth moment. -/
theorem weighted_row_holder_with_full {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (L A : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hQ : ∀ i ∈ s, L ≤ ‖Q i‖) (hP : ∀ i ∈ s, ‖P i‖ ≤ A) :
    L ^ 2 * (∑ i ∈ s, ‖S i * P i‖) ^ 4 ≤
      A ^ 4 * (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4 * ‖Q i‖ ^ 2 := by
  have hsum : (∑ i ∈ s, ‖S i * P i‖) ≤ A * ∑ i ∈ s, ‖S i‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul, mul_comm A]
    exact mul_le_mul_of_nonneg_left (hP i hi) (norm_nonneg _)
  calc
    _ ≤ L ^ 2 * (A * ∑ i ∈ s, ‖S i‖) ^ 4 := by
      gcongr
    _ = A ^ 4 * (L ^ 2 * (∑ i ∈ s, ‖S i‖) ^ 4) := by ring
    _ ≤ A ^ 4 * ((s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4 * ‖Q i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (weighted_row_holder s S Q L hL hQ) (by positivity)
    _ = _ := by ring

end WeightedQRH.Numerator
