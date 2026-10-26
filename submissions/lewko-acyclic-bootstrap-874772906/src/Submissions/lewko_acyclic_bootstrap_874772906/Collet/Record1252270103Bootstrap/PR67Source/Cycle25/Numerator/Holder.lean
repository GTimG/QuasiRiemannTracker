import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.NumeratorHolder
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-! Finite-row inequalities for the weighted physical numerator.

These are unconditional inequalities about the actual finite sums.  In particular, the
selected prime factors occur inside the fourth moment with exponent two, not four.
-/

noncomputable section
open scoped BigOperators
namespace Cycle25.Numerator

/-- Full prime factors may be removed using their upper amplitude bound, while the
selected factors remain in the fourth moment. -/
theorem weighted_row_holder_with_full {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (L A : ℝ) (hL : 0 ≤ L) (_hA : 0 ≤ A)
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
      mul_le_mul_of_nonneg_left (WeightedQRH.Numerator.weighted_row_holder s S Q L hL hQ) (by positivity)
    _ = _ := by ring

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/

end
end Record1252270103Bootstrap.PR67
