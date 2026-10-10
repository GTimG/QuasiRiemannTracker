import OAI.NumberTheory.DirichletL.Hecke.DetectorRowCount
import ZetaZeroFree.Exponent

/-!
The unmarked row minimax in §3.3, including explicit witness losses.
`card_bound_from_two_moments` converts two actual energy inequalities and two
spikes for the same finite set of rows into the manuscript's count exponent.
The analytic moment endpoints and the classification of actual rows remain
separate obligations; no estimate is postulated as a new axiom.
-/

namespace ZetaZeroFree.Analytic.Rows
noncomputable section
open scoped BigOperators
open OAI.SevenEighths

def t0 (δ : ℝ) : ℝ := 5 / (5 - 2 * δ)
def inverseExponent (r : ℝ) : ℝ := max 1 ((1 + 5 * r) / 6)

theorem t0_range {δ : ℝ} (hδ : 0 ≤ δ) (hδu : δ ≤ 5 / 6) :
    1 ≤ t0 δ ∧ t0 δ ≤ 3 / 2 := by
  have hd := Exponent.denominator_positive hδu
  unfold t0
  constructor
  · exact (le_div_iff₀ hd).2 (by linarith)
  · exact (div_le_iff₀ hd).2 (by linarith)

theorem t0_balance {δ : ℝ} (hδu : δ ≤ 5 / 6) :
    (1 + 5 * t0 δ) / 6 - δ * t0 δ = Exponent.R0 δ := by
  have hd := ne_of_gt (Exponent.denominator_positive hδu)
  unfold t0 Exponent.R0
  field_simp
  ring

theorem plain_balance {δ : ℝ} (hδu : δ ≤ 5 / 6) :
    1 - 2 * δ * t0 δ / 3 = Exponent.R0 δ := by
  have hd := ne_of_gt (Exponent.denominator_positive hδu)
  unfold t0 Exponent.R0
  field_simp
  ring

/-- Choosing `t0` before the common witnesses gives (3.15). -/
theorem unmarked_minimax {δ r m loss : ℝ}
    (hδ : 0 ≤ δ) (hδu : δ ≤ 5 / 6) (hloss : 0 ≤ loss)
    (hr : r ≤ t0 δ + loss) (hproduct : t0 δ - loss ≤ r + m) :
    min (inverseExponent r - δ * r) (1 - 2 * δ * m) ≤
      Exponent.R0 δ + 2 * loss := by
  have hplain := plain_balance hδu
  have hδone : δ ≤ 1 := by linarith
  by_cases hrone : r ≤ 1
  · have he : inverseExponent r = 1 := by
      unfold inverseExponent
      exact max_eq_left (by linarith)
    rw [he]
    by_cases hsplit : 2 * t0 δ / 3 ≤ r
    · have hmul := mul_nonneg hδ (sub_nonneg.mpr hsplit)
      have hbase : 1 - δ * r ≤ Exponent.R0 δ := by nlinarith
      exact (min_le_left _ _).trans (by linarith)
    · have hm : t0 δ / 3 - loss ≤ m := by linarith
      have hmul := mul_nonneg hδ (sub_nonneg.mpr hm)
      have hcost := mul_nonneg (sub_nonneg.mpr hδone) hloss
      have hbase : 1 - 2 * δ * m ≤ Exponent.R0 δ + 2 * loss := by
        nlinarith
      exact (min_le_right _ _).trans hbase
  · have he : inverseExponent r = (1 + 5 * r) / 6 := by
      unfold inverseExponent
      exact max_eq_right (by linarith)
    have hbalance := t0_balance hδu
    have hslope : 0 ≤ 5 / 6 - δ := by linarith
    have hmul := mul_nonneg hslope (sub_nonneg.mpr hr)
    have hcost := mul_nonneg (by linarith : 0 ≤ 1 - (5 / 6 - δ)) hloss
    rw [he]
    exact (min_le_left _ _).trans (by nlinarith)

/-- A finite-set count with both polynomials witnessing the same rows. -/
theorem card_bound_from_two_moments {α : Type*} (rows : Finset α)
    (M S : α → ℂ) (U δ r m lengthLoss spikeLoss momentLoss C : ℝ)
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδu : δ ≤ 5 / 6)
    (hlen : 0 ≤ lengthLoss) (hsp : 0 ≤ spikeLoss) (hC : 0 ≤ C)
    (hr : r ≤ t0 δ + lengthLoss) (hproduct : t0 δ - lengthLoss ≤ r + m)
    (hM : ∀ u ∈ rows, U ^ (δ * r - spikeLoss) ≤ ‖M u‖ ^ 2)
    (hS : ∀ u ∈ rows, U ^ (δ * m - spikeLoss) ≤ ‖S u‖ ^ 2)
    (hMenergy : ∑ u ∈ rows, ‖M u‖ ^ 2 ≤ C * U ^ (inverseExponent r + momentLoss))
    (hSenergy : ∑ u ∈ rows, ‖S u‖ ^ 4 ≤ C * U ^ (1 + momentLoss)) :
    (rows.card : ℝ) ≤ C * U ^ (Exponent.R0 δ +
      2 * lengthLoss + 2 * spikeLoss + momentLoss) := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hMi := HeckeDetectorRowCount.card_of_energy rows M U
    (δ * r - spikeLoss) (inverseExponent r + momentLoss) C hUp hM hMenergy
  have hSi : (rows.card : ℝ) ≤ C * U ^ (1 - 2 * δ * m + 2 * spikeLoss + momentLoss) := by
    have hspike (u : α) (hu : u ∈ rows) :
        U ^ (2 * (δ * m - spikeLoss)) ≤ ‖S u * S u‖ ^ 2 := by
      rw [show 2 * (δ * m - spikeLoss) = (δ * m - spikeLoss) +
        (δ * m - spikeLoss) by ring, Real.rpow_add hUp, norm_mul, mul_pow]
      exact mul_le_mul (hS u hu) (hS u hu) (Real.rpow_nonneg hUp.le _) (sq_nonneg _)
    have henergy : ∑ u ∈ rows, ‖S u * S u‖ ^ 2 ≤ C * U ^ (1 + momentLoss) := by
      simpa only [norm_mul, mul_pow, ← pow_add, show 2 + 2 = 4 by norm_num] using hSenergy
    have hh := HeckeDetectorRowCount.card_of_energy rows (fun u => S u * S u) U
      (2 * (δ * m - spikeLoss)) (1 + momentLoss) C hUp hspike henergy
    convert hh using 1
    congr 2
    ring
  have hcount : (rows.card : ℝ) ≤ C * U ^
      (min (inverseExponent r - δ * r) (1 - 2 * δ * m) + 2 * spikeLoss + momentLoss) := by
    by_cases hi : inverseExponent r - δ * r ≤ 1 - 2 * δ * m
    · rw [min_eq_left hi]
      apply hMi.trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow_of_exponent_le hU
      linarith
    · simpa only [min_eq_right (le_of_not_ge hi)] using hSi
  apply hcount.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  linarith [unmarked_minimax hδ hδu hlen hr hproduct]

end
end ZetaZeroFree.Analytic.Rows
