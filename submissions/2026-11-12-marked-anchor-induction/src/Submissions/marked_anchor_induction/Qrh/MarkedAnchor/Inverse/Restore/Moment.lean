/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Euler

/-!
# Inverse.Restore.Moment — restoring avoided primes in a row moment (generic)

Rows `y` range over a finset `Y`; the prime weights `c y i` depend on the row but are bounded
uniformly, `‖c y p‖ ≤ κ p < 1`. If the column on `S ∪ T` has moment `≤ B` at every scale
`s ∈ (0, X]`, then the column on `S` (the primes of `T` avoided: punctures, mask primes,
required slot primes) has moment `≤ (∏_{p∈T} (1-κ p)^{-2}) · B` at every scale in `(0, X]`.
This is the reciprocal Euler factor ("unrestricted reciprocal times `1/(1-X_p)`") in moment form, via
`Euler.col_avoid_finite` and a weighted Cauchy–Schwarz over the geometric series.

* `norm_sum_sq_le_weighted` — `‖∑ w_j v_j‖² ≤ (∑ W_j)(∑ W_j ‖v_j‖²)` for `‖w_j‖ ≤ W_j`.
* `moment_avoid_one`, **`moment_avoid`**.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped BigOperators

/-- Weighted Cauchy–Schwarz. -/
theorem norm_sum_sq_le_weighted {α : Type*} (s : Finset α) (w v : α → ℂ) (W : α → ℝ)
    (hW : ∀ j ∈ s, ‖w j‖ ≤ W j) :
    ‖∑ j ∈ s, w j * v j‖^2 ≤ (∑ j ∈ s, W j) * ∑ j ∈ s, W j * ‖v j‖^2 := by
  have hW0 : ∀ j ∈ s, 0 ≤ W j := fun j hj => (norm_nonneg _).trans (hW j hj)
  have h1 : ‖∑ j ∈ s, w j * v j‖ ≤ ∑ j ∈ s, Real.sqrt (W j) * (Real.sqrt (W j) * ‖v j‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [norm_mul, ← mul_assoc, Real.mul_self_sqrt (hW0 j hj)]
    exact mul_le_mul_of_nonneg_right (hW j hj) (norm_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun j => Real.sqrt (W j))
    (fun j => Real.sqrt (W j) * ‖v j‖)
  have h0 : 0 ≤ ‖∑ j ∈ s, w j * v j‖ := norm_nonneg _
  have e1 : ∑ j ∈ s, Real.sqrt (W j)^2 = ∑ j ∈ s, W j :=
    Finset.sum_congr rfl fun j hj => Real.sq_sqrt (hW0 j hj)
  have e2 : ∑ j ∈ s, (Real.sqrt (W j) * ‖v j‖)^2 = ∑ j ∈ s, W j * ‖v j‖^2 :=
    Finset.sum_congr rfl fun j hj => by rw [mul_pow, Real.sq_sqrt (hW0 j hj)]
  rw [e1, e2] at hcs
  calc ‖∑ j ∈ s, w j * v j‖^2 ≤ (∑ j ∈ s, Real.sqrt (W j) * (Real.sqrt (W j) * ‖v j‖))^2 :=
        pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := hcs

variable {ι ρ : Type*} [DecidableEq ι]

theorem geom_real_le (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ < 1) (J : ℕ) :
    ∑ j ∈ Finset.range J, κ^j ≤ (1-κ)⁻¹ := by
  have h1 : 0 < 1 - κ := by linarith
  have h := geom_sum_mul_neg κ J
  have hJ : 0 ≤ κ^J := pow_nonneg hκ0 J
  calc ∑ j ∈ Finset.range J, κ^j
      = (∑ j ∈ Finset.range J, κ^j) * (1-κ) * (1-κ)⁻¹ := by field_simp
    _ ≤ 1 * (1-κ)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr h1.le)
        rw [h]; linarith
    _ = (1-κ)⁻¹ := one_mul _

/-- One avoided prime. -/
theorem moment_avoid_one (c : ρ → ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (b : ℝ)
    (hΦ : ∀ x, b < x → Φ x = 0) (hn : ∀ i, 1 ≤ n i) (Y : Finset ρ) (S : Finset ι) (p : ι)
    (hp : p ∉ S) (hnp : 1 < n p) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ < 1)
    (hc : ∀ y ∈ Y, ‖c y p‖ ≤ κ)
    (X B : ℝ) (hB : ∀ s, 0 < s → s ≤ X → ∑ y ∈ Y, ‖col (c y) n Φ (insert p S) s‖^2 ≤ B) :
    ∀ s, 0 < s → s ≤ X → ∑ y ∈ Y, ‖col (c y) n Φ S s‖^2 ≤ ((1-κ)⁻¹)^2 * B := by
  intro s hs hsX
  have hB0 : 0 ≤ B := (Finset.sum_nonneg fun y _ => sq_nonneg _).trans (hB s hs hsX)
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (b * s) hnp
  have hnp0 : 0 < n p := lt_trans one_pos hnp
  set G := ∑ j ∈ Finset.range J, κ^j with hG
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun j _ => pow_nonneg hκ0 j
  have hGle : G ≤ (1-κ)⁻¹ := geom_real_le κ hκ0 hκ J
  have hscale : ∀ j, 0 < s / n p ^ j ∧ s / n p ^ j ≤ X := by
    intro j
    have hpj : 1 ≤ n p ^ j := one_le_pow₀ hnp.le
    refine ⟨div_pos hs (pow_pos hnp0 j), ?_⟩
    exact (div_le_self hs.le hpj).trans hsX
  have hy : ∀ y ∈ Y, ‖col (c y) n Φ S s‖^2 ≤
      G * ∑ j ∈ Finset.range J, κ^j * ‖col (c y) n Φ (insert p S) (s / n p ^ j)‖^2 := by
    intro y hyY
    rw [col_avoid_finite (c y) n Φ b hΦ hn S p hp J s hs hJ]
    apply norm_sum_sq_le_weighted
    intro j _
    rw [norm_pow, norm_neg]
    exact pow_le_pow_left₀ (norm_nonneg _) (hc y hyY) j
  calc ∑ y ∈ Y, ‖col (c y) n Φ S s‖^2
      ≤ ∑ y ∈ Y, G * ∑ j ∈ Finset.range J, κ^j * ‖col (c y) n Φ (insert p S) (s / n p ^ j)‖^2 :=
        Finset.sum_le_sum hy
    _ = G * ∑ j ∈ Finset.range J, κ^j * ∑ y ∈ Y, ‖col (c y) n Φ (insert p S) (s / n p ^ j)‖^2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
    _ ≤ G * ∑ j ∈ Finset.range J, κ^j * B := by
        apply mul_le_mul_of_nonneg_left _ hG0
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hB _ (hscale j).1 (hscale j).2) (pow_nonneg hκ0 j)
    _ = G * G * B := by rw [← Finset.sum_mul]; ring
    _ ≤ (1-κ)⁻¹ * (1-κ)⁻¹ * B := by
        apply mul_le_mul_of_nonneg_right _ hB0
        exact mul_le_mul hGle hGle hG0 (hG0.trans hGle)
    _ = ((1-κ)⁻¹)^2 * B := by ring

/-- **Restoring a set `T` of avoided primes** in the row moment. -/
theorem moment_avoid (c : ρ → ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (b : ℝ)
    (hΦ : ∀ x, b < x → Φ x = 0) (hn : ∀ i, 1 ≤ n i) (Y : Finset ρ) (κ : ι → ℝ)
    (T : Finset ι) (hT : ∀ p ∈ T, 1 < n p ∧ 0 ≤ κ p ∧ κ p < 1 ∧ ∀ y ∈ Y, ‖c y p‖ ≤ κ p)
    (S : Finset ι) (hST : Disjoint S T) (X B : ℝ)
    (hB : ∀ s, 0 < s → s ≤ X → ∑ y ∈ Y, ‖col (c y) n Φ (S ∪ T) s‖^2 ≤ B) :
    ∀ s, 0 < s → s ≤ X →
      ∑ y ∈ Y, ‖col (c y) n Φ S s‖^2 ≤ (∏ p ∈ T, ((1-κ p)⁻¹)^2) * B := by
  induction T using Finset.induction_on generalizing S B with
  | empty => simpa using hB
  | @insert p T hpT ih =>
    have hp := hT p (Finset.mem_insert_self p T)
    have hT' : ∀ q ∈ T, 1 < n q ∧ 0 ≤ κ q ∧ κ q < 1 ∧ ∀ y ∈ Y, ‖c y q‖ ≤ κ q :=
      fun q hq => hT q (Finset.mem_insert_of_mem hq)
    have hpS : p ∉ S := fun h => Finset.disjoint_left.mp hST h (Finset.mem_insert_self p T)
    have hST' : Disjoint (insert p S) T := by
      rw [Finset.disjoint_insert_left]
      exact ⟨hpT, Finset.disjoint_of_subset_right (Finset.subset_insert p T) hST⟩
    have hB' : ∀ s, 0 < s → s ≤ X → ∑ y ∈ Y, ‖col (c y) n Φ (insert p S ∪ T) s‖^2 ≤ B := by
      intro s hs hsX
      have : insert p S ∪ T = S ∪ insert p T := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      rw [this]; exact hB s hs hsX
    have h1 := ih hT' (insert p S) hST' B hB'
    have h2 := moment_avoid_one c n Φ b hΦ hn Y S p hpS hp.1 (κ p) hp.2.1 hp.2.2.1 hp.2.2.2 X _ h1
    intro s hs hsX
    rw [Finset.prod_insert hpT]
    calc _ ≤ ((1-κ p)⁻¹)^2 * ((∏ q ∈ T, ((1-κ q)⁻¹)^2) * B) := h2 s hs hsX
      _ = _ := by ring

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.moment_avoid
