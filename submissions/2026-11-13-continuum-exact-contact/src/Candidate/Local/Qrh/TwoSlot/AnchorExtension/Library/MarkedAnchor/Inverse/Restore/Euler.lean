/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Mathlib

/-!
# Inverse.Restore.Euler — the required/avoided prime Euler factor with a profile

Generic finite identities behind the reciprocal Euler factor of a required prime (the reciprocal
Euler series with `p` required to occur is the unrestricted reciprocal times `-X_p/(1-X_p)`),
stated for a profiled squarefree
column, where the Euler product is not available and the factor `1/(1-X_p)` becomes a finite
recursion in the column scale.

For weights `c i` (the prime factor `-ψ(p) χ_p(y) / √(N p)` including the Möbius sign) and norms
`n i`, the profiled column on a finite set `S` at scale `X` is
`col S X = ∑_{A ⊆ S} (∏_{i∈A} c i) Φ((∏_{i∈A} n i)/X)`.

* `col_insert`: `col (insert p S) X = col S X + c p · col S (X / n p)` (`p` avoided / required).
* `col_avoid_expand`: `col S X = ∑_{j<J} (-c p)^j col (insert p S) (X / n p^j)
  + (-c p)^J col S (X / n p^J)` — the truncated geometric series `1/(1-X_p)`.
* `col_eq_zero_of_small`: the column vanishes at scales `X < 1/b` (profile supported in `[a,b]`,
  norms `≥ 1`), so the remainder vanishes for `J` large (`col_avoid_finite`).
* `col_required`: the `p`-required part `col (insert p S) X - col S X = c p · col S (X/n p)`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- The profiled squarefree column on `S` at scale `X`. -/
def col (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (S : Finset ι) (X : ℝ) : ℂ :=
  ∑ A ∈ S.powerset, (∏ i ∈ A, c i) * Φ ((∏ i ∈ A, n i) / X)

omit [DecidableEq ι] in
theorem col_empty (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (X : ℝ) :
    col c n Φ ∅ X = Φ (1 / X) := by
  simp [col]

/-- Splitting off one prime: avoided part plus required part (scale divided by `n p`). -/
theorem col_insert (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (S : Finset ι) (p : ι)
    (hp : p ∉ S) (_hn : n p ≠ 0) (X : ℝ) :
    col c n Φ (insert p S) X = col c n Φ S X + c p * col c n Φ S (X / n p) := by
  unfold col
  rw [Finset.sum_powerset_insert hp, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  have hpA : p ∉ A := fun h => hp (Finset.mem_powerset.mp hA h)
  rw [Finset.prod_insert hpA, Finset.prod_insert hpA]
  have : n p * (∏ i ∈ A, n i) / X = (∏ i ∈ A, n i) / (X / n p) := by
    rw [div_div_eq_mul_div]; ring
  rw [this]; ring

/-- The `p`-required part of the column. -/
theorem col_required (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (S : Finset ι) (p : ι)
    (hp : p ∉ S) (hn : n p ≠ 0) (X : ℝ) :
    col c n Φ (insert p S) X - col c n Φ S X = c p * col c n Φ S (X / n p) := by
  rw [col_insert c n Φ S p hp hn X]; ring

/-- The truncated geometric series: avoiding `p` costs `∑_j (-c p)^j` at scales `X / n p^j`. -/
theorem col_avoid_expand (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (S : Finset ι) (p : ι)
    (hp : p ∉ S) (hn : n p ≠ 0) (J : ℕ) (X : ℝ) :
    col c n Φ S X = ∑ j ∈ Finset.range J, (-c p)^j * col c n Φ (insert p S) (X / n p ^ j) +
      (-c p)^J * col c n Φ S (X / n p ^ J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [ih, Finset.sum_range_succ]
    have h := col_insert c n Φ S p hp hn (X / n p ^ J)
    have hs : X / n p ^ J / n p = X / n p ^ (J+1) := by
      rw [div_div, pow_succ]
    rw [hs] at h
    have : col c n Φ S (X / n p ^ J) =
        col c n Φ (insert p S) (X / n p ^ J) - c p * col c n Φ S (X / n p ^ (J+1)) := by
      rw [h]; ring
    rw [this, pow_succ]
    ring

/-- The column vanishes below the profile support: if `Φ` vanishes on `(b, ∞)` and all norms are
`≥ 1`, then `col S X = 0` for `0 < X`, `b * X < 1`. -/
theorem col_eq_zero_of_small (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (b : ℝ)
    (hΦ : ∀ x, b < x → Φ x = 0) (hn : ∀ i, 1 ≤ n i) (S : Finset ι) (X : ℝ)
    (hX : 0 < X) (hbX : b * X < 1) : col c n Φ S X = 0 := by
  unfold col
  apply Finset.sum_eq_zero
  intro A _
  have h1 : 1 ≤ ∏ i ∈ A, n i := by
    have h : (∏ _i ∈ A, (1:ℝ)) ≤ ∏ i ∈ A, n i := by
      gcongr with i _
      exact hn i
    simpa using h
  rw [hΦ, mul_zero]
  rw [lt_div_iff₀ hX]
  linarith

/-- Finite form of `1/(1-X_p)`: for `J` with `b X < n p^J` the remainder vanishes. -/
theorem col_avoid_finite (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (b : ℝ)
    (hΦ : ∀ x, b < x → Φ x = 0) (hn : ∀ i, 1 ≤ n i) (S : Finset ι) (p : ι) (hp : p ∉ S)
    (J : ℕ) (X : ℝ) (hX : 0 < X) (hJ : b * X < n p ^ J) :
    col c n Φ S X = ∑ j ∈ Finset.range J, (-c p)^j * col c n Φ (insert p S) (X / n p ^ j) := by
  have hnp : 0 < n p := lt_of_lt_of_le one_pos (hn p)
  rw [col_avoid_expand c n Φ S p hp hnp.ne' J X]
  have hpow : 0 < n p ^ J := pow_pos hnp J
  rw [col_eq_zero_of_small c n Φ b hΦ hn S (X / n p ^ J) (div_pos hX hpow) ?_]
  · ring
  · rw [mul_div_assoc', div_lt_one hpow]; exact hJ

/-- Absolute central mass of the geometric series: `∑_{j<J} ‖c p‖^j ≤ 1/(1-‖c p‖)`. -/
theorem geom_mass_le (c : ℂ) (hc : ‖c‖ < 1) (J : ℕ) :
    ∑ j ∈ Finset.range J, ‖c‖^j ≤ (1 - ‖c‖)⁻¹ := by
  have h0 : 0 ≤ ‖c‖ := norm_nonneg c
  rw [geom_sum_eq (ne_of_lt hc) J]
  have h1 : 0 < 1 - ‖c‖ := by linarith
  have : (‖c‖^J - 1) / (‖c‖ - 1) = (1 - ‖c‖^J) / (1 - ‖c‖) := by
    rw [← neg_div_neg_eq]; ring_nf
  rw [this, div_le_iff₀ h1, inv_mul_cancel₀ h1.ne']
  have : 0 ≤ ‖c‖^J := pow_nonneg h0 J
  linarith

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.col_avoid_finite
