/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/LocalFields/CubicConductorWeightedSums.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree

theorem kp_cubic_conductor_geometric_sum (q r : ℕ) (hq : 2 ≤ q) :
    let t : ℝ := (q : ℝ)⁻¹
    1 + (∑ i ∈ Finset.range r, 2 * ((q : ℝ) - 1) * t ^ (i + 2)) +
      2 * t ^ (r + 1) = 1 + 2 * t := by
  dsimp
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.succ_eq_add_one, pow_add, pow_one] at *
    field_simp at *
    nlinarith

theorem kp_cubic_conductor_weighted_sum (q r : ℕ) (hq : 2 ≤ q) :
    let t : ℝ := (q : ℝ)⁻¹
    (∑ i ∈ Finset.range r,
      (((q : ℝ) - 1) * (q : ℝ) ^ (2 * i) * t ^ (3 * i + 2) +
        ((q : ℝ) - 1) * (q : ℝ) ^ (2 * i + 1) * t ^ (3 * i + 3))) +
      2 * (q : ℝ) ^ (2 * r) * t ^ (3 * r + 1) = 2 / (q : ℝ) := by
  dsimp
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hp (n k : ℕ) :
      (q : ℝ) ^ n * (q : ℝ)⁻¹ ^ (n + k) = (q : ℝ)⁻¹ ^ k := by
    rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, one_mul]
  have hterm (i : ℕ) :
      ((q : ℝ) - 1) * (q : ℝ) ^ (2 * i) * (q : ℝ)⁻¹ ^ (3 * i + 2) +
        ((q : ℝ) - 1) * (q : ℝ) ^ (2 * i + 1) * (q : ℝ)⁻¹ ^ (3 * i + 3) =
      2 * ((q : ℝ) - 1) * (q : ℝ)⁻¹ ^ (i + 2) := by
    rw [show 3 * i + 2 = 2 * i + (i + 2) by omega,
      show 3 * i + 3 = (2 * i + 1) + (i + 2) by omega]
    simp only [mul_assoc, hp]
    ring
  simp_rw [hterm]
  rw [show 3 * r + 1 = 2 * r + (r + 1) by omega, mul_assoc, hp]
  have h := kp_cubic_conductor_geometric_sum q r hq
  dsimp at h
  rw [div_eq_mul_inv]
  linarith

end DedekindZetaZeroFree
