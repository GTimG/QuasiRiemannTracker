/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighTailScales.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily
open AsymmetricGeometry

lemma small_source_scale_with_perturbed_lengths {K : ℕ} (Z : ℝ) (hZ : 0 < Z)
    (length : Fin K → ℝ) (t β e : ℝ)
    (hlength : ∑ i, length i = (1 / 6 : ℝ) + t) :
    (∏ i, (Z ^ (length i)) ^ (17 / 50 : ℝ)) *
      ((Z ^ (xBase - t / 2 : ℝ)) ^ (1 / 2 - (17 / 50 : ℝ)) *
        Z ^ (β + 8 * e + (17 / 50 : ℝ) - 1) *
        (Z ^ (yBase - t / 2 : ℝ)) ^ ((1 / 2 : ℝ) - 1)) =
      Z ^ (β + signalOffset + 49 * skew / 150 - 79 / 800 + 8 * e + 51 * t / 100) := by
  rw [physical_scale_power Z hZ, hlength]
  congr 1
  simp only [xBase, yBase, signalOffset]
  ring

lemma small_row_scale_bound_with_perturbed_lengths {K : ℕ}
    (Z U δ t : ℝ) (hZ : 1 ≤ Z) (hU : 1 ≤ U)
    (hUsmall : U ≤ Z ^ (1 / 100 : ℝ)) (_hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2)
    (length : Fin K → ℝ) (hlength : ∑ i, length i = (1 / 6 : ℝ) + t)
    (β e : ℝ) :
    U ^ (8 / 5 + δ - (17 / 50 : ℝ)) * (∏ i, (Z ^ (length i)) ^ (17 / 50 : ℝ)) *
      ((Z ^ (xBase - t / 2 : ℝ)) ^ (1 / 2 - (17 / 50 : ℝ)) *
        Z ^ (β + 8 * e + (17 / 50 : ℝ) - 1) *
        (Z ^ (yBase - t / 2 : ℝ)) ^ ((1 / 2 : ℝ) - 1)) ≤
      Z ^ (β + signalOffset + 49 * skew / 150 - 63 / 800 + 8 * e + 51 * t / 100) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hrow : U ^ (8 / 5 + δ - (17 / 50 : ℝ)) ≤ Z ^ (1 / 50 : ℝ) := by
    calc
      _ ≤ U ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
      _ ≤ (Z ^ (1 / 100 : ℝ)) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hUsmall (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hZ0.le]; norm_num
  rw [mul_assoc, small_source_scale_with_perturbed_lengths Z hZ0 length t β e hlength]
  calc
    _ ≤ Z ^ (1 / 50 : ℝ) * Z ^ (β + signalOffset + 49 * skew / 150 - 79 / 800 + 8 * e + 51 * t / 100) :=
      mul_le_mul_of_nonneg_right hrow (Real.rpow_nonneg hZ0.le _)
    _ = _ := by rw [← Real.rpow_add hZ0]; congr 1; ring

lemma large_source_scale_with_perturbed_lengths {K : ℕ} (Z : ℝ) (hZ : 0 < Z)
    (length : Fin K → ℝ) (t r : ℝ)
    (hlength : ∑ i, length i = (1 / 6 : ℝ) + t) :
    (∏ i, (Z ^ (length i)) ^ r) *
      ((Z ^ (xBase - t / 2 : ℝ)) ^ (1 / 2 - r) * Z ^ (2 + r - 1) *
        (Z ^ (yBase - t / 2 : ℝ)) ^ ((2 : ℝ) - 1)) =
      Z ^ ((53 / 32 : ℝ)-skew/2 + rowBase * r + (3 * r / 2 - 3 / 4) * t) := by
  rw [physical_scale_power Z hZ, hlength]
  congr 1
  simp only [xBase, yBase, rowBase]
  ring

lemma rewrite_large_geometric_scale (Z sourceBase rowBase ζ δ r : ℝ)
    (hZ : 0 < Z) (n : ℕ) :
    Z ^ (sourceBase + rowBase * r) *
      (Z ^ (rowBase + ζ) * (2 : ℝ) ^ n) ^ (8 / 5 + δ - r) =
      Z ^ (sourceBase + (rowBase + ζ) * (8 / 5 + δ) - ζ * r) *
        ((2 : ℝ) ^ (8 / 5 + δ - r)) ^ n := by
  rw [Real.mul_rpow (Real.rpow_nonneg hZ.le _) (by positivity),
    ← Real.rpow_mul hZ.le]
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
    mul_comm (n : ℝ), Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← mul_assoc, ← Real.rpow_add hZ]
  congr 2
  ring

lemma show_large_geometric_summable (Z sourceBase rowBase ζ δ r : ℝ)
    (hZ : 0 < Z) (hr : 8 / 5 + δ < r) :
    Summable (fun n : ℕ => Z ^ (sourceBase + rowBase * r) *
      (Z ^ (rowBase + ζ) * (2 : ℝ) ^ n) ^ (8 / 5 + δ - r)) := by
  simp_rw [rewrite_large_geometric_scale Z sourceBase rowBase ζ δ r hZ]
  exact (summable_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).mul_left _

lemma sum_large_geometric_scale (Z sourceBase rowBase ζ δ r : ℝ)
    (hZ : 0 < Z) (hr : 8 / 5 + δ < r) :
    (∑' n : ℕ, Z ^ (sourceBase + rowBase * r) *
      (Z ^ (rowBase + ζ) * (2 : ℝ) ^ n) ^ (8 / 5 + δ - r)) =
      Z ^ (sourceBase + (rowBase + ζ) * (8 / 5 + δ) - ζ * r) *
        (1 - (2 : ℝ) ^ (8 / 5 + δ - r))⁻¹ := by
  simp_rw [rewrite_large_geometric_scale Z sourceBase rowBase ζ δ r hZ]
  rw [tsum_mul_left, tsum_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))]

end SevenEighths.ProbeHighRowFamily
end

end OAI
