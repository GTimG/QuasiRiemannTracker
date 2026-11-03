/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAILowInverseNormalize.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowPhysicalInverseBound

namespace OAI

noncomputable section

namespace SevenEighths.ProbePhysical

open AsymmetricGeometry

lemma perturbed_low_inverse_power_cancel
    (Z d t α : ℝ) (hZ : 0 < Z) :
    Z ^ (5 / 6 - t - 2 * d + α) * (Z ^ d) ^ 2 /
      Z ^ (5 / 6 - t) = Z ^ α := by
  have hp : (Z ^ d) ^ 2 = Z ^ (2 * d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
    congr 1
    push_cast
    ring
  rw [hp, ← Real.rpow_add hZ, ← Real.rpow_sub hZ]
  congr 1
  ring

lemma perturbed_low_inverse_sqrt_normalized
    (q C B Z L d t α H E : ℝ) (n : ℕ)
    (hq : 0 < q) (hC : 0 ≤ C) (_hB : 0 ≤ B)
    (hZ : 0 < Z) (hL : 0 < L) (hH : 1 ≤ H)
    (hE : 0 ≤ E)
    (hEL : E ≤ C * H ^ n * Z ^ (5 / 6 - t - 2 * d + α))
    (hLB : L ≤ B * Z ^ d) :
    Real.sqrt E / Real.sqrt (q * Z ^ (5 / 6 - t) / L ^ 2) ≤
      Real.sqrt (C * B ^ 2 / q) * H ^ n * Z ^ (α / 2) := by
  have hratio : E / (q * Z ^ (5 / 6 - t) / L ^ 2) ≤
      (C * B ^ 2 / q) * H ^ n * Z ^ α := by
    calc
      _ ≤ (C * H ^ n * Z ^ (5 / 6 - t - 2 * d + α)) /
          (q * Z ^ (5 / 6 - t) / L ^ 2) :=
        div_le_div_of_nonneg_right hEL (by positivity)
      _ = (C * H ^ n * Z ^ (5 / 6 - t - 2 * d + α)) * L ^ 2 /
          (q * Z ^ (5 / 6 - t)) := by field_simp
      _ ≤ (C * H ^ n * Z ^ (5 / 6 - t - 2 * d + α)) *
          (B * Z ^ d) ^ 2 / (q * Z ^ (5 / 6 - t)) := by gcongr
      _ = (C * B ^ 2 / q) * H ^ n *
          (Z ^ (5 / 6 - t - 2 * d + α) * (Z ^ d) ^ 2 /
            Z ^ (5 / 6 - t)) := by ring
      _ = _ := by rw [perturbed_low_inverse_power_cancel Z d t α hZ]
  rw [← Real.sqrt_div hE]
  apply (Real.sqrt_le_sqrt hratio).trans
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have hp : Real.sqrt (Z ^ α) = Z ^ (α / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
    congr 1
    ring
  rw [hp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hH)))
      (by positivity)) (by positivity)

lemma perturbed_low_physical_scale_source
    (C : CalibrationData) (Z L t : ℝ) (hZ : 0 < Z) :
    lowPhysicalScale C (Z ^ (xBase - t / 2) / L)
      (Z ^ (yBase - t / 2) / L) =
      elementNorm C.generator * Z ^ (5 / 6 - t) / L ^ 2 := by
  unfold lowPhysicalScale
  have he : Z ^ (xBase - t / 2) * Z ^ (yBase - t / 2) =
      Z ^ (5 / 6 - t) := by
    rw [← Real.rpow_add hZ]
    congr 1
    dsimp only [xBase, yBase]
    ring
  rw [← he]
  ring

lemma perturbed_low_physical_scale_nominal_bound
    (C : CalibrationData) (Z L c d t : ℝ)
    (hZ : 0 < Z) (hc : 0 < c) (hL : c * Z ^ d ≤ L) :
    lowPhysicalScale C (Z ^ (xBase - t / 2) / L)
      (Z ^ (yBase - t / 2) / L) ≤
      (elementNorm C.generator / c ^ 2) *
        Z ^ (5 / 6 - t - 2 * d) := by
  have hl : 0 < L := lt_of_lt_of_le (by positivity) hL
  rw [perturbed_low_physical_scale_source C Z L t hZ]
  calc
    _ ≤ elementNorm C.generator * Z ^ (5 / 6 - t) /
        (c * Z ^ d) ^ 2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm; positivity)
        (by positivity) (pow_le_pow_left₀ (by positivity) hL 2)
    _ = _ := by
      have hp : (Z ^ d) ^ 2 = Z ^ (2 * d) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow, hp]
      calc
        _ = (elementNorm C.generator / c ^ 2) *
            (Z ^ (5 / 6 - t) / Z ^ (2 * d)) := by ring
        _ = _ := by
          rw [← Real.rpow_sub hZ]

end SevenEighths.ProbePhysical

end

end OAI
