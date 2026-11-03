/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighPrincipalScale.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalRemainderBounds
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbePrincipalRemainderBounds

lemma perturbed_source_scale_identity {ι : Type*} (J : Finset ι)
    (ell : ι → ℝ) (t Z a ξ υ : ℝ)
    (hell : ∑ j ∈ J, ell j = 1 / 6 + t) (hZ : 0 < Z) :
    scalePower (Z ^ (AsymmetricGeometry.xBase - t / 2 : ℝ))
        (Z ^ (AsymmetricGeometry.yBase - t / 2 : ℝ)) Z a ξ υ *
      (∏ j ∈ J, (Z ^ (ell j)) ^ ξ) =
        Z ^ (a + AsymmetricGeometry.signalOffset +
          AsymmetricGeometry.rowBase * (ξ - 1 / 6) +
          AsymmetricGeometry.yBase * (υ - 1) +
          t * (1 / 4 + 3 * ξ / 2 - υ / 2)) := by
  have hp : (∏ j ∈ J, (Z ^ (ell j)) ^ ξ) = Z ^ ((1 / 6 + t) * ξ) := by
    simp only [← Real.rpow_mul hZ.le]
    rw [← Real.rpow_sum_of_pos hZ, ← Finset.sum_mul, hell]
  rw [hp, scalePower, ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  dsimp [AsymmetricGeometry.xBase, AsymmetricGeometry.yBase,
    AsymmetricGeometry.rowBase, AsymmetricGeometry.signalOffset]
  ring

lemma perturbed_source_w_scale_identity {ι : Type*} (J : Finset ι)
    (ell : ι → ℝ) (t Z a e : ℝ)
    (hell : ∑ j ∈ J, ell j = 1 / 6 + t) (hZ : 0 < Z) :
    scalePower (Z ^ (AsymmetricGeometry.xBase - t / 2 : ℝ))
        (Z ^ (AsymmetricGeometry.yBase - t / 2 : ℝ)) Z a (1 / 6 + e) (19 / 20) *
      (∏ j ∈ J, (Z ^ (ell j)) ^ (1 / 6 + e)) =
        Z ^ (a + AsymmetricGeometry.signalOffset +
          AsymmetricGeometry.rowBase * e - AsymmetricGeometry.yBase / 20 +
          t * (1 / 40 + 3 * e / 2)) := by
  rw [perturbed_source_scale_identity J ell t Z a (1 / 6 + e) (19 / 20) hell hZ]
  congr 1
  ring

lemma perturbed_source_z_scale_identity {ι : Type*} (J : Finset ι)
    (ell : ι → ℝ) (t Z a : ℝ)
    (hell : ∑ j ∈ J, ell j = 1 / 6 + t) (hZ : 0 < Z) :
    scalePower (Z ^ (AsymmetricGeometry.xBase - t / 2 : ℝ))
        (Z ^ (AsymmetricGeometry.yBase - t / 2 : ℝ)) Z a (33 / 200) 1 *
      (∏ j ∈ J, (Z ^ (ell j)) ^ (33 / 200 : ℝ)) =
        Z ^ (a + AsymmetricGeometry.signalOffset -
          AsymmetricGeometry.rowBase / 600 - t / 400) := by
  rw [perturbed_source_scale_identity J ell t Z a (33 / 200) 1 hell hZ]
  congr 1
  ring

lemma perturbed_source_w_strict_exponent (β e t : ℝ)
    (he' : e ≤ 1 / 1000)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 1000) :
    (β + e) + AsymmetricGeometry.signalOffset +
      AsymmetricGeometry.rowBase * e - AsymmetricGeometry.yBase / 20 +
      t * (1 / 40 + 3 * e / 2) ≤
        β + AsymmetricGeometry.signalOffset - 7 / 20000 := by
  have heprod := mul_le_mul_of_nonneg_left he' ht
  dsimp [AsymmetricGeometry.rowBase, AsymmetricGeometry.yBase,
    AsymmetricGeometry.signalOffset, AsymmetricGeometry.skew]
  nlinarith

lemma perturbed_source_z_strict_exponent (β e t : ℝ)
    (he : e ≤ 1 / 1000) (ht : 0 ≤ t) :
    (β + e) + AsymmetricGeometry.signalOffset -
      AsymmetricGeometry.rowBase / 600 - t / 400 ≤
        β + AsymmetricGeometry.signalOffset - 7 / 20000 := by
  dsimp [AsymmetricGeometry.rowBase, AsymmetricGeometry.signalOffset,
    AsymmetricGeometry.skew]
  linarith

end SevenEighths.ProbePrincipalRemainderBounds

end

end OAI
