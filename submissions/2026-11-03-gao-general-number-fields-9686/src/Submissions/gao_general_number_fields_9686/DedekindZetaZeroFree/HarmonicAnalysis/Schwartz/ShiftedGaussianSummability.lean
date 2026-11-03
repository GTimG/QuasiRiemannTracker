/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Schwartz/ShiftedGaussianSummability.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.HarmonicAnalysis.Poisson.GaussianLattice

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open AbelianQuotient.Theta

theorem summable_shiftedGaussian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (z : E) {a : ℝ} (ha : 0 < a) :
    Summable (fun ℓ : L => Real.exp (-a * ‖z + (ℓ : E)‖ ^ 2)) := by
  have hbase : Summable (fun ℓ : L => ‖latticeGaussian (a / 2) (ℓ : E)‖) :=
    (summable_latticeGaussian L (half_pos ha)).norm
  have hbound :
      Summable (fun ℓ : L =>
        Real.exp (a * ‖z‖ ^ 2) * ‖latticeGaussian (a / 2) (ℓ : E)‖) :=
    hbase.mul_left _
  apply hbound.of_norm_bounded
  intro ℓ
  have h := norm_latticeGaussian_add_le ha.le z (ℓ : E)
  rw [norm_latticeGaussian] at h
  simpa [norm_latticeGaussian] using h

theorem summable_shiftedGaussian_punctured
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (z : E) {a : ℝ} (ha : 0 < a) :
    Summable (fun ℓ : {ℓ : L // z + (ℓ : E) ≠ 0} =>
      Real.exp (-a * ‖z + ((ℓ : L) : E)‖ ^ 2)) := by
  exact (summable_shiftedGaussian L z ha).comp_injective Subtype.val_injective

end DedekindZetaZeroFree

end
