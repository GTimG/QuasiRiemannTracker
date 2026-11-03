/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Analysis/GeometricDenominator.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPTameTransposeBaseChart.AugmentationSteps.CubeShell

theorem geometric_denominator_tsum (z c : ℂ) (hz : ‖z‖ < 1) :
    (1 - z) * (∑' k : ℕ, c * z ^ k) = c := by
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hz]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, norm_one] at hz
    exact absurd hz (by norm_num)
  field_simp

end DedekindZetaZeroFree.KPTameTransposeBaseChart.AugmentationSteps.CubeShell

end
