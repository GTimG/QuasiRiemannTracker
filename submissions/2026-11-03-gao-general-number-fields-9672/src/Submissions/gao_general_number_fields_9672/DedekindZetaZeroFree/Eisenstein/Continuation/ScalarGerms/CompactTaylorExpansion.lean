/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/ScalarGerms/CompactTaylorExpansion.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Analysis.CauchyCenterContinuity

@[expose] public section

noncomputable section
open scoped Topology NNReal
open Complex Filter
namespace DedekindZetaZeroFree.EisensteinSmoothGerms
open ComplexAnalysis.KernelTaylor.CauchyOperators
variable {X : Type*} [TopologicalSpace X]

theorem scalar_cauchy_coefficients_radius_independent
    (f : ℂ → ℂ) (ρ : ℝ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 ρ))
    (t u : ℝ) (ht : 0 < t) (hu : 0 < u) (htρ : t < ρ) (huρ : u < ρ)
    (n : ℕ) : (cauchyPowerSeries f 0 t).coeff n =
      (cauchyPowerSeries f 0 u).coeff n := by
  have hpt := (hf.differentiableOn.mono
    (Metric.closedBall_subset_ball htρ)).hasFPowerSeriesOnBall
      (R := ⟨t, ht.le⟩) ht
  have hpu := (hf.differentiableOn.mono
    (Metric.closedBall_subset_ball huρ)).hasFPowerSeriesOnBall
      (R := ⟨u, hu.le⟩) hu
  have he := hpt.hasFPowerSeriesAt.eq_formalMultilinearSeries hpu.hasFPowerSeriesAt
  exact congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he

end DedekindZetaZeroFree.EisensteinSmoothGerms

end
