/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/CompactMeromorphicAverages.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

@[expose] public section

noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation

def averageCLM {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] :
    C(X, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 μ ℂ)

theorem averageCLM_apply {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (v : C(X, ℂ)) : averageCLM μ v = ∫ x, v x ∂μ := by
  change L1.integralCLM' ℂ (ContinuousMap.toLp 1 μ ℂ v) = _
  rw [← L1.integral_eq', L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp μ v)

end DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation

end
