/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/MeasureTheory/Density/CompactPositiveComparison.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2

theorem compact_positive_density_lower_bound {E : Type*} [TopologicalSpace E]
    {S K : Set E} {ρ : E → ℝ} (hK : IsCompact K) (hKS : K ⊆ S)
    (hρ : ContinuousOn ρ S) (hpos : ∀ x ∈ S, 0 < ρ x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c ≤ ρ x := by
  exact hK.exists_forall_le' (hρ.mono hKS) (fun x hx => hpos x (hKS hx))

end DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2

end
