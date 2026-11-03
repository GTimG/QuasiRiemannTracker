/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Analysis/ClosedOperators/ClosedGraphLimits.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

@[expose] public section

noncomputable section
open Filter
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

theorem closed_graph_limit
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Δ : H →ₗ.[ℂ] H) (hclosed : Δ.IsClosed)
    (z : ℕ → H × H) (hz : ∀ n, ∃ hn : (z n).1 ∈ Δ.domain,
      Δ ⟨(z n).1, hn⟩ = (z n).2)
    (u v : H) (hlim : Tendsto z atTop (nhds (u,v))) :
    ∃ hu : u ∈ Δ.domain, Δ ⟨u,hu⟩ = v := by
  have hgclosed : IsClosed (Δ.graph : Set (H × H)) := hclosed
  have hmem : (u, v) ∈ Δ.graph := by
    refine hgclosed.mem_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    obtain ⟨hn, hval⟩ := hz n
    show z n ∈ Δ.graph
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨(z n).1, hn⟩, rfl, hval⟩
  rw [LinearPMap.mem_graph_iff] at hmem
  obtain ⟨y, hy1, hy2⟩ := hmem
  change (↑y : H) = u at hy1
  have hu : u ∈ Δ.domain := hy1 ▸ y.property
  refine ⟨hu, ?_⟩
  have hsub : (⟨u, hu⟩ : Δ.domain) = y := by
    ext
    exact hy1.symm
  rw [hsub, hy2]

end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

end
