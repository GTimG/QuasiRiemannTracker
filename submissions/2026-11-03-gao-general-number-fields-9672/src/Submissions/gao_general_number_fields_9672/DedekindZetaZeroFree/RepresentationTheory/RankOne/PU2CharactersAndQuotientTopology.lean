/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/RankOne/PU2CharactersAndQuotientTopology.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.RankOne.U2CharacterConvolutionOrthogonality

@[expose] public section

namespace DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation.CharacterExpansion

open MeasureTheory

open scoped Matrix.Norms.L2Operator InnerProductSpace

theorem cover_compactSpace : CompactSpace RawU2 := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_unitary
  · apply (Metric.isBounded_iff_subset_closedBall 0).mpr
    refine ⟨1, ?_⟩
    intro g hg
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (CStarRing.norm_coe_unitary ⟨g, hg⟩)

end DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation.CharacterExpansion
