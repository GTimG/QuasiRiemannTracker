/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Smooth/CompactCasimirHarmonicTruncation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.RankOne.CharacterCasimirEigenidentity
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.RankOne.HaarDerivativeTransfer

@[expose] public section

section

namespace DedekindZetaZeroFree
namespace KPCompactHarmonic

open MeasureTheory Filter
open scoped Topology Matrix.Norms.L2Operator InnerProductSpace

abbrev U2 := Matrix.unitaryGroup (Fin 2) ℂ

noncomputable def symmetricPowerTrace (n : ℕ) (g : U2) : ℂ :=
  match n with
  | 0 => 1
  | 1 => Matrix.trace g.val
  | n + 2 => Matrix.trace g.val * symmetricPowerTrace (n + 1) g -
      Matrix.det g.val * symmetricPowerTrace n g

noncomputable def rankOneCharacter (ℓ : ℕ) (g : U2) : ℂ :=
  symmetricPowerTrace (2 * ℓ) g / Matrix.det g.val ^ ℓ

private theorem compactU2 : CompactSpace U2 := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_unitary, ?_⟩
  apply (Metric.isBounded_iff_subset_closedBall 0).mpr
  refine ⟨1, ?_⟩
  intro g hg
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact le_of_eq (CStarRing.norm_coe_unitary ⟨g, hg⟩)

attribute [local instance] compactU2

end KPCompactHarmonic
end DedekindZetaZeroFree

end
