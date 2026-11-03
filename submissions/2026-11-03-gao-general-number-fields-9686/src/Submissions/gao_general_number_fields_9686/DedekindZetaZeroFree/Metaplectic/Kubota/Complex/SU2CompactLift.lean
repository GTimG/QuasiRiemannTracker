/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Kubota/Complex/SU2CompactLift.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Kubota.ComplexCharactersHaarAndSU2Splitting
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.L2Operator
namespace DedekindZetaZeroFree.KPActualReflectionData.StandardLocalSource
open KPCplxCharacterHaar

theorem complexSU2Embedding_continuous : Continuous complexSU2Embedding := by
  apply Units.isOpenEmbedding_val.isEmbedding.continuous_iff.mpr
  exact continuous_subtype_val

end DedekindZetaZeroFree.KPActualReflectionData.StandardLocalSource

end
