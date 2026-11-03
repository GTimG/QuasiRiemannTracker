/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/CompactProbabilityExistence.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Quotients.Residual.LpAveraging

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualCompactProbability
open KPContSectorCoveredQuotientVocabulary
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming K_U_compact → K_U_compact
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
local instance : MeasurableSpace (K_U F ζ hζ U) := borel (K_U F ζ hζ U)
local instance : BorelSpace (K_U F ζ hζ U) := ⟨rfl⟩
theorem exists_probability : ∃ ν : Measure (K_U F ζ hζ U),
    IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant := by
  letI : IsTopologicalGroup (ActualCover F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  letI : CompactSpace (K_U F ζ hζ U) := isCompact_iff_compactSpace.mp (K_U_compact F ζ hζ U)
  let Q : TopologicalSpace.PositiveCompacts (K_U F ζ hζ U) :=
    ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩
  refine ⟨Measure.haarMeasure Q, ?_, inferInstance⟩
  refine ⟨?_⟩
  change Measure.haarMeasure Q Q = 1
  exact Measure.haarMeasure_self
end DedekindZetaZeroFree.FourierContinuation.ResidualCompactProbability

end
