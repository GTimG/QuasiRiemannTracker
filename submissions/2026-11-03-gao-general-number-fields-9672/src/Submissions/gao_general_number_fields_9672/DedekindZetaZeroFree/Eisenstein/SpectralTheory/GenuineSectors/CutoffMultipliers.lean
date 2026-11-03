/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/SpectralTheory/GenuineSectors/CutoffMultipliers.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.DifferentialAndCodifferential
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.TestL2Embeddings

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSquareEndPartition

open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

abbrev Cutoff := RealSmoothCutoff F ζ hζ U R P H

structure SectorMultiplier (η : Cutoff F ζ hζ U R P H) where
  op : KPContSectorClosedLpSubspace.H F ζ hζ R U →L[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U
  ae_apply : ∀ u : KPContSectorClosedLpSubspace.H F ζ hζ R U,
    ((op u).val : KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ U → ℂ)
      =ᵐ[KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U]
    fun x => (η.val (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x) : ℂ) *
      (u.val : KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ U → ℂ) x
  test_commutes : ∀ f : S_U F ζ hζ U R P H,
    op (KPContActualSectorTestEmbeddings.iota f) =
      KPContActualSectorTestEmbeddings.iota (scalarMultiply η f)
  ordinary_central_invariant : ∀ (ε : rootsOfUnity 3 F)
      (x : KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ U),
    η.val (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U
      (KPContSectorCoveredQuotientVocabulary.z F ζ hζ U ε x)) =
      η.val (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x)
  genuine_unchanged : ∀ (f : KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ U)
      (ε : rootsOfUnity 3 F)
      (x : KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ U),
    (η.val (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U
      (KPContSectorCoveredQuotientVocabulary.z F ζ hζ U ε x)) : ℂ) *
      f.val (KPContSectorCoveredQuotientVocabulary.z F ζ hζ U ε x) =
    (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      ((η.val (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x) : ℂ) * f.val x)

end DedekindZetaZeroFree.KPContActualSquareEndPartition

end
