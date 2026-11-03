/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/SpectralTheory/WeakSections/SupportAndMultiplication.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.WeakGradientLocalization

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport
open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings
open KPContActualSectorTestDifferentialDescent
open KPContActualSectorFormWeakLocalization

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

def SupportedAE (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) : Prop :=
  ∃ s : BorelL2Sections F ζ hζ U R P H,
    sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s ∧
    ∀ᵐ x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P,
      x ∉ K → squaredNorm F ζ hζ U R P H s.val x = 0

def IsActualProduct (η : CompactMultiplier (U := U) (H := H))
    (u v : KPContSectorClosedLpSubspace.H F ζ hζ R U) : Prop :=
  ∃ s t : BorelL2Sections F ζ hζ U R P H,
    sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s ∧
    sectorLineIsometry F ζ hζ U R P H v = mk F ζ hζ U R P H t ∧
    ∀ a : ActualChart (U := U) (H := H),
      (fun y : a.domain => sectionFields t.val a
        (KPContActualCotangentPieceHilbertSum.coordinates a y)) =ᵐ[a.liftedMeasure]
      (fun y => cutoffLift η.val a
        (KPContActualCotangentPieceHilbertSum.coordinates a y) *
        sectionFields s.val a (KPContActualCotangentPieceHilbertSum.coordinates a y))

end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

end
