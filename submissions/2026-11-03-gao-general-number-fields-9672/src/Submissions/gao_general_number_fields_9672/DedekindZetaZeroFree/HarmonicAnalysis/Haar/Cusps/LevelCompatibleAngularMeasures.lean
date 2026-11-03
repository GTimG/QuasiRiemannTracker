/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/Cusps/LevelCompatibleAngularMeasures.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.SpectralTheory.AngularHaarDisintegration

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

open _root_.DedekindZetaZeroFree.KPMsFixedHaarDisintegration renaming toRawTransport → toRawTransport
open _root_.DedekindZetaZeroFree.KPMsFixedHaarDisintegration renaming fromRawDisintegration → fromRawDisintegration
open _root_.DedekindZetaZeroFree.KPMsFixedHaarDisintegration renaming fromRawCompatibility → fromRawCompatibility

namespace DedekindZetaZeroFree.KPMsActualNativeHaarFamily

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)

def kernels (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) : KPMsFixedHaar.FiberKernel A :=
  (KPMsFixedHaar.probability_fiber_kernel A).some

def rawFamily : KPMsFixedHaar.AllLevels F ζ hζ R (toRawTransport F ζ hζ P) :=
  (KPMsFixedHaar.coherent_cusp_geometry F ζ hζ R
    (toRawTransport F ζ hζ P) (kernels F ζ hζ)).choose

def family : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P where
  totallyComplex := (rawFamily F ζ hζ R P).totallyComplex
  atlas := (rawFamily F ζ hζ R P).atlas
  disintegration := fun U => fromRawDisintegration F ζ hζ
    ((rawFamily F ζ hζ R P).atlas U) R P
    ((rawFamily F ζ hζ R P).disintegration U)
  compatible := by
    intro V U h
    obtain ⟨C⟩ := (rawFamily F ζ hζ R P).compatible V U h
    exact ⟨fromRawCompatibility F ζ hζ R P h
      ((rawFamily F ζ hζ R P).atlas V) ((rawFamily F ζ hζ R P).atlas U)
      ((rawFamily F ζ hζ R P).disintegration V)
      ((rawFamily F ζ hζ R P).disintegration U) C⟩

end DedekindZetaZeroFree.KPMsActualNativeHaarFamily

end
