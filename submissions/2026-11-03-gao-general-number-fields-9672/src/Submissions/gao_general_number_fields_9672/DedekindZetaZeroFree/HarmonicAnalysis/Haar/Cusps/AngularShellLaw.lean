/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/Cusps/AngularShellLaw.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Quotients.Cusps.AngularCoordinates

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology NNReal ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsActualAngularShellSource
open KPMsActualAngularSource
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (S : SourceRecipe F ζ hζ R P H) (U : Level F ζ hζ)

theorem fullToLevel_continuous (D : Iwasawa F ζ hζ) (V : Level F ζ hζ) :
    Continuous (fullToLevel F ζ hζ D V) :=
  continuous_quotient_mk'.quotient_lift _

theorem fullToLevel_measurable (D : Iwasawa F ζ hζ) (V : Level F ζ hζ) :
    Measurable (fullToLevel F ζ hζ D V) := by
  letI : BorelSpace (FullOmega F ζ hζ D) := ⟨rfl⟩
  letI : BorelSpace (Omega F ζ hζ D V) := ⟨rfl⟩
  exact (fullToLevel_continuous D V).measurable

end DedekindZetaZeroFree.KPMsActualAngularShellSource

end
