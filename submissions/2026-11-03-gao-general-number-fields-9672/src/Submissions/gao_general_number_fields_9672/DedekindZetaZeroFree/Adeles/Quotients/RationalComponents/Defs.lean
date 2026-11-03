/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Quotients/RationalComponents/Defs.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.SpectralTheory.SphericalHaarDisintegrationData
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGL.HyperbolicPushforward
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Quotients.ProductHaarSliceTransport

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPActualComponentHaarSources

open KPMsFixedHaar
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

abbrev Gi (i : Fin A.componentCount) :=
  KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i)

def rationalEquiv : KPCuspArithmetic.PGL2 F ≃*
    KPRationalAdelicSplitting.RationalPGL2 F :=
  QuotientGroup.quotientMulEquivOfEq Matrix.GeneralLinearGroup.center_eq_range_scalar

def Ga (i : Fin A.componentCount) :
    Subgroup (KPSmoothActualFlowData.GInfinity F) :=
  (Gi F ζ hζ hF U A i).map
    ((KPSmoothLocalQuotientCharts.archProjection F ζ hζ).comp
      ((KPRationalAdelicSplitting.rationalPGLHom F ζ hζ).comp
        (rationalEquiv F).toMonoidHom))

def B (i : Fin A.componentCount) :=
  KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U (A.representative i)

def C (i : Fin A.componentCount) :=
  Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))

def m (p : KPSmoothActualFlowData.GInfinity F ×
    KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
  KPSmoothActualFlowData.archimedeanInsertion F ζ hζ p.1 * p.2.val

end DedekindZetaZeroFree.KPActualComponentHaarSources

end
