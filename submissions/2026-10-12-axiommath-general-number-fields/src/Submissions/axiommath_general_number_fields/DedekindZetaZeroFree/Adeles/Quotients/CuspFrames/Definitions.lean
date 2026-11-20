/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Quotients/CuspFrames/Definitions.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

abbrev rationalLift (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (σ : KPCuspArithmetic.PGL2 F) : Cover F ζ hζ :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ
      (Classical.choose (Matrix.ProjGenLinGroup.mk_surjective σ)))

def cuspEnd (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (j : Cusps A) (Y : ℝ) : Set (X F ζ hζ) :=
  P.projection U ⁻¹' endSet A j Y

def AdmissibleFrame (j : Cusps A) (Y : ℝ) (x : X F ζ hζ) (g : Cover F ζ hζ) : Prop :=
  KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g = x ∧
    ∃ (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
      (t : ℝ) (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup),
      KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
      KPMsFixedHaarDisintegration.archBasepoint F a =
        KPCuspSiegel.action F ((A.cuspAtlas j.1).representative j.2)
          (KPCuspCharts.toArch F (p,t)) ∧
      g = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        (A.representative j.1).val * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val.val

end DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames

end
