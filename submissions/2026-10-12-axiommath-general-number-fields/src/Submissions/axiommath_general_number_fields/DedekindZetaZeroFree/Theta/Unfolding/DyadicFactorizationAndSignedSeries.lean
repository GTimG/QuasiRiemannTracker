/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Unfolding/DyadicFactorizationAndSignedSeries.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Unfolding.PositiveOrbitSeriesEvaluation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def signedUnfolding {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N) :
    SignedUnfolding R C.transport C.sources C.realization C.packet := by
  have hx := absolute_extraction R C
  exact DedekindZetaZeroFree.OrbitExpansion.SignedUnfoldingSub7.signedUnfolding_of_analytic_evaluations
    R C hx (forward_orbit_evaluation R C hx)
    (fun m D x => (exterior_digit_coefficient R C m D x).2)
    (fun v m Z hZ => (reverse_orbit_evaluation R C hx v m Z hZ).2)

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
