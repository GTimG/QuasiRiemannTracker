/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/SmoothLaurentCoefficients.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Continuation.ScalarMeromorphicFamilies
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Continuation.SmoothGermRestrictionAndTransport
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Continuation.LaurentNumeratorCovariance
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Continuation.LaurentCoefficientIdentificationAndSmoothness

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem selected_source_smooth_germ_of_scalar_germ
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R} (B : JointRootAlignedSources R N)
    (C : ScalarContinuation R B.sources) (v : R.A.UnitQuotient) (H : ScalarGerm C v) :
    ∃ G : IndividualSmoothGerm C v,
      G.radius ≤ H.radius ∧ ∀ s, s ∈ Metric.ball (0 : ℂ) G.radius →
        G.cleared s = (H.cleared s : Functions R) := by
  exact SmoothSource.selected_smooth_upgrade H
end DedekindZetaZeroFree.ThetaExpansion
