/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/SmoothLaurentCoefficients.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.ScalarMeromorphicFamilies
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.SmoothGermRestrictionAndTransport
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.LaurentNumeratorCovariance
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.LaurentCoefficientIdentificationAndSmoothness

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
