/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Unfolding/SignedAbsoluteUnfolding.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Periods.UpperQuotientVanishing
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Unfolding.DyadicFactorizationAndSignedSeries

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem signed_unfolding (R : PrincipalMellin.ActualRecipe S η)
    (hR : RootAligned R) (N : TraceHaarTransport R)
    (prior : Nonempty (JointUpperVanishingSources R N)) : Nonempty (JointSignedUnfoldingSources R N) := by
  obtain ⟨C⟩ := prior
  exact ⟨{ toJointUpperVanishingSources := C, unfolding := SignedExpansion.signedUnfolding R C }⟩
end DedekindZetaZeroFree.ThetaExpansion
