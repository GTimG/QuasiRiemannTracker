/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/UpperQuotientVanishing.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Unfolding.ReverseAbsoluteConvergence
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Unfolding.UpperVanishingCertificates

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem both_upper_averages_zero (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (prior : Nonempty (JointReverseAbsoluteSources R N)) : Nonempty (JointUpperVanishingSources R N) := by
  exact IdeleInsertion.jointUpperVanishingSources_of_jointReverseAbsoluteSources R N prior

end DedekindZetaZeroFree.ThetaExpansion
