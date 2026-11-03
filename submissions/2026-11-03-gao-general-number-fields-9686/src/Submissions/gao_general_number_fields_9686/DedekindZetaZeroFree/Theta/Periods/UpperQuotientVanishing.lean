/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/UpperQuotientVanishing.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Unfolding.ReverseAbsoluteConvergence
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Unfolding.UpperVanishingCertificates

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem both_upper_averages_zero (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (prior : Nonempty (JointReverseAbsoluteSources R N)) : Nonempty (JointUpperVanishingSources R N) := by
  exact IdeleInsertion.jointUpperVanishingSources_of_jointReverseAbsoluteSources R N prior

end DedekindZetaZeroFree.ThetaExpansion
