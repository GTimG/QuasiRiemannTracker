/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Unfolding/ReverseAbsoluteConvergence.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Profiles.LogarithmicRegularityAndSmoothing
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Unfolding.ForwardOrbitAbsoluteIntegrability

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem reverse_joint_absolute (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (prior : Nonempty (JointSameResidueProfileSources R N)) : Nonempty (JointReverseAbsoluteSources R N) := by
  obtain ⟨C⟩ := prior
  exact ⟨DedekindZetaZeroFree.OrbitFrequencies.jointReverseAbsoluteSources R C⟩

end DedekindZetaZeroFree.ThetaExpansion
