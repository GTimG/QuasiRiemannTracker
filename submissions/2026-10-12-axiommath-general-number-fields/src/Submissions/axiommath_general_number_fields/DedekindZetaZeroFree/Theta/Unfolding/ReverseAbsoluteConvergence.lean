/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Unfolding/ReverseAbsoluteConvergence.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Profiles.LogarithmicRegularityAndSmoothing
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Unfolding.ForwardOrbitAbsoluteIntegrability

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
