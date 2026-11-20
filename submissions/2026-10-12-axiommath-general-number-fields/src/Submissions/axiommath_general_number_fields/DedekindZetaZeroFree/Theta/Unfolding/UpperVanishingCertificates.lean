/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Unfolding/UpperVanishingCertificates.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Periods.OddUpperAverageVanishing

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.IdeleInsertion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)

def JointReverseAbsoluteSources.withUpperZero (C : JointReverseAbsoluteSources R N) : JointUpperVanishingSources R N where
  toJointReverseAbsoluteSources := C
  upperZero := bothUpperZero R C.constantTerm C.descent

theorem jointUpperVanishingSources_of_jointReverseAbsoluteSources (prior : Nonempty (JointReverseAbsoluteSources R N)) : Nonempty (JointUpperVanishingSources R N) := by
  rcases prior with ⟨C⟩
  exact ⟨JointReverseAbsoluteSources.withUpperZero R N C⟩
end DedekindZetaZeroFree.IdeleInsertion

end
