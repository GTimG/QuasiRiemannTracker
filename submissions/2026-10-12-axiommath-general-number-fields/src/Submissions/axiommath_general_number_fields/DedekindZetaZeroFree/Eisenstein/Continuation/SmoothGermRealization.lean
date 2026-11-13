/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/SmoothGermRealization.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Continuation.ScalarMeromorphicFamilies
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Continuation.SmoothGerms.UniformCompactTaylorRealization

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SharedSource
open MomentSources EisensteinSmoothGerms
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem selected_realization_exists
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R}
    (B : JointRootAlignedSources R N) : Nonempty (Realization R B.sources) := by
  obtain ⟨C, ⟨H⟩⟩ := ThetaExpansion.selected_scalar_source_exists  R B
  obtain ⟨T, _⟩ := scalar_family_realization_constructed H
  exact ⟨T⟩

end DedekindZetaZeroFree.SharedSource

end
