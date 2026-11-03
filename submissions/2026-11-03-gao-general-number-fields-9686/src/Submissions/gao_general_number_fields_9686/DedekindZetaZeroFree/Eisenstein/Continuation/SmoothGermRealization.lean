/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/SmoothGermRealization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.ScalarMeromorphicFamilies
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.SmoothGerms.UniformCompactTaylorRealization

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
