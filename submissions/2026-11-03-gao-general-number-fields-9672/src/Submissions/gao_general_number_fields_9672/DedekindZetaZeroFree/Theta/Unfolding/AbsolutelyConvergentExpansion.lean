/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Unfolding/AbsolutelyConvergentExpansion.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Moments.Reflected.RankOneExpansion

@[expose] public section

namespace DedekindZetaZeroFree.MomentSources
noncomputable section
variable {F : Type} [Field F] [NumberField F]

theorem source_exists
    (S : SArithmeticData F) (η : RayClassCharacter F S.modulus)
    (hη : η.IsPrincipal) (P : PrincipalRayHeckeData F S.modulus η) :
    ∃ R : PrincipalMellin.ActualRecipe S η,
      RootAligned R ∧ Nonempty (SelectedMomentSource R) :=
  ThetaExpansion.selected_rank_one_expansion S η hη P

end
end DedekindZetaZeroFree.MomentSources
