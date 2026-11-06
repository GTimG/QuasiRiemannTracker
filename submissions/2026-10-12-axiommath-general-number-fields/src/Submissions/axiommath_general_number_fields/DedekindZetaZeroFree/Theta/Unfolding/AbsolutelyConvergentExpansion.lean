/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Unfolding/AbsolutelyConvergentExpansion.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Moments.Reflected.RankOneExpansion

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
