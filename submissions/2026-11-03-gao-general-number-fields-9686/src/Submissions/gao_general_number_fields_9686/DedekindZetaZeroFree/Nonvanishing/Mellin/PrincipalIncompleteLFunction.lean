/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Nonvanishing/Mellin/PrincipalIncompleteLFunction.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalSourceCriterion
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Unfolding.AbsolutelyConvergentExpansion

@[expose] public section

namespace DedekindZetaZeroFree

theorem principal_mellin_zero_free
    (F : Type) [Field F] [NumberField F]
    (S : SArithmeticData F)
    (η : RayClassCharacter F S.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F S.modulus η) :
    ∀ s : ℂ, (5999 / 6000 : ℝ) < s.re → s ≠ 1 →
      comparisonPrincipalIncompleteL F S η hη P s ≠ 0 := by
  obtain ⟨R, _, ⟨M⟩⟩ := MomentSources.source_exists S η hη P
  exact MomentSources.principal_zero_free_of_selected_source F S η hη P R M

end DedekindZetaZeroFree
