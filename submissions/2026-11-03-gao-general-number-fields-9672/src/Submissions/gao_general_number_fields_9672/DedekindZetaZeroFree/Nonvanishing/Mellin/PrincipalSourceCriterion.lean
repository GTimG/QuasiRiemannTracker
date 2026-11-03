/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Nonvanishing/Mellin/PrincipalSourceCriterion.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SixthRootAlignment
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Nonvanishing.Mellin.ProbeInversion

@[expose] public section

namespace DedekindZetaZeroFree.MomentSources

theorem principal_zero_free_of_selected_source
    (F : Type) [Field F] [NumberField F]
    (S : SArithmeticData F) (η : RayClassCharacter F S.modulus)
    (hη : η.IsPrincipal) (P : PrincipalRayHeckeData F S.modulus η)
    (R : PrincipalMellin.ActualRecipe S η) (M : SelectedMomentSource R) :
    ∀ s : ℂ, (5999 / 6000 : ℝ) < s.re → s ≠ 1 →
      comparisonPrincipalIncompleteL F S η hη P s ≠ 0 := by
  have hzero := recipe_zero_free_of_moment R (moment_of_source R M)
  intro s hs hs1
  exact PrincipalMellin.incomplete_nonzero_of_enlargement F S R.A
    R.containsOriginal R.sameModulus η hη P R.probe.principal R.continuation
    s (by linarith) hs1 (hzero s hs hs1)

end DedekindZetaZeroFree.MomentSources
