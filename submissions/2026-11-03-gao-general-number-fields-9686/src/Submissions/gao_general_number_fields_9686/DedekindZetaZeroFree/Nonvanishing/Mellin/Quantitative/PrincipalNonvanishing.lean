/-
2026-11-03 refinement by Zhongpai Gao (https://github.com/Gaozhongpai).
The following header records the PR #114 source provenance at 09afbb4ce6570c1615d58509dc197fc9f0956b7d.
This file now contains the native parameter refinement at
829193272c1eaf223bb7228fbfb9003f414808e9; local imports are relocated under Submissions.gao_general_number_fields_9686.
Original declaration namespaces and all source attribution are retained.
Native compilation and tracker admission remain pending; see Candidate.Provenance.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Nonvanishing/Mellin/Quantitative/PrincipalNonvanishing.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.ZeroExclusion
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalSourceCriterion
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Unfolding.AbsolutelyConvergentExpansion

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative

open DedekindZetaZeroFree

theorem comparisonPrincipalIncompleteL_ne_zero
    (F : Type) [Field F] [NumberField F] (S : SArithmeticData F)
    (η : RayClassCharacter F S.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F S.modulus η) :
    ∀ s : ℂ, 4843 / 5000 < s.re → s ≠ 1 →
      comparisonPrincipalIncompleteL F S η hη P s ≠ 0 := by
  obtain ⟨R, hR, ⟨M⟩⟩ := DedekindZetaZeroFree.MomentSources.source_exists S η hη P
  intro s hs hs1
  have hzero : R.L s ≠ 0 :=
    RecipeZeroFree.recipe_zero_free (⟨R, hR, M⟩ : FixedData S η) s hs hs1
  exact PrincipalMellin.incomplete_nonzero_of_enlargement F S R.A
    R.containsOriginal R.sameModulus η hη P R.probe.principal R.continuation
    s (by linarith) hs1 hzero

end DedekindZetaZeroFree.Quantitative
