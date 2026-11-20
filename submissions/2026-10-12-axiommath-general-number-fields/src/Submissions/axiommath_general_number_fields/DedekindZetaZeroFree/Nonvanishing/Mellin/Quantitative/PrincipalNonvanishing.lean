/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Nonvanishing/Mellin/Quantitative/PrincipalNonvanishing.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.ZeroExclusion
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalSourceCriterion
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Unfolding.AbsolutelyConvergentExpansion

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative

open DedekindZetaZeroFree

theorem comparisonPrincipalIncompleteL_ne_zero
    (F : Type) [Field F] [NumberField F] (S : SArithmeticData F)
    (η : RayClassCharacter F S.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F S.modulus η) :
    ∀ s : ℂ, 31 / 32 < s.re → s ≠ 1 →
      comparisonPrincipalIncompleteL F S η hη P s ≠ 0 := by
  obtain ⟨R, hR, ⟨M⟩⟩ := DedekindZetaZeroFree.MomentSources.source_exists S η hη P
  intro s hs hs1
  have hzero : R.L s ≠ 0 :=
    RecipeZeroFree.recipe_zero_free (⟨R, hR, M⟩ : FixedData S η) s hs hs1
  exact PrincipalMellin.incomplete_nonzero_of_enlargement F S R.A
    R.containsOriginal R.sameModulus η hη P R.probe.principal R.continuation
    s (by linarith) hs1 hzero

end DedekindZetaZeroFree.Quantitative
