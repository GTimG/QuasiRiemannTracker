/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Moments/Principal/Contour/ResidueNonvanishing.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.SpectralFunction

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.ResidueNonzero

noncomputable section

variable {F : Type} [Field F] [NumberField F]
variable {S : DedekindZetaZeroFree.SArithmeticData F}
variable {η : DedekindZetaZeroFree.RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem RS_ne_zero : Spectral.RS D ≠ 0 := by
  unfold Spectral.RS DedekindZetaZeroFree.comparisonPrincipalResidue
  apply mul_ne_zero
  · exact DedekindZetaZeroFree.PrincipalMellinComparison.principal_regularization_ne_zero F
      D.recipe.A.modulus D.recipe.A.modulus_ne_zero D.recipe.target D.recipe.probe.principal
      D.recipe.continuation
  · exact DedekindZetaZeroFree.MellinZeroFree.comparisonPrincipalIncompleteL_eulerFactors_ne_zero
      F D.recipe.A D.recipe.target 1 (by norm_num)

theorem c₀_ne_zero : Spectral.c₀ D ≠ 0 := by
  unfold Spectral.c₀
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (RS_ne_zero D)) D.M_one_sixth_ne_zero)
      D.W1Hat_one_ne_zero) (by norm_num)

end

end DedekindZetaZeroFree.Quantitative.ResidueNonzero
