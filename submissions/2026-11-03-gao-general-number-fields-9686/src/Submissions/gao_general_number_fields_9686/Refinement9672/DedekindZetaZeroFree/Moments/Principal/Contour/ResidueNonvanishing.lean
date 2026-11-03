/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/Moments/Principal/Contour/ResidueNonvanishing.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.SpectralFunction

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

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

end Refinement9672
