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
Original path: DedekindZetaZeroFree/Nonvanishing/Mellin/Quantitative/PrincipalNonvanishing.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.ZeroExclusion
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalSourceCriterion
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Unfolding.AbsolutelyConvergentExpansion

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree

theorem comparisonPrincipalIncompleteL_ne_zero
    (F : Type) [Field F] [NumberField F] (S : SArithmeticData F)
    (η : RayClassCharacter F S.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F S.modulus η) :
    ∀ s : ℂ, 1209 / 1250 < s.re → s ≠ 1 →
      comparisonPrincipalIncompleteL F S η hη P s ≠ 0 := by
  obtain ⟨R, hR, ⟨M⟩⟩ := DedekindZetaZeroFree.MomentSources.source_exists S η hη P
  intro s hs hs1
  have hzero : R.L s ≠ 0 :=
    RecipeZeroFree.recipe_zero_free (⟨R, hR, M⟩ : FixedData S η) s hs hs1
  exact PrincipalMellin.incomplete_nonzero_of_enlargement F S R.A
    R.containsOriginal R.sameModulus η hη P R.probe.principal R.continuation
    s (by linarith) hs1 hzero

end DedekindZetaZeroFree.Quantitative

end Refinement9672
