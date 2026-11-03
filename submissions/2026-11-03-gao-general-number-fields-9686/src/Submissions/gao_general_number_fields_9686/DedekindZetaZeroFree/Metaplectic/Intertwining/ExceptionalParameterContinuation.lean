/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/ExceptionalParameterContinuation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OpenCellTestVector
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInductionAndBorelRetraction

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPExceptionalRaw
open KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPRankOneShellContinuation KPRankOneForwardTestVector
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

include hζ in
 theorem root : ∃ ξ : (valuation (LocalField F q)).integer,
    (ξ : LocalField F q) = algebraMap F (LocalField F q) (ζ ^ 4) ∧ IsPrimitiveRoot ξ 3 := by
  have hp : IsPrimitiveRoot (algebraMap F (LocalField F q) (ζ ^ 4)) 3 :=
    (hζ.pow (by norm_num) (by norm_num : 12 = 4 * 3)).map_of_injective
      (FaithfulSMul.algebraMap_injective F (LocalField F q))
  have hv : valuation (LocalField F q) (algebraMap F (LocalField F q) (ζ ^ 4)) = 1 := by
    apply (pow_eq_one_iff_of_nonneg zero_le (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [← map_pow, hp.pow_eq_one, map_one]
  let ξ : (valuation (LocalField F q)).integer := ⟨algebraMap F (LocalField F q) (ζ ^ 4),
    by rw [Valuation.mem_integer_iff, hv]⟩
  refine ⟨ξ, rfl, ?_⟩
  exact (show IsPrimitiveRoot (((valuation (LocalField F q)).integer.subtype) ξ) 3 from hp).of_map_of_injective Subtype.val_injective

end
end DedekindZetaZeroFree.KPExceptionalRaw
