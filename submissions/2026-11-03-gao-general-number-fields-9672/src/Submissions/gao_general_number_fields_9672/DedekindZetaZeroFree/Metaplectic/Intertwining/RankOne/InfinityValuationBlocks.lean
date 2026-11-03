/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/RankOne/InfinityValuationBlocks.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellData

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.InfinityTailNumeratorSteps

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain ValuativeRel
open KPRankOneOpenCellKernel KPRankOneReverseRegulatorShellsRaw

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]

def infinityBlock (N n : ℕ) : Set (LocalField F q)ˣ :=
  {v | (N : ℤ) + 3 * (n : ℤ) < valuationIndex F q v ∧
    valuationIndex F q v ≤ (N : ℤ) + 3 * ((n : ℤ) + 1)}

end
end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.InfinityTailNumeratorSteps
