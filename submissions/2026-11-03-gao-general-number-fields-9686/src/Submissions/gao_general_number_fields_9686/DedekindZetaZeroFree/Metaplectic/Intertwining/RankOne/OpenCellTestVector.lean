/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/RankOne/OpenCellTestVector.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.NormalizedLevelNumerator
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.GlobalContinuationFromLevelIntegrals
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ContinuedOperatorFamilies

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneForwardTestVector

open scoped Valued NumberField
open Classical MeasureTheory ValuativeRel KPLocalPrincipalSeries KPRankOneRootParameter
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPRankOneShellContinuation
open NumberField IsDedekindDomain KPLocalExceptionalConstruction

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

theorem r_zero : r K 0 = 1 := by simp [r]

theorem t_zero : t K 0 = (residueCardinality K : ℂ)⁻¹ := by
  simp [t, r_zero]

end
end DedekindZetaZeroFree.KPRankOneForwardTestVector
