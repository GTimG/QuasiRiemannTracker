/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/RankOne/OpenCellKernel.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.NormalizedLevelNumerator
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.GlobalContinuationFromLevelIntegrals
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ZeroMapNonvanishing

@[expose] public section

section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.KPRankOneOpenCellKernel
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPRankOneShellContinuation
open KPLocalExceptionalConstruction
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)

variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

abbrev multiplicativeMeasure (μ : Measure (LocalField F q)) :=
  KPCubicHaar.multiplicativeHaar (LocalField F q) μ

end

end DedekindZetaZeroFree.KPRankOneOpenCellKernel

end
