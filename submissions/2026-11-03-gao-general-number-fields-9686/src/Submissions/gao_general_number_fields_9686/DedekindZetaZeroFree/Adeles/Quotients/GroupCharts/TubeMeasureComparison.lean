/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Quotients/GroupCharts/TubeMeasureComparison.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Quotients.GroupCharts.FiniteLevelTubeDomination

@[expose] public section

noncomputable section
open MeasureTheory Topology
open scoped Classical NumberField ENNReal
namespace DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2
open KPContActualSphericalRightFieldIdentification

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

def chartTube (chart : GroupChart F ζ hζ U R P H)
    (p : KPContLocalNorm.Space (groupDimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    KPSmoothLocalQuotientCharts.X F ζ hζ :=
  KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (chart.groupLift p.1 * p.2)

theorem group_chart_full_tube_haar_domination
    (chart : GroupChart F ζ hζ U R P H)
    (A : Set (KPContLocalNorm.Space (groupDimension F)))
    (hA : IsCompact A) (hAT : A ⊆ chart.T.carrier) :
    ∃ (μArch : Measure (KPSmoothLocalQuotientCharts.ArchGroup F))
      (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) (C : ℝ),
      μArch.IsHaarMeasure ∧ ν.IsHaarMeasure ∧
      Measure.map (fun p : KPSmoothLocalQuotientCharts.ArchGroup F ×
          KPFiniteCuspAtlas.FiniteCover F ζ hζ =>
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ p.1 * p.2)
          (μArch.prod ν) = R.adelicHaar ∧
      0 < ν (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) ∧
      ν (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) < ⊤ ∧
      0 < C ∧
      Measure.map (chartTube chart)
        ((volume.restrict A).prod
          (ν.restrict (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)))) ≤
        ENNReal.ofReal C • R.quotientHaar := by
  exact actual_original_chart_tube_domination chart A hA hAT

end DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2

end
