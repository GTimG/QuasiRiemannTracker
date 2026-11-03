/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/PrincipalSeries/ScalarSections/EvaluatorSmoothness.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Approximation.ArchimedeanChartMultiplication
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.Smooth.RestrictedTensorEvaluation
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.RankOne.ArchimedeanBigCellBasePoint

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPGlobalResidualConstruction Filter
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12

theorem quotientCoreEvaluator_continuous
    (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C)) :
    Continuous (quotientCoreEvaluator A P C x) := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨U, hlevel⟩ := quotientCoreValue_uniform_level A P C x
  obtain ⟨V, hVo, hb, hVD, _, _, _, hthick, _⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  apply continuous_iff_continuousAt.mpr
  intro g
  let J := fun y => quotientCoreEvaluator A P C x (g * archChart F ζ hζ y)
  have hJ : ContinuousAt J (archBase F) :=
    ((quotientCoreEvaluator_chart_smooth A P C x g).continuousOn.mono hVD).continuousAt
      (hVo.mem_nhds hb)
  have hbase : J (archBase F) = quotientCoreEvaluator A P C x g := by
    simp only [J, KPInterface.ResidueConstruction.Raw.archChart_base,
      Subgroup.coe_one, mul_one]
  apply Filter.tendsto_def.mpr
  intro S hS
  have hn : J ⁻¹' S ∈ nhds (archBase F) := hJ (by rwa [hbase])
  obtain ⟨W, hW, hoW, hbW⟩ := mem_nhds_iff.mp (Filter.inter_mem hn (hVo.mem_nhds hb))
  have hWV : W ⊆ V := fun y hy => (hW hy).2
  have hT := hthick W hoW hbW hWV U
  have hG : (fun k : G F ζ hζ => g⁻¹ * k) ⁻¹'
      {k | ∃ y ∈ W, ∃ u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U, k = archChart F ζ hζ y * u} ∈ nhds g := by
    have hc : ContinuousAt (fun k : G F ζ hζ => g⁻¹ * k) g :=
      continuousAt_const.mul continuousAt_id
    exact hc (by simpa using hT)
  apply Filter.mem_of_superset hG
  intro k hk
  obtain ⟨y, hy, u, hu, hk⟩ := hk
  have hk' : k = g * (archChart F ζ hζ y * u) := by rw [← hk]; group
  change quotientCoreEvaluator A P C x k ∈ S
  rw [hk', ← mul_assoc, hlevel _ u hu]
  exact (hW hy).1

theorem quotientCoreEvaluator_smooth
    (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C)) :
    KPLiteralRaw.Smooth F ζ hζ (quotientCoreEvaluator A P C x) :=
  ⟨quotientCoreEvaluator_continuous A P C x,
    quotientCoreEvaluator_chart_smooth A P C x, quotientCoreValue_uniform_level A P C x⟩
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
