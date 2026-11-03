/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/SpectralTheory/Residual/SectionMetricAndEigenfunctions.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.ScalarRealization
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.ArchimedeanCasimir
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.CutoffGraphConvergence

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSectionMetric
open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra KPContSectorSmoothFramesSupport
open ResidualSphericalGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem component_slice (Z : smoothSections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (b : KPSmoothActualFlowData.GInfinity F) :
    originalScalar F ζ hζ U R P H Z
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ b *
          ((H.atlas U).representative i).val)) =
      (Z.val i).val (KPMsFixedHaarDisintegration.archBasepoint F b) := by
  change ((smoothS F ζ hζ U R P H).symm Z).val.val _ = _
  rw [group_lift_formula]
  have hs := S_apply F ζ hζ U R P H ((smoothS F ζ hζ U R P H).symm Z).val i
    (KPMsFixedHaarDisintegration.archBasepoint F b)
  change (S F ζ hζ U R P H ((smoothS F ζ hζ U R P H).symm Z).val i).val _ = _ at hs
  have hz : S F ζ hζ U R P H ((smoothS F ζ hζ U R P H).symm Z).val = Z.val :=
    congrArg Subtype.val ((smoothS F ζ hζ U R P H).apply_symm_apply Z)
  rw [hz] at hs
  exact hs.symm
theorem section_eigen_of_native (Z : smoothSections F ζ hζ U R P H) (a : ℂ)
    (heigen : ∀ g, KPMsGreenFlux.casimir F ζ hζ
      (originalScalar F ζ hζ U R P H Z ∘ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) g =
      a * originalScalar F ζ hζ U R P H Z (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) :
    KPContActualSectorCutoffGraphLimit.localLaplacian Z = a • Z.val := by
  obtain ⟨e,he⟩ := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_product_splitting F ζ hζ
  funext i
  apply Subtype.ext
  funext x
  let b := KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ x
  have hb : KPMsFixedHaarDisintegration.archBasepoint F b = x :=
    KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection F ζ hζ x
  have hslice (d : KPSmoothActualFlowData.GInfinity F) :
      (originalScalar F ζ hζ U R P H Z ∘ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ)
        (e (d,(H.atlas U).representative i)) =
      (Z.val i).val (KPMsFixedHaarDisintegration.archBasepoint F d) := by
    rw [he]
    exact component_slice F ζ hζ U R P H Z i d
  have hm := ResidualSphericalMetric.original_slice_casimir F ζ hζ
    (originalScalar F ζ hζ U R P H Z ∘ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ)
    e he ((H.atlas U).representative i) (Z.val i).val (Z.property i) hslice b
  rw [hb, KPContArchLaplacianCoordinateBridge.bridge F (Z.val i).val (Z.property i) x] at hm
  have hv := heigen (e (b,(H.atlas U).representative i))
  rw [hm] at hv
  have hs := hslice b
  rw [hb] at hs
  simp only [Function.comp_apply] at hs
  rw [hs] at hv
  exact hv
end DedekindZetaZeroFree.FourierContinuation.ResidualSectionMetric

end
