/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Quotients/CuspFrames/FiniteOffsetConstruction.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Torus.CuspFrames.NormFactorization
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.FiniteCoverLevelIdentification

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal Topology BigOperators
namespace DedekindZetaZeroFree.KPMsAngularSourceRecipe
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem exists_offset_source_recipe
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :
    Nonempty (OffsetSourceRecipe F ζ hζ R P H) := by
  obtain ⟨L, hL⟩ := matching_levels F ζ hζ
  refine ⟨{ atlasLevel := L, level_matching := hL, height_normalized := ?_ }⟩
  intro U j a p t ε u ha
  have hu : u.val ∈ (L U).toOpenSubgroup.toSubgroup.map
      (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype := by
    rw [← hL U]
    exact u.property
  obtain ⟨v, hv, he⟩ := Subgroup.mem_map.mp hu
  change v.val = u.val at he
  have hcentral : (KPCuspGenuineMonodromy.central F ζ hζ ε).val =
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε := rfl
  simpa only [Subgroup.coe_mul, hcentral, he] using
    (actual_frame_norm_factorization F ζ hζ
      (((H.atlas (L U)).cuspAtlas j.1).representative j.2) a
      ((H.atlas (L U)).representative j.1 *
        KPCuspGenuineMonodromy.central F ζ hζ ε * v) p t ha)

end DedekindZetaZeroFree.KPMsAngularSourceRecipe

end
