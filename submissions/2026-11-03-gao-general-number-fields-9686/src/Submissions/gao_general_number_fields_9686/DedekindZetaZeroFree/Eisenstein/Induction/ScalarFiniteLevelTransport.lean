/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Induction/ScalarFiniteLevelTransport.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.FiniteCoverLevelIdentification

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
def atlasLevel : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ →
    KPMsFixedHaarDisintegration.Level F ζ hζ :=
  (KPMsAngularSourceRecipe.matching_levels F ζ hζ).choose

theorem level_matching (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.globalLevel F ζ hζ U =
      (atlasLevel F ζ hζ U).toOpenSubgroup.toSubgroup.map
        (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype :=
  (KPMsAngularSourceRecipe.matching_levels F ζ hζ).choose_spec U
end DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource

end
