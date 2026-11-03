/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Quotients/CuspFrames/FiniteCoverLevelIdentification.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.FiniteOffsetData

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.KPMsAngularSourceRecipe
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem finitePart_eq_finiteCover :
    KPGlobalTorusFunctionData.finitePart F ζ hζ =
      KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
  rw [KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure,
    ActualFiniteFactor.finiteSubgroup_eq_ker]
  ext g
  change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g = 1 ↔
    KPCuspGenuineMonodromy.archProjection F ζ hζ g = 1
  constructor
  · intro h
    funext w
    have hw := congrFun h w
    rw [KPMsActualCuspSource.projection_compare] at hw
    let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)
    have hh := congrArg (Matrix.ProjGenLinGroup.map e.symm.toRingHom) hw
    dsimp only [e] at hh
    simpa only [← MonoidHom.comp_apply, ← Matrix.ProjGenLinGroup.map_comp,
      RingEquiv.symm_toRingHom_comp_toRingHom, Matrix.ProjGenLinGroup.map_id,
      MonoidHom.id_apply, map_one, Pi.one_apply] using hh
  · intro h
    funext w
    rw [KPMsActualCuspSource.projection_compare, h]
    exact map_one _

private theorem matching_of_subgroup_eq {G : Type*} [Group G] [TopologicalSpace G]
    (J K : Subgroup G) (h : J = K) :
    ∃ L : CompactOpenLevel J → CompactOpenLevel K,
      ∀ U, U.toOpenSubgroup.toSubgroup.map J.subtype =
        (L U).toOpenSubgroup.toSubgroup.map K.subtype := by
  subst K
  exact ⟨id, fun _ => rfl⟩

theorem matching_levels :
    ∃ L : Level F ζ hζ → KPMsFixedHaarDisintegration.Level F ζ hζ,
      ∀ U, KPGlobalTorusFunctionData.globalLevel F ζ hζ U =
        (L U).toOpenSubgroup.toSubgroup.map (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype := by
  exact matching_of_subgroup_eq _ _ (finitePart_eq_finiteCover F ζ hζ)
end DedekindZetaZeroFree.KPMsAngularSourceRecipe

end
