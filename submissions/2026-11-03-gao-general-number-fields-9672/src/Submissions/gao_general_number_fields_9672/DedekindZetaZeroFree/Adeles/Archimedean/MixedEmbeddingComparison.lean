/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Archimedean/MixedEmbeddingComparison.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Characters.SIntegerTraceAnnihilation
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Characters.TraceCharacterNondegeneracy

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

theorem sArchModel_comparison (F : Type*) [Field F] [NumberField F] :
    Continuous (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) ∧
      Continuous (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ∧
      ∀ x : F,
        NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F
            ((algebraMap F (NumberField.InfiniteAdeleRing F)) x) =
          NumberField.mixedEmbedding F x := by
  classical
  let e : NumberField.InfiniteAdeleRing F ≃ₜ NumberField.mixedEmbedding.mixedSpace F :=
    (Homeomorph.piEquivPiSubtypeProd (fun v : NumberField.InfinitePlace F => v.IsReal)
      (fun v => v.Completion)).trans
      (Homeomorph.prodCongr
        (Homeomorph.piCongrRight fun v =>
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph)
        ((Homeomorph.piCongrRight fun v =>
          (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp v.2)).toHomeomorph).trans
          (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
            (Equiv.subtypeEquivRight fun _ =>
              NumberField.InfinitePlace.not_isReal_iff_isComplex))))
  refine ⟨?_, ?_, ?_⟩
  · exact e.continuous
  · exact e.symm.continuous
  · intro x
    exact (NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm

end DedekindZetaZeroFree

end
