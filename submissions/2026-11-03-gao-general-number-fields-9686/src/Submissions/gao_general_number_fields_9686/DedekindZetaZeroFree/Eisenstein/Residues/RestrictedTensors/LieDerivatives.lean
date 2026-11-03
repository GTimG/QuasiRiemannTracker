/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/RestrictedTensors/LieDerivatives.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.Smooth.RestrictedTensors.OperatorWordEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open LiteralSource MomentSources HCGeneration TensorActionSource
open KPContActualSphericalRightFieldIdentification KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem restrictedSlot_residue_lie (N : TraceHaarTransport R)
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : s.val, Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (i : Fin 6) (v : complexCore) :
    actualRight F R.A.zeta12 R.A.primitive_zeta12
      ((actualLieIndexEquiv (F := F)).symm (w,i))
      (coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v)) =
    coreResidue R P C
      (restrictedSlotTensor R.A P C s x w hw (NativeComplexHCOperators.operators i v)) := by
  let μ := fun q : KPFinitePlace F => Measure.addHaarMeasure (TensorSeedSource.integerCompacts q)
  let : ∀ q, (μ q).IsAddHaarMeasure := fun q => inferInstance
  have hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1 :=
    fun _ => Measure.addHaarMeasure_self
  let H := actualImageData R P C μ hμ
  let u := fun v : complexCore => PiTensorProduct.tprod ℂ
    (Function.update x ⟨Sum.inl w,hw⟩ (harmonicInverse v))
  let b : List (StageGenerator R P C s) :=
    [Sum.inr i].map (stageComplexIndex R P C s w)
  have he : actualStageWord R P C μ hμ s b (sourceStageQuotient R H s.val (u v)) =
      sourceStageQuotient R H s.val (u (NativeComplexHCOperators.operators i v)) := by
    rw [actualStageWord_eq_image]
    change stageImageWord R P C H s ([Sum.inr i].map (stageComplexIndex R P C s w))
      (stageImageQuotient R P C H s (u v)) =
      stageImageQuotient R P C H s (u (NativeComplexHCOperators.operators i v))
    rw [stageComplexIndex_word R P C H s w hw,
      stageImageQuotient_variable_slot,stageImageQuotient_variable_slot,tensorSlot_tprod]
    simp only [Function.update_self,Function.update_idem]
    rfl
  have hh := actualCoreResidue_stage_word R P C μ hμ N s b
    (sourceStageQuotient R H s.val (u v))
  rw [he,actualCoreResidue_source_stage,actualCoreResidue_source_stage] at hh
  exact hh.symm

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
