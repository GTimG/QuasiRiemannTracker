/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Smooth/RestrictedTensors/OperatorWordEvaluation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.LieOperatorWords

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct NNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open LiteralSource MomentSources HCGeneration
open KPContActualSphericalRightFieldIdentification KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem restrictedSlot_native_word (N : TraceHaarTransport R)
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : s.val, Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (b : List (Fin (groupDimension F))) :
    ∃ (y : ∀ j : s.val, Plus R.A P C j.val) (a : List ComplexGenerator),
      (∀ v : complexCore,
        actualRightWord F R.A.zeta12 R.A.primitive_zeta12 b
          (coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v)) =
        coreResidue R P C (restrictedSlotTensor R.A P C s y w hw (complexWord a v))) ∧
      ∀ orders : Finset ℕ, ∃ inputOrders : Finset ℕ, ∃ B : ℝ≥0, B ≠ 0 ∧
        ∀ v : complexCore, (orders.sup coreSeminorm) (complexWord a v) ≤
          B * (inputOrders.sup coreSeminorm) v := by
  let μ := fun q : KPFinitePlace F => Measure.addHaarMeasure (TensorSeedSource.integerCompacts q)
  let : ∀ q, (μ q).IsAddHaarMeasure := fun q => inferInstance
  obtain ⟨y,a,ha⟩ := restrictedSlot_residue_native_word R P C μ
    (fun _ => Measure.addHaarMeasure_self) N s x w hw b
  exact ⟨y,a,ha,complexWord_seminorm_bound a⟩

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
