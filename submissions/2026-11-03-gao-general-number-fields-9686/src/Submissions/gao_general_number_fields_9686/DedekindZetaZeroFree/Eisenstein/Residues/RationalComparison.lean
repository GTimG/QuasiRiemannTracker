/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/RationalComparison.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalTensorEvaluation
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Intertwining.Residues.RationalVectorCofactor

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct BigOperators
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages
open KPGlobalResidualConstruction
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem comparison_pure_rational
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : s.val, Fiber R.A P C j.val)
    (t : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12) :
    (comparison R.A P C (RestrictedTensorSimple.stageInclusion
      (Fiber R.A P C) (reference R.A P C) (bad R.A P C) s
      (PiTensorProduct.tprod ℂ x))).val.val t =
    (∏ a : s.val.toLeft, x ⟨.inl a.val, Finset.mem_toLeft.mp a.property⟩) *
      ActualCofactor.rationalStageEval F R.A.zeta12 R.A.primitive_zeta12 P C
        (ScalarAbsorption.rightLevel C.exceptional s).val
        (ScalarAbsorption.rightLevel C.exceptional s).property t
        (fun q => x ⟨.inr q.val, Finset.mem_toRight.mp q.property⟩) := by
  unfold comparison
  simp only [LinearMap.comp_apply]
  rw [ScalarAbsorption.absorb_stage, ScalarAbsorption.stageEquiv_pure]
  simp only [map_smul]
  rw [finiteTensorMap_stage]
  rfl

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
