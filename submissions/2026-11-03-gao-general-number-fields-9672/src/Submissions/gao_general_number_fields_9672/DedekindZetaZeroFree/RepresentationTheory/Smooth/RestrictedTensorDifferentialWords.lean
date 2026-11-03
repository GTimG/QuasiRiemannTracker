/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Smooth/RestrictedTensorDifferentialWords.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.LieDerivatives

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages HCGeneration
open KPContActualSphericalRightFieldIdentification
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def stageBasisWord (s : RestrictedTensorSimple.Level (bad R.A P C)) :
    List (Fin (groupDimension F)) →
      Module.End ℂ (RestrictedTensorSimple.Stage (Plus R.A P C) s.val)
  | [] => LinearMap.id
  | i :: w => (stageLieSlot R P C s (actualLieIndexEquiv (F := F) i).1
      (s.property (by simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad]))
      (actualLieIndexEquiv (F := F) i).2).comp (stageBasisWord s w)

theorem quotientCoreEvaluator_stage_actualRightWord
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : List (Fin (groupDimension F)))
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    actualRightWord F ζ hζ w
      (quotientCoreEvaluator R.A P C (RestrictedTensorSimple.stageInclusion _ _ _ s x)) =
    quotientCoreEvaluator R.A P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (stageBasisWord R P C s w x)) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [actualRightWord, ih]
    exact quotientCoreEvaluator_stage_actualRight R P C s i _

def evaluatedStageBasisWord (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : List (Fin (groupDimension F))) :
    RestrictedTensorSimple.Stage (Plus R.A P C) s.val →ₗ[ℂ] MomentSources.Functions R :=
  (quotientCoreEvaluator R.A P C).comp
    ((RestrictedTensorSimple.stageInclusion _ _ _ s).comp (stageBasisWord R P C s w))

@[simp] theorem evaluatedStageBasisWord_apply
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : List (Fin (groupDimension F)))
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    evaluatedStageBasisWord R P C s w x = actualRightWord F ζ hζ w
      (quotientCoreEvaluator R.A P C (RestrictedTensorSimple.stageInclusion _ _ _ s x)) :=
  (quotientCoreEvaluator_stage_actualRightWord R P C s w x).symm

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
