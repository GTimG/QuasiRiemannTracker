/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Induction/LocalModels/VectorAndFiberEquivalences.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RestrictedTensors.ExceptionalSetEquivalence
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.ParameterEvaluation
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Induction.ScalarSections.FlatInsertion

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open NumberField MomentSources KPGlobalTorusFiniteStages
open PrincipalOfKP.ResidueCoreBridge.CanonicalBinding
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def plusEquiv (v : KPHilbert.Place F) :
    FaithfulSource.RepairedInducing.Plus R N P C v ≃ₗ[ℂ] LiteralSource.Plus R.A P C v := by
  cases v <;> exact LinearEquiv.refl ℂ _

theorem reference_eq (v : KPHilbert.Place F) :
    plusEquiv R N P C v (FaithfulSource.RepairedInducing.plusReference R N P C v) =
      LiteralSource.plusReference R.A P C v := by
  cases v with
  | inl w => rfl
  | inr q =>
    rfl

theorem localValue_eq (v : KPHilbert.Place F)
    (g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 v)
    (x : FaithfulSource.RepairedInducing.Plus R N P C v) :
    FaithfulSource.RepairedInducing.localValue R N P C v g x =
      LiteralSource.localValue R.A P C v g (plusEquiv R N P C v x) := by
  cases v <;> rfl

def coreEquiv : FaithfulSource.RepairedInducing.PlusCore R N P C ≃ₗ[ℂ]
    RestrictedTensorSimple.Core (LiteralSource.Plus R.A P C)
      (LiteralSource.plusReference R.A P C) (LiteralSource.bad R.A P C) := by
  change RestrictedTensorSimple.Core (LiteralSource.Plus R.A P C)
    (LiteralSource.plusReference R.A P C) (FaithfulSource.RepairedInducing.bad R P C) ≃ₗ[ℂ] _
  exact RestrictedTensorSimple.equalBadEquiv _ _ _ _
    (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.badSet_eq_fullBad
      F R.A.zeta12 R.A.primitive_zeta12 P C)

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
