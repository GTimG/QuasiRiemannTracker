/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/SourceExistence.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.SphericalExteriorInsertion
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Whittaker.Nonvanishing.NormalizedFourierCoefficient
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.RepeatedCorePeriod

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem current_period_source_nonempty
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) : Nonempty (NonDegenerate.PeriodSource R N) := by
  obtain ⟨P,C,hP,hC⟩ := EisensteinReferenceSections.FrozenFibers.exists_model_fibers R.A R.classKilled
  obtain ⟨u,hu⟩ := exists_initial_plus_fourier_ne_zero_normalized R P C N hC
  let x := RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C)
    (bad R.A P C) ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u)
  obtain ⟨D,hD,hflat⟩ := exists_repeated_core_period_source R P C  hR N x
    (coreFlatInsertion_initial_exterior_spherical R P C hC (PiTensorProduct.tprod ℂ u)) hu
  exact ⟨D⟩
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
