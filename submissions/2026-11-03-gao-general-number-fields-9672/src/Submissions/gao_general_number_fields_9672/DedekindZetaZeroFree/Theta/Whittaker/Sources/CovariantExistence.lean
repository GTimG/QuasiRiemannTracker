/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/Sources/CovariantExistence.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.Sources.CovariantConstruction
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.SphericalExteriorInsertion
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.Nonvanishing.NormalizedFourierCoefficient

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

theorem current_covariant_nonempty
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) : Nonempty (NonDegenerate.ComplexCovariant R N) := by
  obtain ⟨P,C,hP,hC⟩ := EisensteinReferenceSections.FrozenFibers.exists_model_fibers R.A R.classKilled
  obtain ⟨u,hu⟩ := exists_initial_plus_fourier_ne_zero_normalized R P C N hC
  let μ := fun q : KPFinitePlace F => Measure.addHaarMeasure (TensorSeedSource.integerCompacts q)
  letI : ∀ q, (μ q).IsAddHaarMeasure := fun q => inferInstance
  exact exists_covariant_from_initial_plus R P C μ
    (fun _ => Measure.addHaarMeasure_self)  hR N hC u
    (coreFlatInsertion_initial_exterior_spherical R P C hC (PiTensorProduct.tprod ℂ u)) hu

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
