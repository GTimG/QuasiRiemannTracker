/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/Nonvanishing/PlusSectionFourierCoefficient.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Whittaker.Nonvanishing.CoreFourierCoefficient

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
variable (N : MomentSources.TraceHaarTransport R)
set_option backward.isDefEq.respectTransparency false

include μ hμ N in
theorem exists_initial_plus_fourier_ne_zero (hC : C.exceptional = R.A.Sf) :
    ∃ x : ∀ j : bad R.A P C, Plus R.A P C j.val,
      MomentSources.fourier R (KPWildKernelUpperBound.quotientHaar F)
        (coreResidue R P C (RestrictedTensorSimple.stageInclusion
          (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
          ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ x))) 1 ≠ 0 := by
  obtain ⟨y,hy⟩ := exists_initial_actualCoreFourier_ne_zero R P C μ hμ N hC
  choose x hx using fun j : bad R.A P C =>
    TensorActionSource.sourceQuotient_surjective R (actualImageData R P C μ hμ) j.val (y j)
  refine ⟨x, ?_⟩
  have he : TensorActionSource.sourceStageQuotient R (actualImageData R P C μ hμ)
      (bad R.A P C) (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ y := by
    rw [TensorActionSource.sourceStageQuotient, PiTensorProduct.map_tprod]
    exact congrArg (PiTensorProduct.tprod ℂ) (funext hx)
  change MomentSources.fourier R (KPWildKernelUpperBound.quotientHaar F)
    (actualCoreResidue R P C μ hμ N _) 1 ≠ 0 at hy
  rw [← he, actualCoreResidue_source_stage] at hy
  exact hy
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
