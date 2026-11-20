/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/Nonvanishing/NormalizedFourierCoefficient.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Whittaker.Nonvanishing.PlusSectionFourierCoefficient

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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem exists_initial_plus_fourier_ne_zero_normalized (N : MomentSources.TraceHaarTransport R)
    (hC : C.exceptional = R.A.Sf) :
    ∃ x : ∀ j : bad R.A P C, Plus R.A P C j.val,
      MomentSources.fourier R (KPWildKernelUpperBound.quotientHaar F)
        (coreResidue R P C (RestrictedTensorSimple.stageInclusion
          (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
          ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ x))) 1 ≠ 0 := by
  let μ := fun q : KPFinitePlace F => Measure.addHaarMeasure (TensorSeedSource.integerCompacts q)
  letI : ∀ q, (μ q).IsAddHaarMeasure := fun q => inferInstance
  exact exists_initial_plus_fourier_ne_zero R P C μ
    (fun _ => Measure.addHaarMeasure_self) N hC
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
