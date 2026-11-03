/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/ArchimedeanWeylCovariance.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Intertwining.ArchimedeanRootTransport
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Intertwining.StandardIntegral.AbsoluteIntegrability

@[expose] public section

noncomputable section
open scoped NumberField Classical
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

theorem actual_forward_arch_covariance
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (s : ℂ) (v : S) (u : NumberField.InfinitePlace F → ℝ)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    (∫ x : Adeles F, KPContActualSphericalFlatStage.L F ζ hζ U ι s v
      (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x *
        ((KPContFlatArchDiagonalMultiplier.aInfinity F ζ hζ u).val * g))
      ∂KPAdditiveHaar.adelicMeasure F) =
    Complex.exp (((2 : ℂ) / 3 - 2 * s) * ((∑ w, u w : ℝ) : ℂ)) *
      (∫ x : Adeles F, KPContActualSphericalFlatStage.L F ζ hζ U ι s v
        (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x * g)
        ∂KPAdditiveHaar.adelicMeasure F) := by
  simp_rw [forward_integrand_arch_transport F ζ hζ U ι s v u]
  rw [integral_const_mul, integral_arch_mul F ζ hζ u _
    (standard_measurable F ζ hζ U ι s v g)]
  rw [← mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
