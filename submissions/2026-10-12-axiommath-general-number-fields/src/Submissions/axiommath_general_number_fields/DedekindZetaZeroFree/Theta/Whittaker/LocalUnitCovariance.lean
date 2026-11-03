/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/LocalUnitCovariance.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.LocalFields.SexticUnitPhasesAndValuations
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Whittaker.UnitDiagonalCovariance

@[expose] public section

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField ValuativeRel
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem exterior_whittaker_value_unit_covariance (R : PrincipalMellin.ActualRecipe S η)
    (hR : RootAligned R) {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N)
    (p : ThetaBranch.ExteriorPrime R.A) (e : ℤ)
    (u : (p.val.adicCompletion F)ˣ) (t : 𝓞 F)
    (ht : ‖(u : p.val.adicCompletion F) - algebraMap (𝓞 F) (p.val.adicCompletion F) t‖ < 1)
    (hu : valuation (p.val.adicCompletion F) (u : p.val.adicCompletion F) = 1) :
    exteriorWhittakerValue R C p (exteriorCompletionGenerator R p ^ e * u) =
      exteriorWhittakerValue R C p (exteriorCompletionGenerator R p ^ e) *
        ThetaBranch.residueCharacter R.A R.σ p (Ideal.Quotient.mk p.val.asIdeal t) ^ (2 * e) := by
  obtain ⟨ui, rfl⟩ := ExteriorWhittakerValues.UnitCovarianceCompletion.exists_integerUnit_of_valuation_one p u hu
  have h := ExteriorWhittakerValues.exterior_unit_covariance C.factorization p (exteriorCompletionGenerator R p)
    (ExteriorWhittakerValues.UnitCovarianceCompletion.exterior_completion_generator_ordinary_valuation R p) e ui
  have hp := ExteriorWhittakerValues.UnitCovarianceCompletion.unit_phase_of_norm_sub_lt_one R hR p ui t ht
  simp only [hp] at h
  simpa only [exteriorWhittakerValue, exterior_diagonal_eq_standard_lift, exteriorImageAction, mul_comm] using h

end DedekindZetaZeroFree.ThetaExpansion

end
