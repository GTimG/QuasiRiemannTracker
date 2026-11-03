/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Profiles/ResidualSourceRealization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.ExteriorCoefficients

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources NumberField ValuativeRel ThetaExpansion
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
def currentStage08 (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N) : JointExteriorCoefficientSources R N := by
  have hW := exterior_whittaker_equivariance R C
  refine { C with exterior := {
    rational_exact := exterior_rational_value_eq_spherical_factor R hR C hW
    crt_product := ?_
    local_exact := ?_ } }
  · intro c n P hc hn
    dsimp only
    calc
      (∏ p ∈ P, C.factorization.exteriorValue R p
        (∏ q ∈ P, R.probe.allowed.generator (ThetaBranch.primeIdeal R.A q) ^
          (idealPrimeExponent q.val.asIdeal c.val.val + 3 * idealPrimeExponent q.val.asIdeal n.val))) =
        (∏ p ∈ P, ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p
          (∏ q ∈ P, R.probe.allowed.generator (ThetaBranch.primeIdeal R.A q) ^
            (idealPrimeExponent q.val.asIdeal c.val.val + 3 * idealPrimeExponent q.val.asIdeal n.val))) :=
        Finset.prod_congr rfl (fun p _ => exterior_rational_value_eq_spherical_factor R hR C hW p _)
      _ = _ := exterior_spherical_factors_crt R c n P hc hn
  · intro p e u t ht hu
    exact exterior_whittaker_value_generator_pow_mul_unit R hR C hW p e u t ht hu

end DedekindZetaZeroFree.RootDerivatives

end
