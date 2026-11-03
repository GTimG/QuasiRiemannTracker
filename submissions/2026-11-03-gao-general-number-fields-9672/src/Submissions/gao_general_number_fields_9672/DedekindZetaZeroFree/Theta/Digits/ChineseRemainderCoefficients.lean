/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Digits/ChineseRemainderCoefficients.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.NormalizedResidualFunctionals
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.SphericalCRTProduct

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem exterior_spherical_factors_crt (R : PrincipalMellin.ActualRecipe S η)
    (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior)
    (P : Finset (ThetaBranch.ExteriorPrime R.A))
    (hc : c.val.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal c.val.val)
    (hn : n.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal n.val) :
    let b := ∏ p ∈ P, R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) ^
      (idealPrimeExponent p.val.asIdeal c.val.val + 3 * idealPrimeExponent p.val.asIdeal n.val)
    (∏ p ∈ P, ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p b) =
      R.probe.coefficients.gammaTwo c /
        ((Real.sqrt (R.A.exteriorNorm c.val) : ℂ) * (R.A.exteriorNorm n : ℂ)) := by
  exact ExteriorWhittakerValues.NumericalSpherical.sphericalProduct R c n P hc hn

end DedekindZetaZeroFree.ThetaExpansion

end
