/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Digits/Exterior/TameRationalPhases.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.LocalFields.RationalOrdersAndReduction

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open MomentSources NumberField IsDedekindDomain ThetaExpansion ValuativeRel
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem localUnit_factorization (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) :
    x = R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) ^ ThetaBranch.order p.val x *
      ThetaBranch.localUnit R.A R.probe.allowed p x := by
  unfold ThetaBranch.localUnit
  simp

theorem effective_rational (hR : RootAligned R) (p : ThetaBranch.ExteriorPrime R.A) (x y : Fˣ) :
    KPSourceConvention.sourceC F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)
      (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom y) =
      ThetaBranch.symbol R.A R.σ p (ThetaBranch.localUnit R.A R.probe.allowed p x) ^ (2 * ThetaBranch.order p.val y) *
      ThetaBranch.symbol R.A R.σ p (ThetaBranch.localUnit R.A R.probe.allowed p y) ^ (-2 * ThetaBranch.order p.val x) := by
  let ux := ThetaBranch.localUnit R.A R.probe.allowed p x
  let uy := ThetaBranch.localUnit R.A R.probe.allowed p y
  have hx := ThetaBranch.localUnit_order R.A R.probe.allowed p x
  have hy := ThetaBranch.localUnit_order R.A R.probe.allowed p y
  obtain ⟨u, hu⟩ := rational_unit R p ux hx
  obtain ⟨v, hv⟩ := rational_unit R p uy hy
  have hh := KPSourceConvention.sourceC_valuation_units F R.A.zeta12 R.A.primitive_zeta12
    p.val (ExteriorWhittakerValues.exterior_good_six p) (exteriorCompletionGenerator R p)
    (ExteriorWhittakerValues.UnitCovarianceCompletion.exterior_completion_generator_ordinary_valuation R p) u v
    (ThetaBranch.order p.val x) (ThetaBranch.order p.val y)
  rw [rational_character R hR p ux hx u hu, rational_character R hR p uy hy v hv] at hh
  rw [hu, hv] at hh
  have he (z : Fˣ) : Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom z =
      exteriorCompletionGenerator R p ^ ThetaBranch.order p.val z *
        Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom
          (ThetaBranch.localUnit R.A R.probe.allowed p z) := by
    conv_lhs => rw [localUnit_factorization R p z]
    rw [map_mul, map_zpow]
  rw [← he x, ← he y] at hh
  exact hh

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
