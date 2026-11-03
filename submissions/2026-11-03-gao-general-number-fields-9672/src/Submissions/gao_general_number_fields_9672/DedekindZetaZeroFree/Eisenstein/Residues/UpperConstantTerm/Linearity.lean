/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/UpperConstantTerm/Linearity.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.UpperConstantTerm.ForwardKernel

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPLiteralRaw ThetaExpansion TensorActionSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C)
  (plusReference R.A P C) (bad R.A P C)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem coreResidue_upper_integrable (x : V)
    (μ : Measure (KPAdditiveQuotient F)) (hμ : μ.IsAddHaarMeasure) (g : G F ζ hζ) :
    Integrable (fun u : KPAdditiveQuotient F => coreResidue R P C x
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out u) * g)) μ := by
  obtain ⟨r, B, hr, _, _, hB⟩ := core_compact_period_clearing R P C x μ hμ g
  have hres : coreResidue R P C x =
      (ownedLiteralResidueFamily (full_product_compact_iwasawa R)).cleared
        (asLiteralFlat (coreFlatInsertion R P C x)) 0 := by
    change (ownedLiteralResidueFamily (full_product_compact_iwasawa R)).residue
      (literalZeroProfileEquiv (full_product_compact_iwasawa R) (coreFlatInsertion R P C x)) = _
    exact LiteralResidueFamily.residue_flat _ _
  rw [hres]
  exact (hB 0 (Metric.mem_ball_self hr)).1

def coreResidueUpperLinear : V →ₗ[ℂ] Functions F ζ hζ where
  toFun x g := ∫ u : KPAdditiveQuotient F, coreResidue R P C x
    (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out u) * g)
    ∂KPWildKernelUpperBound.quotientHaar F
  map_add' x y := by
    funext g
    simp only [map_add, Pi.add_apply]
    exact integral_add
      (coreResidue_upper_integrable R P C x _ inferInstance g)
      (coreResidue_upper_integrable R P C y _ inferInstance g)
  map_smul' a x := by
    funext g
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, integral_const_mul,
      RingHom.id_apply]

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
