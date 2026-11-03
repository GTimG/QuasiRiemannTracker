/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/Boundary/RadialHomogeneity.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residues.UpperMeanHeightDerivative

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPContFlatArchDiagonalMultiplier KPMsActualAngularSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "G" => KPGlobalTorusFunctionData.G F ζ hζ
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
local notation "Source" => KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)

def boundaryProduct (f : Source) (x : V) (g : G) : ℂ :=
  (KPContFlatSourceRecipe.flatR F ζ hζ 0 f).val g *
    star (∫q : KPAdditiveQuotient F,
      coreResidue R P C x (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g)
      ∂KPWildKernelUpperBound.quotientHaar F)

theorem boundaryProduct_arch_covariance (f : Source) (x : V)
    (u : InfinitePlace F → ℝ) (g : G) :
    boundaryProduct R P C f x ((aInfinity F ζ hζ u).val * g) =
      Complex.exp ((2:ℂ) * ((∑w, u w : ℝ) : ℂ)) * boundaryProduct R P C f x g := by
  unfold boundaryProduct
  rw [flatR_covariance, coreResidue_upper_arch_covariance, star_mul]
  have he : star (Complex.exp (((2:ℂ)/3) * ((∑w,u w:ℝ):ℂ))) =
      Complex.exp (((2:ℂ)/3) * ((∑w,u w:ℝ):ℂ)) := by
    rw [show (((2:ℂ)/3) * ((∑w,u w:ℝ):ℂ)) = (((2:ℝ)/3 * ∑w,u w:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_exp]
    change (starRingEnd ℂ) (Complex.ofReal _) = _
    exact RCLike.conj_ofReal _
  rw [he]
  simp only [mul_zero, add_zero]
  have hx : Complex.exp (((4:ℂ)/3) * ((∑w,u w:ℝ):ℂ)) *
      Complex.exp (((2:ℂ)/3) * ((∑w,u w:ℝ):ℂ)) =
      Complex.exp ((2:ℂ) * ((∑w,u w:ℝ):ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = (Complex.exp (((4:ℂ)/3) * ((∑w,u w:ℝ):ℂ)) *
        Complex.exp (((2:ℂ)/3) * ((∑w,u w:ℝ):ℂ))) *
        ((KPContFlatSourceRecipe.flatR F ζ hζ 0 f).val g *
          star (∫q : KPAdditiveQuotient F,
            coreResidue R P C x (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g)
            ∂KPWildKernelUpperBound.quotientHaar F)) := by ring
    _ = _ := by rw [hx]

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
