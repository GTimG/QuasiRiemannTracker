/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Moments/Reflected/FrequencyTerm.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Digits.SignedExteriorCoefficients

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def actualReflectedTerm {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (Z : ℝ)
    (ξ : ThetaReflectionData.Frequency R.A) : ℂ :=
  exteriorDigitCoefficient R C m (Quotient.out ξ) *
    (Characters.L R v (Quotient.out ξ))⁻¹ *
      C.realization.H C.packet v (ThetaReflectionData.frequencyClass R.A ξ)
        (Z * ThetaReflectionData.frequencyNorm R.A ξ)

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
