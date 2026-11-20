/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Digits/SignedExteriorCoefficients.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Digits.Exterior.ProductAverageCoefficients

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem exterior_digit_coefficient {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (m : ThetaReflectionData.Row R.A)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed m) (x : Fˣ) :
    (∀ d, Function.HasFiniteMulSupport (exteriorDigitFactor R C m x d)) ∧
    exteriorDigitCoefficient R C m x =
      ThetaBranch.exteriorCoefficient R.A R.probe.allowed R.σ (Characters.psi R) m D x := by
  exact ⟨fun d => DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits.finite_support R C m x d,
    DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits.coefficient_exact R C m D x⟩

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
