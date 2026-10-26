import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.PrimaryMaskTransport
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.ActualRowDensity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentChildRows CenteredMomentNaturalRowSource RayFourExpansion
local notation "O" => HeckeFamily.O

theorem actual_second_natural_mask (η χ : Character) (w A : O)
    (F : NaturalRow η w)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff F.character I else 0)
    (ξ : RayCharacter) (child : NaturalRow (childCharacter χ ξ) A)
    (final : NaturalRow (childCharacter η ξ) (w*A)) (I : Ideal O) :
    idealCoeff child.character I = idealCoeff (excluded final.character χ.modulus) I := by
  by_cases hs : Supported I
  · rw [natural_row_supported_ideal _ _ child I hs,
      childCharacter, idealCoeff_product, hmask I,
      natural_row_supported_ideal _ _ F I hs,
      excluded_ideal _ _ χ.modulus_ne_bot,
      natural_row_supported_ideal _ _ final I hs,
      childCharacter, idealCoeff_product, idealRowHom_argument_mul]
    by_cases hc : IsCoprime I χ.modulus <;> simp only [hc, ite_true, ite_false] <;> ring
  · rw [natural_row_ideal_zero_of_not_supported _ _ child I hs,
      excluded_ideal _ _ χ.modulus_ne_bot,
      natural_row_ideal_zero_of_not_supported _ _ final I hs]
    split_ifs <;> rfl

theorem actual_second_punctured_natural_mask (η χ : Character) (w A : O)
    (F : NaturalRow η w)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff F.character I else 0)
    (ξ : RayCharacter) (child : NaturalRow (childCharacter χ ξ) A)
    (final : NaturalRow (childCharacter η ξ) (w*A))
    (R : Ideal O) (hR : R ≠ 0) (I : Ideal O) :
    idealCoeff (excluded child.character R) I =
      idealCoeff (excluded final.character (χ.modulus*R)) I := by
  rw [excluded_ideal _ _ hR, actual_second_natural_mask η χ w A F hmask ξ child final I,
    excluded_ideal _ _ χ.modulus_ne_bot,
    excluded_ideal _ _ (mul_ne_zero χ.modulus_ne_bot hR), IsCoprime.mul_right_iff]
  by_cases hc : IsCoprime I χ.modulus <;> by_cases hr : IsCoprime I R <;>
    simp only [hc, hr, and_self, true_and, false_and, ite_true, ite_false]

theorem actual_fixed_product_natural_mask (η χ ν : Character) (w : O)
    (F : NaturalRow η w) (G : NaturalRow (η.product ν) w)
    (R : Ideal O) (hR : R ≠ 0)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I = idealCoeff (excluded F.character R) I)
    (I : Ideal O) :
    idealCoeff (χ.product ν) I = idealCoeff (excluded G.character R) I := by
  rw [idealCoeff_product, hcoeff I, excluded_ideal _ _ hR,
    excluded_ideal _ _ hR, F.ideal I, G.ideal I, idealCoeff_product]
  split_ifs <;> ring

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
