import Candidate.Cycle63.Moment.SecondNaturalMask
import Candidate.Cycle63.Moment.HighSourceEnergy

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondSixthReduction
open CenteredMomentSecondSixthSource CenteredMomentSecondExceptionalFamily
open CenteredMomentCanonicalFirst CenteredMomentChildRows IdealMobiusDivisorSum
open CenteredMomentHeckeColumnWindow CenteredMomentSecondChildProfile

theorem actual_reduced_family_supported_ideal (η : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter → Character) (hf : Family η C D hC hD U τ)
    (χ : RayCharacter) (I : Ideal O) (hI : Supported I) :
    idealCoeff (τ χ) I = idealCoeff (childCharacter η χ) I *
      idealRowHom (reducedNumerator C D U) I := by
  have h := CenteredMomentSecondFamilyTransport.row_presentation_height
    η (τ χ) χ (reducedNumerator C D U) (hf.element_eq χ) I hI 0
  simp only [heightCoeff, Complex.ofReal_zero, mul_zero, Complex.cpow_zero,
    mul_one] at h
  rw [child_ideal_primary η χ I hI, h]
  ring

/-- The physical puncture restores the sixth factors cancelled in the second
character presentation; no conductor comparison for that presentation is used. -/
theorem actual_retained_reduced_mask (η : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter → Character) (hf : Family η C D hC hD U τ)
    (χ : RayCharacter) (z : O) (F : NaturalRow (τ χ) z)
    (G : NaturalRow (childCharacter η χ)
      ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z))
    (P : Ideal O) (hP : P ≠ 0) (hcop : ∀ J : Ideal O, IsCoprime J P → IsCoprime J C) (I : Ideal O) :
    idealCoeff (excluded F.character P) I =
      idealCoeff (excluded G.character P) I := by
  rw [excluded_ideal _ _ hP, excluded_ideal _ _ hP]
  by_cases hc : IsCoprime I P
  · rw [ite_eq_left hc, ite_eq_left hc]
    by_cases hs : Supported I
    · rw [natural_row_supported_ideal _ _ F I hs,
        natural_row_supported_ideal _ _ G I hs,
        actual_reduced_family_supported_ideal η C D hC hD U τ hf χ I hs,
        idealRowHom_argument_mul,
        residual_sixth_coefficient C D hC hCD U I hs
          (hcop I hc).symm]
      ring
    · rw [natural_row_ideal_zero_of_not_supported _ _ F I hs,
        natural_row_ideal_zero_of_not_supported _ _ G I hs]
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem actual_retained_fixed_dictionary_mask (η χ₁ : Character) (w : O)
    (first : NaturalRow η w)
    (hfirst : ∀ I : Ideal O, idealCoeff χ₁ I =
      if IsCoprime I χ₁.modulus then idealCoeff first.character I else 0)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter → Character) (hf : Family χ₁ C D hC hD U τ)
    (ξ : RayCharacter) (z : O) (F : NaturalRow (τ ξ) z)
    (second : NaturalRow (childCharacter χ₁ ξ)
      ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z))
    (fixed : NaturalRow (childCharacter η ξ)
      (w * ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z)))
    (P : Ideal O) (hP : P ≠ 0) (hcop : ∀ J : Ideal O, IsCoprime J P → IsCoprime J C) (I : Ideal O) :
    idealCoeff (excluded F.character P) I =
      idealCoeff (excluded fixed.character (χ₁.modulus * P)) I := by
  rw [actual_retained_reduced_mask χ₁ C D hC hD hCD U τ hf ξ z F second P hP hcop I]
  exact actual_second_punctured_natural_mask η χ₁ w _ first hfirst ξ second fixed P hP I

section WholeFamily
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

end WholeFamily
end
end OAI.SevenEighths.Cycle63Moment
